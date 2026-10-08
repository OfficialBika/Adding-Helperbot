#!/usr/bin/env bash
set -Eeuo pipefail

DATA_DIR="${BOT_API_DATA_DIR:-/srv/telegram-bot-api/data}"
RETENTION_HOURS="${BOT_API_TEMP_RETENTION_HOURS:-48}"
DRY_RUN=0

usage() {
  cat <<'EOF'
Usage: bika-telegram-bot-api-temp-cleanup [--dry-run]

Deletes only regular files under <BOT_API_DATA_DIR>/temp that are older than
BOT_API_TEMP_RETENTION_HOURS. The Bot API working directory itself is never
touched.
EOF
}

log() {
  printf '%s %s\n' "[bika-telegram-bot-api-temp-cleanup]" "$*"
}

die() {
  log "ERROR: $*" >&2
  exit 1
}

while (($#)); do
  case "$1" in
    --dry-run)
      DRY_RUN=1
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      usage >&2
      die "unknown argument: $1"
      ;;
  esac
  shift
done

[[ "$DATA_DIR" = /* ]] || die "BOT_API_DATA_DIR must be an absolute path"
DATA_DIR="${DATA_DIR%/}"
[[ -n "$DATA_DIR" && "$DATA_DIR" != "/" ]] || die "refusing unsafe BOT_API_DATA_DIR=$DATA_DIR"

[[ "$RETENTION_HOURS" =~ ^[0-9]+$ ]] || die "BOT_API_TEMP_RETENTION_HOURS must be an integer"
(( RETENTION_HOURS >= 24 )) || die "retention must be at least 24 hours"
(( RETENTION_HOURS <= 720 )) || die "retention must not exceed 720 hours (30 days)"

for command in find realpath flock du awk tr wc; do
  command -v "$command" >/dev/null 2>&1 || die "$command is required"
done

if [[ ! -d "$DATA_DIR" ]]; then
  log "SKIP: data directory does not exist: $DATA_DIR"
  exit 0
fi

DATA_REAL="$(realpath -e -- "$DATA_DIR")"
TEMP_DIR="$DATA_REAL/temp"

if [[ ! -e "$TEMP_DIR" ]]; then
  log "SKIP: temp directory does not exist: $TEMP_DIR"
  exit 0
fi

[[ -d "$TEMP_DIR" ]] || die "temp path is not a directory: $TEMP_DIR"
[[ ! -L "$TEMP_DIR" ]] || die "refusing symlinked temp directory: $TEMP_DIR"

TEMP_REAL="$(realpath -e -- "$TEMP_DIR")"
[[ "$TEMP_REAL" == "$DATA_REAL/temp" ]] || die "refusing temp path outside data directory: $TEMP_REAL"

LOCK_FILE="${TMPDIR:-/tmp}/bika-telegram-bot-api-temp-cleanup.lock"
exec 9>"$LOCK_FILE"
if ! flock -n 9; then
  log "SKIP: another cleanup run is already active"
  exit 0
fi

RETENTION_MINUTES=$((RETENTION_HOURS * 60))
BEFORE_BYTES="$(du -sb -- "$TEMP_REAL" | awk '{print $1}')"
STALE_COUNT="$(find "$TEMP_REAL" -xdev -type f -mmin "+$RETENTION_MINUTES" -print0 | tr -cd '\0' | wc -c | tr -d '[:space:]')"

if (( DRY_RUN )); then
  log "DRY-RUN: stale_files=$STALE_COUNT retention_hours=$RETENTION_HOURS temp=$TEMP_REAL size_bytes_before=$BEFORE_BYTES"
  exit 0
fi

if (( STALE_COUNT == 0 )); then
  log "OK: no stale temp files retention_hours=$RETENTION_HOURS temp=$TEMP_REAL size_bytes=$BEFORE_BYTES"
  exit 0
fi

if ! find "$TEMP_REAL" -xdev -ignore_readdir_race -type f -mmin "+$RETENTION_MINUTES" -delete; then
  die "cleanup encountered a deletion error under $TEMP_REAL"
fi

AFTER_BYTES="$(du -sb -- "$TEMP_REAL" | awk '{print $1}')"
log "OK: removed_stale_files=$STALE_COUNT retention_hours=$RETENTION_HOURS temp=$TEMP_REAL size_bytes_before=$BEFORE_BYTES size_bytes_after=$AFTER_BYTES"
