#!/usr/bin/env bash
set -Eeuo pipefail

SCRIPT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../deploy/local-bot-api" && pwd)/cleanup-temp.sh"
ROOT="$(mktemp -d)"
trap 'rm -rf -- "$ROOT"' EXIT

DATA="$ROOT/data"
mkdir -p "$DATA/temp" "$DATA/working"

printf 'old-temp' > "$DATA/temp/old.bin"
printf 'fresh-temp' > "$DATA/temp/fresh.bin"
printf 'old-working' > "$DATA/working/keep.bin"
touch -d '72 hours ago' "$DATA/temp/old.bin" "$DATA/working/keep.bin"
touch -d '2 hours ago' "$DATA/temp/fresh.bin"

BOT_API_DATA_DIR="$DATA" BOT_API_TEMP_RETENTION_HOURS=48 "$SCRIPT"

[[ ! -e "$DATA/temp/old.bin" ]]
[[ -e "$DATA/temp/fresh.bin" ]]
[[ -e "$DATA/working/keep.bin" ]]

printf 'dry-run-old' > "$DATA/temp/dry-run.bin"
touch -d '72 hours ago' "$DATA/temp/dry-run.bin"
BOT_API_DATA_DIR="$DATA" BOT_API_TEMP_RETENTION_HOURS=48 "$SCRIPT" --dry-run
[[ -e "$DATA/temp/dry-run.bin" ]]

rm -rf -- "$DATA/temp"
mkdir -p "$ROOT/outside"
ln -s "$ROOT/outside" "$DATA/temp"

set +e
BOT_API_DATA_DIR="$DATA" BOT_API_TEMP_RETENTION_HOURS=48 "$SCRIPT" >/dev/null 2>&1
RC=$?
set -e
[[ "$RC" -ne 0 ]]

printf 'Local Bot API temp cleanup tests passed\n'
