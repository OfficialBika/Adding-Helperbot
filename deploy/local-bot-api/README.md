# Local Telegram Bot API for Bika

This directory adds an optional VPS-side Local Telegram Bot API Server for
the existing Adding/Lookup bot. The main branch remains unchanged; this is a
separate testable branch.

## What is added

- Official Telegram Bot API server built from `tdlib/telegram-bot-api`.
- Private `127.0.0.1:8081` binding.
- Persistent storage under a configurable absolute path.
- Shared host/container path so Local Bot API `getFile` results can be read
  directly by a host-running Python bot.
- Safe direct-file lookup with automatic fallback to the existing
  `bot.download()` path.
- Hourly systemd cleanup for stale files under the Bot API `temp` directory,
  with a conservative 48-hour default retention.

## VPS test setup

Create storage:

```bash
sudo mkdir -p /srv/telegram-bot-api-test/data/temp
sudo chown -R 1000:1000 /srv/telegram-bot-api-test
```

Create the Local Bot API environment:

```bash
cd ~/Adding-Helperbot/deploy/local-bot-api
cp .env.example .env
nano .env
```

Set `TELEGRAM_API_ID` and `TELEGRAM_API_HASH`. These are separate from
the Telegram bot token.

Build and start:

```bash
sudo docker compose build
sudo docker compose up -d
sudo docker compose ps
sudo docker compose logs --tail=100 telegram-bot-api
```

The service listens only on localhost:

```text
127.0.0.1:8081
```

Test the server before changing the bot:

```bash
export BOT_TOKEN='YOUR_TEST_BOT_TOKEN'
curl -sS "http://127.0.0.1:8081/bot${BOT_TOKEN}/getMe"
```

After the local server returns `"ok":true`, the Telegram bot can be logged
out from the cloud Bot API and then pointed at the local endpoint.

For a host-running Python bot, add:

```env
BOT_API_BASE_URL=http://127.0.0.1:8081
BOT_API_IS_LOCAL=true
BOT_API_LOCAL_FILES_ROOT=/srv/telegram-bot-api-test/data
```

`BOT_API_LOCAL_FILES_ROOT` must exactly match `BOT_API_DATA_DIR`.

## Automatic temp cleanup

The cleanup job intentionally does **not** delete anything from the Bot API
working directory. It only removes regular files older than the configured
retention period from:

```text
<BOT_API_DATA_DIR>/temp
```

Default policy:

- runs hourly through a persistent systemd timer;
- keeps temporary files for at least 48 hours;
- never follows or deletes a symlinked `temp` directory;
- refuses unsafe paths and retention values;
- leaves Bot API account/work data untouched.

Install it on the VPS:

```bash
cd ~/Adding-Helperbot/deploy/local-bot-api

sudo install -m 0755 cleanup-temp.sh /usr/local/bin/bika-telegram-bot-api-temp-cleanup
sudo install -m 0644 systemd/bika-telegram-bot-api-temp-cleanup.service /etc/systemd/system/
sudo install -m 0644 systemd/bika-telegram-bot-api-temp-cleanup.timer /etc/systemd/system/
sudo install -m 0644 cleanup.env.example /etc/bika-telegram-bot-api-cleanup.env

sudoedit /etc/bika-telegram-bot-api-cleanup.env
```

Set `BOT_API_DATA_DIR` there to the exact same path used by
`BOT_API_DATA_DIR` in the Local Bot API compose environment. Leave
`BOT_API_TEMP_RETENTION_HOURS=48` unless you have a deliberate reason to
change it.

Enable and run it:

```bash
sudo systemctl daemon-reload
sudo systemctl enable --now bika-telegram-bot-api-temp-cleanup.timer

# Run one cleanup immediately to verify the setup:
sudo systemctl start bika-telegram-bot-api-temp-cleanup.service

sudo systemctl status bika-telegram-bot-api-temp-cleanup.timer --no-pager
sudo journalctl -u bika-telegram-bot-api-temp-cleanup.service -n 50 --no-pager
```

Dry-run before changing anything:

```bash
BOT_API_DATA_DIR=/srv/telegram-bot-api-test/data \
BOT_API_TEMP_RETENTION_HOURS=48 \
/usr/local/bin/bika-telegram-bot-api-temp-cleanup --dry-run
```

Do not use `rm -rf <BOT_API_DATA_DIR>/*` or delete arbitrary files from the
Bot API working directory.

## Verification

Run the existing regression suite from the repository root:

```bash
python -m unittest discover -s tests -p "test_*.py" -v
```

Validate the cleanup script itself:

```bash
bash -n deploy/local-bot-api/cleanup-temp.sh
bash tests/test_local_bot_api_cleanup.sh
```

Then start the existing bot normally and send a test photo. A successful
direct-file lookup will log `mode=local_file`. An unusable local path falls
back to the existing HTTP download path.

## Safety

The implementation does not change MongoDB schemas, source routing, result
formatting, or lookup decisions. Local Bot API is disabled unless configured
through environment variables.

The cleanup job is deliberately scoped to temporary files only. It does not
attempt to clean the Bot API working directory, bot authorization state, or
other persistent data.

Do not expose port 8081 publicly, and do not commit real tokens, MongoDB
credentials, Telegram API hashes, or session strings.
