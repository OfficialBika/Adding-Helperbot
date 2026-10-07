# Local Telegram Bot API for Bika

This directory builds the official Telegram Bot API server from the upstream
source repository and runs it in local mode. Telegram documents that local mode
removes the normal file-download size limit and, importantly for this bot,
getFile can return an absolute local file path so the bot can read the file
directly instead of downloading it a second time.

## 1. Recommended VPS layout

Use Ubuntu 24.04 LTS for the VPS initially. Docker currently supports Ubuntu
22.04, 24.04 and 26.04; the upstream Telegram Bot API build generator also
provides Ubuntu 24/26 instructions.

Recommended layout:

  /srv/telegram-bot-api/
    compose.yaml
    .env
    data/

Keep the Local Bot API HTTP endpoint private. The compose file publishes it only
on 127.0.0.1:8081.

## 2. Create Telegram API credentials

Open https://my.telegram.org, sign in with the Telegram account that owns the
application, open "API development tools", create an application, and copy the
api_id and api_hash.

These are NOT the bot token. The bot token is still used by the bot itself.

Create the runtime environment file:

  cd /path/to/Adding-Helperbot/deploy/local-bot-api
  cp .env.example .env
  nano .env

Replace TELEGRAM_API_ID and TELEGRAM_API_HASH.

## 3. Install Docker on Ubuntu

Use Docker's official apt repository. The current Docker documentation supports
Ubuntu 22.04, 24.04 and 26.04.

  sudo apt update
  sudo apt install -y ca-certificates curl
  sudo install -m 0755 -d /etc/apt/keyrings
  sudo curl -fsSL https://download.docker.com/linux/ubuntu/gpg -o /etc/apt/keyrings/docker.asc
  sudo chmod a+r /etc/apt/keyrings/docker.asc

  sudo tee /etc/apt/sources.list.d/docker.sources <<EOF
  Types: deb
  URIs: https://download.docker.com/linux/ubuntu
  Suites: $(. /etc/os-release && echo "${UBUNTU_CODENAME:-$VERSION_CODENAME}")
  Components: stable
  Architectures: $(dpkg --print-architecture)
  Signed-By: /etc/apt/keyrings/docker.asc
  EOF

  sudo apt update
  sudo apt install -y docker-ce docker-ce-cli containerd.io docker-buildx-plugin docker-compose-plugin

  sudo systemctl enable --now docker
  sudo docker run hello-world
  docker compose version

## 4. Prepare persistent storage

  sudo mkdir -p /srv/telegram-bot-api/data/temp
  sudo chown -R 1000:1000 /srv/telegram-bot-api

The UID/GID must match BOT_API_UID/BOT_API_GID in .env.

## 5. Build and start

  cd /path/to/Adding-Helperbot/deploy/local-bot-api
  docker compose build
  docker compose up -d

Check the service:

  docker compose ps
  docker compose logs --tail=100 telegram-bot-api

The healthcheck verifies that port 8081 is listening.

## 6. Test the Local Bot API BEFORE switching the bot

Set BOT_TOKEN only in your shell, never commit it:

  export BOT_TOKEN='YOUR_BOT_TOKEN'
  curl -s "http://127.0.0.1:8081/bot${BOT_TOKEN}/getMe"

A successful response should contain:

  {"ok":true,...}

Do NOT call logOut until this local API is running correctly.

## 7. Cut the bot over to the local server

Telegram requires the bot to be logged out from the cloud Bot API before moving
it to a local Bot API server; otherwise Telegram does not guarantee that the bot
will receive all updates.

At the cutover moment:

  curl -s "https://api.telegram.org/bot${BOT_TOKEN}/logOut"

Then point the bot to:

  BOT_API_BASE_URL=http://127.0.0.1:8081
  BOT_API_IS_LOCAL=true
  BOT_API_LOCAL_FILES_ROOT=/var/lib/telegram-bot-api

For a bot process running inside Docker on the same bika_net network, use:

  BOT_API_BASE_URL=http://telegram-bot-api:8081

and mount the same host data directory into the bot container at exactly:

  /var/lib/telegram-bot-api

The exact same path matters because getFile can return an absolute path.

## 8. Why Bika now has a direct-file fast path

The unified lookup code calls getFile() in local mode. When the returned
file_path is absolute and under BOT_API_LOCAL_FILES_ROOT, it reads that file
directly from disk. If anything is unavailable or the path does not pass the
safety check, it falls back to the normal aiogram download path.

That fallback is deliberate: Local Bot API deployment errors must not change
lookup correctness.

## 9. Do not expose port 8081 publicly

The compose file intentionally binds:

  127.0.0.1:8081:8081

Do not change that to 0.0.0.0:8081 unless there is a specific reason. The Local
Bot API is an internal service for this VPS.

If the bot itself runs in Docker, prefer the private Docker network and the
service DNS name instead of publishing the port at all.

## 10. Production verification checklist

Before considering the migration complete:

  1. Local getMe returns ok=true.
  2. Bot starts against the local base URL.
  3. Normal commands still work.
  4. A known Telegram photo resolves by file_unique_id.
  5. A cold photo lookup logs mode=local_file.
  6. A hash lookup computes the expected result.
  7. Mongo data and existing lookup behavior remain unchanged.
  8. Restarting the VPS automatically restarts the Local Bot API.
  9. The Local Bot API data directory persists across container recreation.
