# Bika Adding & Helper — Adding-only Branch

This branch is intentionally dedicated to the Adding pipeline.

## Runtime

The branch runs one Telegram bot process:

python unified/main.py

The helper userbot collects source data and the bot accepts trusted forwarded/source-bot posts in the configured Adding Group.

## Data flow

Source bot / source channel
→ Helper
→ Adding Group
→ source resolver
→ name + optional source ID
→ MongoDB upsert

The runtime does not contain a media search service, similarity engine, fingerprint cache, or separate NameBot process.

## Adding rules

- Only the configured Adding Group can create records.
- Forwarded posts must match a configured or known source identity.
- Direct source-bot messages are accepted only for known source identities.
- Helper-generated source results are accepted through the trusted Helper userbot identity.
- Real Telegram media records must include Telegram file_unique_id.
- The Adding path stores Telegram media identifiers and message metadata; it does not download media for fingerprint generation.
- Hallow and Catcher Logs use Telegram UID/origin identity where source IDs are not stable.
- Grabber FW uses a stable source variant when the bot identity is known.

## Helper

Owner/admin HelperManager commands remain available, including inline and forward collectors with durable progress checkpoints.

## Database

MongoDB remains the authoritative Adding database. Existing records are preserved. Obsolete search indexes are removed during startup while adding-related dedupe indexes remain.

The existing DB name is intentionally preserved to avoid an unnecessary data migration.

## Deployment

Render starts:

python unified/main.py

Set BOT_TOKEN, MONGO_URI, OWNER_IDS, and ADDING_CHAT_ID. AddHelper also needs API_ID, API_HASH, and SESSION_STRING.

Do not commit real tokens, MongoDB credentials, or Pyrogram session strings.
