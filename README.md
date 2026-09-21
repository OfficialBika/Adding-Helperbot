# Bika Adding + NameBotV3 Unified Repository

This branch combines Adding-Helperbot and NameBotV3 while keeping them as two independent Render Web Services.

## Services

- bika-adding -> python app.py
- bika-namebotv3 -> python namebotv3/main.py

Both services use the same MongoDB database (waifu_adding_v2).

NameBotV3 uses the SQLite hybrid fingerprint engine. SQLite is a rebuildable secondary index/cache; MongoDB remains the source of truth.

## Data flow

Adding -> MongoDB -> NameBotV3 SQLite index -> lookup

The SQLite index is rebuilt from MongoDB after a fresh Render instance/redeploy.

## Render

Deploy this repository using render.yaml. Render creates two Web Services. Each service needs its own Telegram BOT_TOKEN, PUBLIC_URL, and WEBHOOK_SECRET. Use the same MONGO_URI and DB_NAME for both.

For Adding, also set the Pyrogram API_ID, API_HASH, and SESSION_STRING values required by the existing helper.

For NameBotV3, keep LOOKUP_ENGINE_MODE=sqlite.

Do not commit real tokens, MongoDB credentials, or session strings.
