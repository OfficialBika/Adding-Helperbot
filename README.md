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


## MongoDB ↔ SQLite consistency

- MongoDB is the source of truth for all lookup records.
- In SQLite mode, exact UID/SHA/origin lookups still query MongoDB directly.
- SQLite stores rebuildable photo/video similarity fingerprints and compact item snapshots.
- Adding creates an `updated_at` index on every source collection so NameBotV3 delta sync can use an indexed watermark query.
- NameBotV3 completes the initial SQLite build before marking the webhook service ready.
- A periodic full SQLite rebuild (default: every 6 hours) is enabled to recover missed index state and remove rows for documents deleted from MongoDB, because deletions do not carry an `updated_at` watermark.
- Render local storage is treated as ephemeral; a fresh instance can rebuild the secondary index from MongoDB.


## Broadcast performance tuning

The async broadcast worker is I/O-bound; its concurrency is configurable independently from Telegram API pacing. The default profile for a 12-vCPU / 24-GB VPS is:

```dotenv
BROADCAST_WORKERS=20
BROADCAST_RATE_PER_SECOND=25
BROADCAST_DELIVERY_BATCH_SIZE=800
BROADCAST_CHAT_INTERVAL_MS=1000
BROADCAST_PROGRESS_UPDATE_EVERY=100
MONGO_MIN_POOL_SIZE=4
MONGO_MAX_POOL_SIZE=32
```

- Worker concurrency is clamped to 1–24; the default is 20.
- Global sending is clamped to 1–27 messages/second; the default is 25 to retain headroom below Telegram's documented approximate free bulk limit of 30 messages/second.
- Per-chat pacing remains at least one second, and Telegram `RetryAfter` responses extend the global and affected-chat pause.
- The delivery queue is written in batches of 800 by default; progress edits occur every 100 completed deliveries to reduce unnecessary Telegram API calls.
- These values are starting defaults, not a guarantee of 25 successful sends/sec. Monitor 429s, API latency, MongoDB pool wait, and actual throughput. Do not increase the rate beyond Telegram's limits or enable paid broadcasts without explicit owner approval.
