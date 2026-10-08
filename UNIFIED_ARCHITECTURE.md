# Bika Adding-only Architecture

This branch is the isolated Adding runtime.

## Responsibilities

- Collect characters from configured source bots/channels through AddHelper.
- Accept trusted source posts in one Adding Group.
- Parse character name and optional source character ID.
- Preserve Telegram file IDs and file_unique_ids.
- Deduplicate and update MongoDB records.
- Expose status, stats, ping, authorization, and Helper controls.

## Explicitly out of scope

- Media search handlers
- Automatic media matching
- Manual media matching commands
- Perceptual similarity
- Photo/video fingerprint generation
- Search caches
- Search-only SQLite indexes
- Search-only access gates
- Separate NameBot runtime

## Record flow

1. Helper asks a configured source bot/channel for data.
2. The helper response is forwarded or delivered to the Adding Group.
3. The Adding bot authenticates the source path.
4. The parser extracts name and optional source ID.
5. Telegram media identifiers and message metadata are collected.
6. MongoDB upserts the record using a source-aware identity key.
7. A compact save/update notice is sent in the Adding Group.

## Identity policy

Normal sources prefer source_key + character_id.

Hallow and Catcher Logs use source_key + file_unique_id because source IDs are not stable for those datasets.

Grabber FW uses source_key + source_variant + character_id when the Grabber bot identity is known. Unknown Grabber variants fall back to Telegram UID/origin identity.

Real media is rejected when Telegram file_unique_id is unavailable.

## Performance goal

The Adding hot path avoids unnecessary network and CPU work. It does not download media or build image/video fingerprints merely to save a record.
