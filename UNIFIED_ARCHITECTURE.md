# Unified Adding + Lookup V4

This branch now contains a single runtime for both jobs:

- **One Telegram bot process**
- **One MongoDB database**
- **One Adding group** configured by `ADDING_CHAT_ID`
- The Adding group is **ingest-only**
- Every other allowed private/group chat is **lookup-only**
- MongoDB collection: `characters`

## MongoDB policy

The new `characters` collection intentionally does **not** store:

- character ID
- rarity
- anime / series / movie

It stores only what is needed to identify and look up the media:

- character name
- output command / source key
- Telegram file unique IDs
- SHA-256 aliases
- photo fingerprints
- video fingerprints / samples
- media type / duration
- source origin and Adding-group archive reference
- timestamps

The fingerprint index uses MongoDB chunk fields so approximate photo lookup can avoid scanning the whole collection.

## Runtime flow

1. Helper userbot requests characters from configured source bots.
2. Responses are forwarded into the single Adding group.
3. The unified bot parses the name and fingerprints the media.
4. The record is upserted into MongoDB.
5. Media posted anywhere else is looked up against the same collection.
6. Exact UID/SHA/origin matches are attempted before similarity matching.

## Commands

Owner only:

- `/startdmcatchbot`
- `/startdmgrabbot`
- `/startdmsenpaibot`
- `/startdmhallowbot`
- `/startdmtakersbot`
- `/stopdm`
- `/addingstatus`
- `/stats`

## Deployment

Render now starts only:

`python unified/main.py`

Use the variables in `unified/env.example`.

Recommended fresh MongoDB database:

`bika_adding_lookup`
