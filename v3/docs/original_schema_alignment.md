# V3 Original Schema Alignment

This document records fields from the original Adding-Helperbot implementation that V3 must preserve.

## Source Definition

Each source keeps its own configuration:

- source key
- MongoDB collection
- command
- bot identity
- parser type
- source specific archive/log target

## Parsed Data

Original parser data includes:

- name
- anime_name
- rarity
- card_id
- command_name
- raw_text
- source_key

## Media Metadata

V3 keeps media lookup information:

- media_type
- file_id
- file_unique_id
- sha256
- phash
- frame_hashes
- media_geometry
- photo_fingerprint
- video_fingerprint
- fingerprint_version

## Fingerprint Compatibility

Preserve:

- MEDIA_SCHEMA_VERSION
- MEDIA_FINGERPRINT_VERSION
- PHOTO_HASH_VERSION
- VIDEO_HASH_VERSION

## Storage Rules

- Do not replace source collections.
- Keep source separated lookup data.
- Use file_unique_id for duplicate protection.
- Keep photo/video fingerprint data for accurate lookup.
- Store references and metadata required by NameBotV3 lookup.
