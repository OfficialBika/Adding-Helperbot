# Adding-Helperbot V3 Architecture

## Purpose

Adding-Helperbot V3 is a lookup data preparation system.

It collects data from multiple source bots, parses responses, normalizes records, and stores structured lookup data for lookup bots.

## Pipeline

Source Bots

```
Source Bot -> Binding -> Watcher -> Crawler -> Parser -> Normalizer -> MongoDB Writer -> Lookup Bots
```

## Principles

- Keep existing crawler/parser workflow.
- Separate each source bot data domain.
- Store lookup metadata, not duplicate media storage.
- Keep Telegram file references for lookup response.
- Protect data with duplicate checks.

## V3 Layers

- parsers: extract source specific data
- normalizers: standardize lookup records
- repositories: MongoDB access layer
- collections: per bot/source separation
- validators: prevent invalid lookup records
