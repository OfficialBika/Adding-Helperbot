# Broadcast operations

## Safety and target scope

Broadcasting is restricted to bot owners and private-chat commands. Every broadcast requires an explicit confirmation button; confirmations expire after 15 minutes. Destinations are active private chats that have interacted with the bot and groups/supergroups where Telegram reports the bot as a member. Owner private chats are excluded. Channels are not broadcast targets.

Private recipients can opt out with \`/stopbroadcast\` and opt back in with \`/startbroadcast\`. The bot marks blocked/deactivated private chats inactive after delivery failures. If Telegram explicitly denies message-send rights in a group, the bot attempts \`leaveChat\` and removes that group from future broadcasts.

## Commands

- \`/broadcast Your announcement\` — preview and confirm a plain-text broadcast.
- Reply to a message with \`/broadcast\` — preview and confirm a copy of that message (media or text).
- \`/broadcast status\` — show the latest five broadcast jobs and current counts.
- \`/broadcast cancel\` — cancel the most recent pending/running job.
- \`/stopbroadcast\` — opt out of private broadcasts.
- \`/startbroadcast\` — opt back in.

## Delivery behavior

Broadcast jobs and per-chat delivery outcomes are stored in MongoDB. The worker processes jobs sequentially, uses four delivery workers with a shared conservative rate limiter, respects Telegram retry-after values, and makes bounded retries for transient network errors. Progress is persisted and shown on the confirmation message every 25 completed deliveries and at job completion. Queued/running jobs and deliveries left in a sending state are recovered when the bot starts again.

Telegram does not provide an idempotency key for sends. If the bot process stops after Telegram accepts a message but before the success result is persisted to MongoDB, that recipient can receive the same broadcast again after recovery. The system favors not silently losing an unrecorded pending delivery.

## Operational logs

Look for \`BROADCAST targets initialized\`, \`BROADCAST finished\`, \`AUTO LEAVE group=...\`, and \`AUTO LEAVE failed group=...\` in the bot service journal. Auto-leave is restricted to group/supergroup send-permission failures; unrelated parsing, lookup, and API errors are not treated as permission failures.
