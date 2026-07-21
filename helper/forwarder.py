class HelperForwarder:
    def __init__(self, target_chat):
        self.target_chat = target_chat

    async def forward(self, client, message):
        return await client.forward_messages(
            self.target_chat,
            message.chat.id,
            message.id
        )
