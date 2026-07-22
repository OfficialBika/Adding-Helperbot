class HelperForwarder:
    def __init__(self, target_chat):
        self.target_chat = target_chat

    async def forward(self, client, message):
        if not message or not self.target_chat:
            return
        await message.forward(self.target_chat)
