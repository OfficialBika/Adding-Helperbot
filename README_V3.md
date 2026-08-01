# Adding HelperBot V3

## Architecture

```
Telegram
  |
  v
Middleware
  |
  v
Handlers
  |
  v
Services
  |
  v
Repositories
  |
  v
MongoDB
```

## Components

- Aiogram Bot Core
- Pyrogram Service Layer
- MongoDB Repository Pattern
- Image Processing Pipeline
- Duplicate Detection
- Admin System
- Docker Deployment
- CI Testing

## Run

```bash
cp .env.example .env
pip install -r requirements.txt
python main.py
```
