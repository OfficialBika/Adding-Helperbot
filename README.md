# 🚀 Adding HelperBot V3

<p align="center">
  <b>Next Generation Telegram Image Management Bot</b><br>
  Built with modern async architecture, scalable services and production-ready tooling.
</p>

---

## ✨ Features

- 🤖 Aiogram Telegram Bot Core
- 📱 Pyrogram Client Integration
- 🖼️ Advanced Image Processing Pipeline
- 🔍 Duplicate Image Detection
- 🗄️ MongoDB Repository Architecture
- 👤 User Management System
- 🛡️ Admin Control System
- 📊 Health Monitoring
- 🐳 Docker Deployment
- ⚙️ CI/CD Automation
- 🔐 Security Scanning

---

## 🏗️ V3 Architecture

```text
Telegram
   |
   v
Middleware Layer
   |
   v
Handlers
   |
   v
Service Layer
   |
   v
Repository Layer
   |
   v
MongoDB
```

---

## 📦 Tech Stack

| Component | Technology |
|---|---|
| Bot Framework | Aiogram 3 |
| MTProto Client | Pyrogram |
| Database | MongoDB + Motor |
| Image Engine | Pillow / OpenCV |
| Testing | Pytest |
| CI | GitHub Actions |
| Deployment | Docker |

---

## 🚀 Installation

```bash
git clone https://github.com/OfficialBika/Adding-Helperbot.git
cd Adding-Helperbot

cp .env.example .env

pip install -r requirements.txt

python main.py
```

---

## 🐳 Docker Deployment

```bash
docker compose up -d --build
```

---

## 🔧 Environment

Required variables:

```env
BOT_TOKEN=
DATABASE_URL=
API_ID=
API_HASH=
ADMIN_IDS=
```

---

## 🧪 Development

Run tests:

```bash
pytest
```

Code quality:

```bash
flake8 .
isort --check-only .
```

---

## 🔐 Security

V3 includes:

- Dependency vulnerability scanning
- CodeQL analysis
- Automated CI validation

---

## 📁 Project Structure

```text
app/
├── handlers/
├── services/
├── database/
├── middlewares/
├── config/
└── utils/

tests/
.github/
Dockerfile
docker-compose.yml
```

---

## 📌 Version

Current Branch: `Adding-HelperV3`

Status: Production Migration 🚀

---

Made with ❤️ by OfficialBika
