# 🚀 Adding HelperBot V3

<p align="center">
  <b>Next Generation Telegram Image Management Bot</b><br>
  Built with modern async architecture, scalable services and production-ready tooling.
</p>

<p align="center">

![Python](https://img.shields.io/badge/Python-3.12-blue)
![Docker](https://img.shields.io/badge/Docker-Ready-blue)
![CI](https://github.com/OfficialBika/Adding-Helperbot/actions/workflows/test.yml/badge.svg)
![Security](https://github.com/OfficialBika/Adding-Helperbot/actions/workflows/security.yml/badge.svg)

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

```bash
pytest

flake8 .
isort --check-only .
```

---

## 🔐 Security

V3 includes:

- Dependency vulnerability scanning
- CodeQL analysis
- Automated CI validation
- Pre-commit quality checks

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

## 📌 Release

Current Branch: `Adding-HelperV3`

Version: `v3.0.0`

Status: Production Migration 🚀

---

Made with ❤️ by OfficialBika
