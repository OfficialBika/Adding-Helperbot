from .client import database

items = database.collection('items')
sudo_users = database.collection('sudo_users')
known_users = database.collection('known_users')
user_modes = database.collection('user_modes')
settings = database.collection('settings')
