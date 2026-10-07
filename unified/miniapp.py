from __future__ import annotations

from datetime import datetime, timedelta, timezone
from html import escape

from aiohttp import web

from unified.store import characters, db


INDEX_HTML = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<meta name="theme-color" content="#080518">
<meta name="description" content="BIKA Game Arena">
<title>BIKA GAME — Arena</title>
<style>
:root{
  --bg:#060412;--panel:#0d0a22;--panel2:#120d2f;--line:#2c1d68;--line2:#4732a0;
  --text:#f7f5ff;--muted:#aaa4c8;--pink:#ff21d4;--violet:#8c34ff;--blue:#20b7ff;
  --cyan:#23e2ff;--green:#24e6a0;--gold:#ffd15c;--shadow:0 20px 70px rgba(0,0,0,.45);
}
*{box-sizing:border-box}
html,body{margin:0;min-height:100%;background:
radial-gradient(circle at 12% 10%,rgba(119,45,255,.18),transparent 26%),
radial-gradient(circle at 87% 6%,rgba(255,31,200,.13),transparent 24%),
radial-gradient(circle at 50% 70%,rgba(34,180,255,.06),transparent 30%),var(--bg);
color:var(--text);font-family:Inter,ui-sans-serif,system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif}
button,input{font:inherit}
a{color:inherit;text-decoration:none}
.app{display:grid;grid-template-columns:180px minmax(0,1fr);min-height:100vh}
.sidebar{position:sticky;top:0;height:100vh;border-right:1px solid rgba(111,76,214,.28);background:linear-gradient(180deg,rgba(11,7,27,.96),rgba(6,4,17,.98));padding:22px 15px;z-index:20}
.brand{padding:4px 10px 22px}
.brand b{display:block;font-size:38px;line-height:1;font-weight:900;letter-spacing:-2px;background:linear-gradient(90deg,#ff17d3,#a548ff,#20c9ff);-webkit-background-clip:text;background-clip:text;color:transparent}
.brand small{display:block;color:#ff7adf;font-weight:800;letter-spacing:7px;margin-top:5px}
.nav{display:grid;gap:7px}
.nav button{border:1px solid transparent;background:transparent;color:#b9b3d6;text-align:left;padding:12px 12px;border-radius:13px;display:flex;gap:12px;align-items:center;cursor:pointer;transition:.2s}
.nav button:hover{background:rgba(128,58,255,.11);color:#fff}
.nav button.active{background:linear-gradient(90deg,rgba(91,39,255,.78),rgba(196,32,245,.78));border-color:#8f58ff;box-shadow:0 0 25px rgba(153,52,255,.3);color:white}
.nav .icon{width:20px;text-align:center;font-size:17px}
.sidebar-card{margin-top:24px;padding:15px;border:1px solid var(--line);background:linear-gradient(145deg,#18103c,#0d0a24);border-radius:16px;box-shadow:var(--shadow)}
.sidebar-card .gift{font-size:30px}
.sidebar-card strong{display:block;margin-top:6px}
.sidebar-card p{margin:7px 0 0;color:var(--muted);font-size:12px;line-height:1.45}
.sidebar-card .btn{margin-top:12px;width:100%}
.main{min-width:0;padding:10px 14px 26px}
.topbar{height:58px;display:flex;gap:12px;align-items:center;margin-bottom:12px}
.menu-btn{display:none}
.search{flex:1;position:relative}
.search input{width:100%;height:42px;border-radius:13px;border:1px solid #2d2360;background:#0b0820;color:white;padding:0 44px 0 15px;outline:none;box-shadow:inset 0 0 18px rgba(85,39,255,.08)}
.search input:focus{border-color:#7148ff;box-shadow:0 0 0 3px rgba(113,72,255,.12)}
.search span{position:absolute;right:14px;top:11px;color:#7f78a0}
.top-pill{height:42px;padding:0 14px;display:flex;align-items:center;gap:9px;border:1px solid var(--line);border-radius:13px;background:#0b0820;font-size:13px;white-space:nowrap}
.dot{width:8px;height:8px;border-radius:50%;background:var(--green);box-shadow:0 0 12px var(--green)}
.balance{border-color:#3b2a83}
.balance b{color:var(--gold)}
.profile{display:flex;align-items:center;gap:10px;padding-right:6px}
.avatar{width:32px;height:32px;border-radius:10px;background:linear-gradient(135deg,#df2eff,#4d38ff);display:grid;place-items:center;font-weight:800}
.hero-grid{display:grid;grid-template-columns:minmax(0,1.35fr) minmax(365px,1fr);gap:12px}
.hero{position:relative;overflow:hidden;border-radius:18px;border:1px solid #4a28a3;min-height:280px;padding:28px;background:
radial-gradient(circle at 82% 22%,rgba(255,30,218,.48),transparent 25%),
radial-gradient(circle at 78% 78%,rgba(21,181,255,.25),transparent 28%),
linear-gradient(135deg,#251050,#0b0922 62%,#08051a);box-shadow:var(--shadow)}
.hero:before,.hero:after{content:"";position:absolute;border-radius:50%;filter:blur(2px)}
.hero:before{width:280px;height:280px;right:-70px;top:-85px;border:1px solid rgba(255,87,231,.55);box-shadow:0 0 70px rgba(255,35,214,.26)}
.hero:after{width:170px;height:170px;right:110px;bottom:-85px;border:1px solid rgba(37,210,255,.45);box-shadow:0 0 60px rgba(32,183,255,.2)}
.hero-content{position:relative;z-index:2;max-width:60%}
.kicker{display:inline-flex;align-items:center;gap:7px;color:#cfc7ff;border:1px solid #4b3989;padding:6px 10px;border-radius:999px;background:rgba(20,11,49,.72);font-size:11px;font-weight:800;letter-spacing:.7px}
.hero h1{font-size:clamp(40px,6vw,77px);line-height:.9;margin:20px 0 12px;letter-spacing:-4px}
.hero h1 span{display:block;background:linear-gradient(90deg,#ff35d7,#3ba6ff);-webkit-background-clip:text;background-clip:text;color:transparent}
.hero p{color:#c6bfd9;max-width:560px;line-height:1.6;margin:0}
.actions{display:flex;gap:10px;margin-top:22px;flex-wrap:wrap}
.btn{border:0;color:#fff;font-weight:850;cursor:pointer;padding:12px 17px;border-radius:12px;background:linear-gradient(90deg,#7a26ff,#f019c6,#1f8fff);box-shadow:0 9px 28px rgba(130,42,255,.3)}
.btn.secondary{border:1px solid #49377f;background:#110c2b}
.stats-strip{display:grid;grid-template-columns:repeat(4,1fr);gap:8px;margin-top:20px}
.stat{padding:10px 11px;border:1px solid #35256d;background:rgba(7,5,20,.52);border-radius:12px}
.stat b{display:block;font-size:15px}
.stat span{font-size:10px;color:#9d96bc}
.side-stack{display:grid;gap:12px}
.side-card{border:1px solid var(--line);background:linear-gradient(145deg,#120d2f,#0a0720);border-radius:18px;padding:16px;box-shadow:var(--shadow)}
.side-card h3{margin:0 0 11px;font-size:14px}
.live-row,.rank-row{display:flex;align-items:center;gap:9px;padding:8px 0;border-bottom:1px solid rgba(64,45,119,.36)}
.live-row:last-child,.rank-row:last-child{border-bottom:0}
.mini-avatar{width:28px;height:28px;border-radius:9px;background:linear-gradient(135deg,#253d9f,#ff29d1);display:grid;place-items:center;font-size:12px;font-weight:800}
.live-row small,.rank-row small{color:#948dad}
.live-row strong{margin-left:auto;color:#4ae1ac;font-size:12px}
.rank-row .n{width:22px;text-align:center;color:#8e83b7;font-weight:800}
.rank-row strong{margin-left:auto;color:#e7c76c;font-size:12px}
.event{background:
linear-gradient(135deg,rgba(30,13,72,.8),rgba(100,21,82,.55)),
radial-gradient(circle at 95% 30%,rgba(255,215,77,.35),transparent 28%);position:relative;overflow:hidden}
.event .time{font-size:30px;font-weight:900;margin:10px 0 2px}
.event .time small{font-size:10px;color:#9991b8;font-weight:600}
.section{margin-top:14px}
.section-head{display:flex;align-items:center;justify-content:space-between;gap:12px;margin:0 2px 9px}
.section-head h2{font-size:15px;margin:0}
.section-head span{font-size:11px;color:#968caf}
.games{display:grid;grid-template-columns:repeat(8,minmax(130px,1fr));gap:9px;overflow:hidden}
.game{position:relative;min-height:173px;border-radius:16px;border:1px solid #39267f;background:linear-gradient(180deg,#171035,#0c0920);overflow:hidden;cursor:pointer;transition:.22s;box-shadow:0 12px 30px rgba(0,0,0,.27)}
.game:hover{transform:translateY(-3px);border-color:#8a54ff;box-shadow:0 18px 40px rgba(86,44,204,.25)}
.game-art{height:108px;position:relative;overflow:hidden;background:#1a1035}
.game-art:before,.game-art:after{content:"";position:absolute;border-radius:50%}
.game-art:before{width:150px;height:150px;left:-45px;bottom:-65px;background:radial-gradient(circle,rgba(255,25,209,.72),transparent 64%)}
.game-art:after{width:180px;height:180px;right:-60px;top:-75px;background:radial-gradient(circle,rgba(26,176,255,.48),transparent 64%)}
.game-icon{position:absolute;inset:0;display:grid;place-items:center;font-size:44px;filter:drop-shadow(0 7px 15px rgba(0,0,0,.4))}
.tag{position:absolute;top:7px;left:7px;background:#ff1d8f;border-radius:999px;font-size:9px;font-weight:900;padding:4px 7px;z-index:2}
.tag.blue{background:#2676ff}.tag.gold{background:#b7800f}
.game-body{padding:9px 9px 10px}
.game-body b{display:block;font-size:12px}
.game-body small{color:#8e87ac;font-size:10px}
.play{margin-top:7px;width:100%;padding:7px;border-radius:8px;border:1px solid #4c34a5;background:linear-gradient(90deg,#4725f9,#1c8fff);color:#fff;font-weight:800;font-size:10px}
.dashboard{display:grid;grid-template-columns:1.35fr 1fr 1fr 1fr;gap:10px;margin-top:14px}
.widget{min-height:344px;border-radius:17px;border:1px solid var(--line);background:linear-gradient(145deg,#100a27,#09071c);overflow:hidden;box-shadow:var(--shadow)}
.widget-head{height:45px;padding:0 13px;display:flex;justify-content:space-between;align-items:center;border-bottom:1px solid rgba(58,40,111,.55);font-size:13px;font-weight:800}
.widget-head small{font-size:9px;color:#8f88ac}
.crash{height:284px;padding:15px;display:flex;flex-direction:column;justify-content:flex-end;position:relative;background:
linear-gradient(180deg,rgba(28,18,65,.15),rgba(3,2,14,.25)),
repeating-linear-gradient(0deg,transparent,transparent 36px,rgba(60,45,113,.18) 37px),
repeating-linear-gradient(90deg,transparent,transparent 58px,rgba(60,45,113,.16) 59px)}
.mult{font-size:42px;font-weight:950;letter-spacing:-2px;text-shadow:0 0 30px rgba(53,181,255,.35)}
.graph{height:62px;position:relative;margin-top:-4px}
.graph svg{width:100%;height:100%}
.controls{display:flex;gap:7px;margin-top:8px}.chip{border:1px solid #34256e;background:#0e0a25;border-radius:8px;color:#a9a1c5;padding:7px 9px;font-size:9px}
.widget-body{padding:12px}
.slot{display:grid;grid-template-columns:repeat(4,1fr);gap:7px;margin-top:8px}
.symbol{height:51px;border-radius:10px;border:1px solid #5d2f9b;background:radial-gradient(circle,#3a1b72,#140b2e);display:grid;place-items:center;font-size:23px;box-shadow:inset 0 0 22px rgba(255,31,215,.1)}
.field{display:flex;justify-content:space-between;align-items:center;margin-top:10px;border:1px solid #34256d;border-radius:9px;padding:8px 9px;background:#0d0922}
.field span{color:#9189a9;font-size:9px}.field b{font-size:11px}
.blackjack{height:284px;padding:14px;display:flex;flex-direction:column;justify-content:space-between;background:radial-gradient(circle at 50% 20%,#3a1737,#170c26 58%,#09061a)}
.table{border-radius:16px;border:1px solid #55356c;background:radial-gradient(circle at center,#2a1a29,#110919);height:118px;display:grid;place-items:center;position:relative}
.cards{display:flex;gap:6px;transform:rotate(-6deg)}
.card{height:61px;width:44px;border-radius:6px;background:#fff;color:#111;display:grid;place-items:center;font-size:20px;font-weight:900;box-shadow:0 8px 16px rgba(0,0,0,.4)}
.card.red{color:#cc1733}
.pills{display:flex;gap:6px}.pill{flex:1;padding:8px 5px;text-align:center;border-radius:8px;font-size:9px;font-weight:850;border:1px solid #384090;background:#201757}
.pill.hot{background:linear-gradient(90deg,#7b240f,#c58a13);border-color:#e2b23a}
.wallet{height:100%;padding:13px}.wallet .amount{font-size:31px;font-weight:950;color:#f1cb67;margin:8px 0 1px}
.wallet p{font-size:10px;color:#8f88a7;margin:0 0 14px}.wallet .wallet-row{display:grid;grid-template-columns:repeat(3,1fr);gap:7px}.wallet .wallet-btn{padding:10px 7px;border-radius:9px;border:1px solid #3d2c7b;background:#120c2d;color:#bfb8d9;font-size:9px;font-weight:800;text-align:center}
.activity{margin-top:7px;display:grid;gap:6px}.activity .a{display:flex;justify-content:space-between;padding:7px 0;border-bottom:1px solid rgba(58,40,111,.34);font-size:9px}.a span{color:#8f88a9}.a b{color:#48dda1}
.footer{margin-top:15px;color:#736b90;font-size:10px;display:flex;justify-content:space-between;gap:10px}
.mobile-nav{display:none}
.toast{position:fixed;right:18px;bottom:18px;background:#130c2e;border:1px solid #6846b6;border-radius:12px;padding:10px 14px;color:#fff;font-size:11px;box-shadow:0 18px 40px rgba(0,0,0,.45);opacity:0;transform:translateY(10px);pointer-events:none;transition:.25s;z-index:99}
.toast.show{opacity:1;transform:translateY(0)}
@media (max-width:1200px){.games{grid-template-columns:repeat(4,1fr)}.dashboard{grid-template-columns:1fr 1fr}.wallet-widget{grid-column:span 2}}
@media (max-width:900px){.app{grid-template-columns:1fr}.sidebar{display:none}.main{padding:10px 10px 74px}.menu-btn{display:grid;place-items:center;width:42px;height:42px;border:1px solid #34256d;border-radius:12px;background:#0b0820;color:#fff}.topbar{height:48px}.top-pill{display:none}.hero-grid{grid-template-columns:1fr}.side-stack{grid-template-columns:1fr 1fr}.hero-content{max-width:100%}.hero{min-height:330px}.games{grid-template-columns:repeat(2,1fr)}.dashboard{grid-template-columns:1fr}.wallet-widget{grid-column:auto}.mobile-nav{display:flex;position:fixed;z-index:30;left:8px;right:8px;bottom:8px;height:58px;border:1px solid #3a2a79;background:rgba(10,6,26,.94);backdrop-filter:blur(14px);border-radius:16px;justify-content:space-around;align-items:center;box-shadow:0 16px 44px rgba(0,0,0,.48)}.mobile-nav button{border:0;background:transparent;color:#9189ad;font-size:10px;display:grid;gap:3px;justify-items:center}.mobile-nav button.active{color:#fff}.mobile-nav .mi{font-size:18px}}
@media (max-width:560px){.side-stack{grid-template-columns:1fr}.hero{padding:20px;min-height:360px}.hero h1{font-size:48px}.stats-strip{grid-template-columns:repeat(2,1fr)}.games{grid-template-columns:repeat(2,1fr)}.game{min-height:165px}.game-art{height:100px}.footer{display:block}.footer span{display:block;margin-top:4px}}
.mobile-preview{margin-top:16px;border:1px solid #2e2268;border-radius:18px;background:linear-gradient(180deg,#0c0821,#070515);padding:12px}.mobile-preview .label{display:flex;align-items:center;justify-content:center;margin:-2px auto 12px;width:max-content;padding:7px 16px;border:1px solid #3f2d7e;border-radius:999px;background:#0b0820;color:#d8d0ef;font-size:10px;font-weight:900;letter-spacing:.7px}.phones{display:grid;grid-template-columns:repeat(6,1fr);gap:10px;overflow:hidden}.phone{min-width:0;height:138px;border-radius:16px;border:1px solid #332571;background:linear-gradient(180deg,#120d31,#070518);padding:7px;box-shadow:inset 0 0 28px rgba(119,49,255,.08)}.phone .ph-head{font-size:7px;color:#8f88ab;margin-bottom:7px;display:flex;justify-content:space-between}.phone .screen{height:73px;border-radius:10px;border:1px solid #45328b;background:radial-gradient(circle at 65% 25%,rgba(255,35,211,.4),transparent 25%),linear-gradient(145deg,#221048,#09071c);display:grid;place-items:center;font-size:25px}.phone b{display:block;font-size:8px;margin-top:7px}.phone small{font-size:7px;color:#827b9e}@media (max-width:900px){.mobile-preview{display:none}}
</style>
</head>
<body>
<div class="app">
  <aside class="sidebar">
    <div class="brand"><b>BIKA</b><small>GAME</small></div>
    <div class="nav">
      <button class="active" data-section="home"><span class="icon">⌂</span>Home</button>
      <button data-section="games"><span class="icon">🎮</span>Games</button>
      <button data-section="live"><span class="icon">◉</span>Live</button>
      <button data-section="tournament"><span class="icon">🏆</span>Tournament</button>
      <button data-section="leaderboard"><span class="icon">☷</span>Leaderboard</button>
      <button data-section="wallet"><span class="icon">▣</span>Wallet</button>
      <button data-section="history"><span class="icon">◷</span>History</button>
      <button data-section="profile"><span class="icon">♙</span>Profile</button>
      <button data-section="vip"><span class="icon">✦</span>VIP Club</button>
      <button data-section="referral"><span class="icon">♧</span>Referral</button>
      <button data-section="settings"><span class="icon">⚙</span>Settings</button>
    </div>
    <div class="sidebar-card">
      <div class="gift">🎁</div><strong>Daily Bonus</strong>
      <p>Claim your reward and keep your Arena streak alive.</p>
      <button class="btn" onclick="toast('Daily Bonus UI is ready')">CLAIM BONUS</button>
    </div>
  </aside>

  <main class="main" id="home">
    <header class="topbar">
      <button class="menu-btn" onclick="toast('Use the bottom navigation on mobile')">☰</button>
      <div class="search"><input id="search" type="search" placeholder="Search characters, sources, or events..."><span>⌕</span></div>
      <div class="top-pill"><span class="dot"></span><span>Service Ready</span></div>
      <div class="top-pill balance">Database <b id="sourceCount">—</b></div>
      <div class="top-pill profile"><div class="avatar">B</div><div><b style="font-size:12px">Official Bika</b><div style="font-size:9px;color:#938ba9">Level 18</div></div></div>
      <button class="btn" style="height:42px;padding:0 16px;border-radius:12px;white-space:nowrap" onclick="toast('Deposit flow is not connected to the existing bot data')">DEPOSIT</button>
      <div class="top-pill" style="font-size:16px;padding:0 11px">✈️</div>
      <div class="top-pill" style="font-size:16px;padding:0 11px">⛶</div>
    </header>

    <section class="hero-grid">
      <div class="hero">
        <div class="hero-content">
          <span class="kicker">⚡ NEXT-GEN WEB ARENA</span>
          <h1>BIKA <span>GAME ARENA</span></h1>
          <p>PLAY • WIN • UPGRADE • BE A LEGEND</p>
          <p style="margin-top:8px">A premium neon dashboard built around your existing BIKA service and MongoDB data layer. The UI is responsive from desktop to mobile.</p>
          <div class="actions">
            <button class="btn" onclick="document.getElementById('games').scrollIntoView({behavior:'smooth'})">PLAY NOW</button>
            <button class="btn secondary" onclick="refreshData()">REFRESH DATA</button>
          </div>
          <div class="stats-strip">
            <div class="stat"><b id="totalChars">—</b><span>CHARACTERS</span></div>
            <div class="stat"><b id="todayUpdates">—</b><span>UPDATES / 24H</span></div>
            <div class="stat"><b id="uptimeStatus">ONLINE</b><span>APP STATUS</span></div>
            <div class="stat"><b>MongoDB</b><span>AUTHORITY</span></div>
          </div>
        </div>
      </div>

      <div class="side-stack">
        <div class="side-card">
          <h3>👥 Live Service</h3>
          <div class="live-row"><div class="mini-avatar">B</div><div><b>BIKA Bot</b><small style="display:block">Webhook / Mini App</small></div><strong>ONLINE</strong></div>
          <div class="live-row"><div class="mini-avatar">DB</div><div><b>MongoDB</b><small style="display:block">Authoritative store</small></div><strong id="dbState">CHECK</strong></div>
          <div class="live-row"><div class="mini-avatar">⚡</div><div><b>UID / Hash Index</b><small style="display:block">Accelerators active</small></div><strong>READY</strong></div>
        </div>
        <div class="side-card event">
          <div style="font-size:10px;color:#c9a8ff;letter-spacing:1px">DAILY EVENT</div>
          <h3 style="color:#ff4fe4;font-size:18px;margin:4px 0">MEGA REWARDS</h3>
          <div class="time">LIVE <small>DATA SYNC</small></div>
          <button class="btn" style="width:100%;margin-top:8px" onclick="refreshData()">SYNC NOW</button>
        </div>
        <div class="side-card">
          <h3>🏆 Ranking — UI Preview</h3>
          <div class="rank-row"><span class="n">1</span><div class="mini-avatar">K</div><b>Kyaw Gyi</b><strong>1,250,000</strong></div>
          <div class="rank-row"><span class="n">2</span><div class="mini-avatar">M</div><b>Maung Maung</b><strong>980,500</strong></div>
          <div class="rank-row"><span class="n">3</span><div class="mini-avatar">T</div><b>Thant Zin</b><strong>850,200</strong></div>
          <div style="font-size:9px;color:#746e8f;margin-top:8px">Visual component only — no fabricated wallet/game transaction data.</div>
        </div>
      </div>
    </section>

    <section class="section" id="games">
      <div class="section-head"><h2>🔥 Popular Games</h2><span>Visual UI / launch-ready shell →</span></div>
      <div class="games">
        <article class="game"><div class="game-art"><span class="tag">+ LIVE</span><div class="game-icon">🚀</div></div><div class="game-body"><b>Rocket Crash</b><small>Realtime-style panel</small><button class="play" onclick="toast('Rocket Crash shell selected')">PLAY NOW</button></div></article>
        <article class="game"><div class="game-art"><span class="tag gold">HOT</span><div class="game-icon">🎰</div></div><div class="game-body"><b>Premium Slot</b><small>Premium neon reels</small><button class="play" onclick="toast('Premium Slot shell selected')">PLAY NOW</button></div></article>
        <article class="game"><div class="game-art"><span class="tag blue">LIVE</span><div class="game-icon">🃏</div></div><div class="game-body"><b>Blackjack</b><small>Casino table shell</small><button class="play" onclick="toast('Blackjack shell selected')">PLAY NOW</button></div></article>
        <article class="game"><div class="game-art"><div class="game-icon">🎲</div></div><div class="game-body"><b>Shan Koe Mee</b><small>Game card ready</small><button class="play" onclick="toast('Shan Koe Mee shell selected')">PLAY NOW</button></div></article>
        <article class="game"><div class="game-art"><div class="game-icon">✨</div></div><div class="game-body"><b>Plinko</b><small>Arcade-style panel</small><button class="play" onclick="toast('Plinko shell selected')">PLAY NOW</button></div></article>
        <article class="game"><div class="game-art"><div class="game-icon">🎡</div></div><div class="game-body"><b>Lucky Wheel</b><small>Reward wheel shell</small><button class="play" onclick="toast('Lucky Wheel shell selected')">PLAY NOW</button></div></article>
        <article class="game"><div class="game-art"><span class="tag blue">LIVE</span><div class="game-icon">💣</div></div><div class="game-body"><b>Mines</b><small>Arcade-style panel</small><button class="play" onclick="toast('Mines shell selected')">PLAY NOW</button></div></article>
        <article class="game"><div class="game-art"><span class="tag" style="background:#4d416c">SOON</span><div class="game-icon">♛</div></div><div class="game-body"><b>Coming Soon</b><small>More arena games</small><button class="play" onclick="toast('Coming soon')">COMING SOON</button></div></article>
      </div>
    </section>

    <section class="dashboard">
      <article class="widget">
        <div class="widget-head"><span>🚀 Rocket Crash</span><small>LIVE UI SHELL</small></div>
        <div class="crash">
          <div style="font-size:9px;color:#85809e">MULTIPLIER</div>
          <div class="mult">3.42x</div>
          <div class="graph">
            <svg viewBox="0 0 500 80" preserveAspectRatio="none" aria-hidden="true"><defs><linearGradient id="g1" x1="0" x2="1"><stop offset="0" stop-color="#9c39ff"/><stop offset="1" stop-color="#1fbbff"/></linearGradient></defs><path d="M0,74 C70,78 95,68 140,59 S215,52 251,38 325,34 358,20 435,18 500,4" fill="none" stroke="url(#g1)" stroke-width="5" stroke-linecap="round"/><path d="M0,79 L0,74 C70,78 95,68 140,59 S215,52 251,38 325,34 358,20 435,18 500,4 L500,80Z" fill="url(#g1)" opacity=".09"/></svg>
          </div>
          <div class="controls"><span class="chip">1s</span><span class="chip">2s</span><span class="chip">4s</span><span class="chip">6s</span><span class="chip">8s</span><span class="chip">10s</span></div>
        </div>
      </article>

      <article class="widget">
        <div class="widget-head"><span>🎰 Premium Slot</span><small>HOT</small></div>
        <div class="widget-body">
          <div style="text-align:center;font-size:10px;color:#ff7de5">JACKPOT</div>
          <div style="text-align:center;font-size:20px;font-weight:950;color:#ffd56b">125,680,000</div>
          <div class="slot"><div class="symbol">7</div><div class="symbol">💎</div><div class="symbol">👑</div><div class="symbol">🍀</div><div class="symbol">🍒</div><div class="symbol">🔔</div><div class="symbol">7</div><div class="symbol">💠</div></div>
          <div class="field"><span>BET AMOUNT</span><b>50,000</b></div>
          <button class="btn" style="width:100%;margin-top:9px" onclick="toast('Spin shell selected')">SPIN NOW</button>
        </div>
      </article>

      <article class="widget">
        <div class="widget-head"><span>🃏 Blackjack</span><small>LIVE UI SHELL</small></div>
        <div class="blackjack">
          <div class="table">
            <div style="position:absolute;top:9px;font-size:9px;color:#b5a8ba">DEALER 17</div>
            <div class="cards"><div class="card red">7♥</div><div class="card">Q♣</div></div>
          </div>
          <div><div style="font-size:9px;color:#9a91ac;margin-bottom:6px">PLAYER 19</div><div class="pills"><div class="pill" style="background:#123d2f">HIT</div><div class="pill" style="background:#511b35">STAND</div><div class="pill hot">DOUBLE</div><div class="pill">SPLIT</div></div></div>
        </div>
      </article>

      <article class="widget wallet-widget">
        <div class="widget-head"><span>💰 Wallet</span><small>UI PREVIEW</small></div>
        <div class="wallet">
          <div style="font-size:10px;color:#8f88a9">Current Balance</div>
          <div class="amount">—</div>
          <p>Wallet values are intentionally not fabricated by this UI.</p>
          <div class="wallet-row"><div class="wallet-btn" onclick="toast('Deposit flow placeholder')">DEPOSIT</div><div class="wallet-btn">WITHDRAW</div><div class="wallet-btn">HISTORY</div></div>
          <div class="activity"><div class="a"><span>Database Records</span><b id="activityCount">—</b></div><div class="a"><span>Sources</span><b id="activitySources">—</b></div><div class="a"><span>Service</span><b>ONLINE</b></div></div>
        </div>
      </article>
    </section>

    <section class="section">
      <div class="section-head"><h2>🗂️ Latest Character Data</h2><span id="updatedAt">Waiting for sync…</span></div>
      <div class="widget" style="min-height:0">
        <div id="recent" style="padding:10px 13px;color:#8f88a7;font-size:10px">Loading authoritative MongoDB data…</div>
      </div>
    </section>

<section class="mobile-preview">
      <div class="label">▣ MOBILE VERSION (RESPONSIVE DESIGN)</div>
      <div class="phones">
        <div class="phone"><div class="ph-head"><span>BIKA GAME</span><span>•••</span></div><div class="screen">🎮</div><b>Home</b><small>Play now</small></div>
        <div class="phone"><div class="ph-head"><span>Games</span><span>●</span></div><div class="screen">🚀</div><b>Games</b><small>Popular</small></div>
        <div class="phone"><div class="ph-head"><span>Rocket</span><span>LIVE</span></div><div class="screen">3.42x</div><b>Rocket Crash</b><small>Multiplier</small></div>
        <div class="phone"><div class="ph-head"><span>Slot</span><span>HOT</span></div><div class="screen">🎰</div><b>Premium Slot</b><small>Spin now</small></div>
        <div class="phone"><div class="ph-head"><span>Blackjack</span><span>LIVE</span></div><div class="screen">🃏</div><b>Blackjack</b><small>Hit / Stand</small></div>
        <div class="phone"><div class="ph-head"><span>Profile</span><span>⚙</span></div><div class="screen">B</div><b>Official Bika</b><small>Level 18</small></div>
      </div>
    </section>

    <footer class="footer"><span>BIKA GAME Arena UI • Neon responsive shell</span><span>Existing Telegram/lookup logic is kept separate from the presentation layer.</span></footer>
  </main>
</div>

<nav class="mobile-nav">
  <button class="active" onclick="scrollToId('home')"><span class="mi">⌂</span>Home</button>
  <button onclick="scrollToId('games')"><span class="mi">🎮</span>Games</button>
  <button onclick="scrollToId('live')"><span class="mi">◉</span>Live</button>
  <button onclick="scrollToId('wallet')"><span class="mi">▣</span>Wallet</button>
  <button onclick="refreshData()"><span class="mi">↻</span>Sync</button>
</nav>
<div id="toast" class="toast"></div>

<script>
const $ = (id)=>document.getElementById(id);
function toast(message){const t=$('toast');t.textContent=message;t.classList.add('show');clearTimeout(window.__toast);window.__toast=setTimeout(()=>t.classList.remove('show'),1800)}
function scrollToId(id){const el=document.getElementById(id);if(el)el.scrollIntoView({behavior:'smooth',block:'start'});else window.scrollTo({top:0,behavior:'smooth'})}
function fmt(n){return new Intl.NumberFormat().format(Number(n||0))}
function esc(s){return String(s??'').replace(/[&<>"']/g,m=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[m]))}
async function refreshData(){
  try{
    const r=await fetch('/miniapp/api/overview',{cache:'no-store'});
    const data=await r.json();
    $('totalChars').textContent=fmt(data.total_characters);
    $('todayUpdates').textContent=fmt(data.updates_24h);
    $('sourceCount').textContent=fmt(data.source_count);
    $('activityCount').textContent=fmt(data.total_characters);
    $('activitySources').textContent=fmt(data.source_count);
    $('dbState').textContent=data.database_ok?'ONLINE':'CHECK';
    $('uptimeStatus').textContent=data.database_ok?'ONLINE':'CHECK';
    $('updatedAt').textContent='Synced '+new Date().toLocaleTimeString();
    $('recent').innerHTML=(data.recent||[]).map(row=>{
      const date=row.updated_at?new Date(row.updated_at).toLocaleString():'—';
      return '<div style="display:grid;grid-template-columns:2fr 1fr 1fr 1fr;gap:10px;padding:9px 0;border-bottom:1px solid rgba(58,40,111,.34)"><b style="color:#fff">'+esc(row.name||'Unknown')+'</b><span>'+esc(row.source_key||'unknown')+'</span><span>'+esc(row.media_type||'unknown')+'</span><span style="text-align:right">'+esc(date)+'</span></div>';
    }).join('')||'<div>No character records returned.</div>';
  }catch(e){
    $('dbState').textContent='ERROR';$('uptimeStatus').textContent='CHECK';$('recent').textContent='Data sync failed. The UI shell remains available.';
  }
}
document.querySelectorAll('.nav button').forEach(btn=>btn.addEventListener('click',()=>{
  document.querySelectorAll('.nav button').forEach(x=>x.classList.remove('active'));btn.classList.add('active');
  const s=btn.dataset.section;
  if(s==='home')window.scrollTo({top:0,behavior:'smooth'});
  else if(s==='games')scrollToId('games');
  else toast(s.toUpperCase()+' view is part of the UI shell');
}));
$('search').addEventListener('input',e=>{
  const q=e.target.value.trim().toLowerCase();
  document.querySelectorAll('.game').forEach(card=>card.style.display=!q||card.textContent.toLowerCase().includes(q)?'':'none');
});
refreshData();
</script>
</body>
</html>"""


async def miniapp_page(_: web.Request) -> web.Response:
    return web.Response(text=INDEX_HTML, content_type="text/html", charset="utf-8")


async def miniapp_overview(_: web.Request) -> web.Response:
    now = datetime.now(timezone.utc)
    payload = {
        "database_ok": False,
        "total_characters": 0,
        "updates_24h": 0,
        "source_count": 0,
        "recent": [],
    }
    try:
        await db.command("ping")
        payload["database_ok"] = True
        payload["total_characters"] = await characters.count_documents({})
        payload["updates_24h"] = await characters.count_documents(
            {"updated_at": {"$gte": now - timedelta(hours=24)}}
        )
        source_values = await characters.distinct("source_key")
        payload["source_count"] = len([x for x in source_values if str(x).strip()])
        cursor = characters.find(
            {},
            {
                "_id": 0,
                "name": 1,
                "source_key": 1,
                "media_type": 1,
                "updated_at": 1,
            },
        ).sort("updated_at", -1).limit(8)
        async for row in cursor:
            value = row.get("updated_at")
            if isinstance(value, datetime):
                value = value.astimezone(timezone.utc).isoformat()
            else:
                value = str(value or "")
            payload["recent"].append(
                {
                    "name": escape(str(row.get("name") or "Unknown")),
                    "source_key": escape(str(row.get("source_key") or "unknown")),
                    "media_type": escape(str(row.get("media_type") or "unknown")),
                    "updated_at": value,
                }
            )
    except Exception:
        # The page itself remains available even if the database is temporarily unavailable.
        pass
    return web.json_response(payload)


def register_miniapp(app: web.Application) -> None:
    app.router.add_get("/miniapp", miniapp_page)
    app.router.add_get("/miniapp/", miniapp_page)
    app.router.add_get("/miniapp/api/overview", miniapp_overview)
