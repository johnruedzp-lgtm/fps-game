"use strict";

const canvas = document.getElementById("gameCanvas");
const ctx = canvas.getContext("2d", {
  alpha: false,
  desynchronized: true
});

const ui = {
  hud: document.getElementById("hud"),
  menu: document.getElementById("menu"),
  pause: document.getElementById("pauseMenu"),
  gameOver: document.getElementById("gameOver"),
  unsupported: document.getElementById("unsupported"),
  score: document.getElementById("score"),
  wave: document.getElementById("wave"),
  enemies: document.getElementById("enemies"),
  health: document.getElementById("health"),
  healthBar: document.getElementById("healthBar"),
  ammo: document.getElementById("ammo"),
  reserve: document.getElementById("reserve"),
  message: document.getElementById("message"),
  hitMarker: document.getElementById("hitMarker"),
  damageFlash: document.getElementById("damageFlash"),
  muzzleFlash: document.getElementById("muzzleFlash"),
  weapon: document.getElementById("weapon"),
  finalScore: document.getElementById("finalScore"),
  finalWave: document.getElementById("finalWave"),
  quality: document.getElementById("quality"),
  start: document.getElementById("startButton"),
  resume: document.getElementById("resumeButton"),
  restart: document.getElementById("restartButton")
};

const TAU = Math.PI * 2;
const FOV = Math.PI / 3;
const HALF_FOV = FOV / 2;
const MAP_SIZE = 24;
const MOVE_SPEED = 3.4;
const SPRINT_SPEED = 5.2;
const PLAYER_RADIUS = 0.22;
const MAX_DEPTH = 22;

const map = [
  "111111111111111111111111",
  "100000000000000000000001",
  "100000000000000000000001",
  "100011100000011100000001",
  "100010000000000100000001",
  "100010000222000100000001",
  "100000000202000000000001",
  "100000000202000000000001",
  "100001000202000001000001",
  "100001000222000001000001",
  "100001000000000001000001",
  "100001110000001111000001",
  "100000000000000000000001",
  "100000000033300000000001",
  "100000000030300000000001",
  "100001100030300011000001",
  "100001000033300001000001",
  "100001000000000001000001",
  "100001000111100001000001",
  "100000000100100000000001",
  "100000000100100000000001",
  "100000000000000000000001",
  "100000000000000000000001",
  "111111111111111111111111"
];

let screenW = 1280;
let screenH = 720;
let renderScale = 0.82;
let columnWidth = 2;
let rayCount = 640;
let projectionPlane = 640;
let depthBuffer = new Float32Array(rayCount);

let state = "menu";
let previousTime = performance.now();
let score = 0;
let wave = 1;
let health = 100;
let ammo = 30;
let reserve = 180;
let reloading = false;
let reloadTimer = 0;
let fireCooldown = 0;
let bobTime = 0;
let recoil = 0;
let verticalVelocity = 0;
let cameraHeight = 0;
let messageTimer = 0;
let hitTimer = 0;
let damageTimer = 0;
let muzzleTimer = 0;
let waveDelay = 0;
let animationFrame = 0;

const keys = Object.create(null);
const enemies = [];
const particles = [];

const player = {
  x: 2.5,
  y: 2.5,
  angle: 0
};

function resize() {
  renderScale = Number(ui.quality.value) || 0.82;

  const cssW = window.innerWidth;
  const cssH = window.innerHeight;
  const dpr = Math.min(window.devicePixelRatio || 1, 1.5);

  screenW = Math.max(480, Math.floor(cssW * dpr * renderScale));
  screenH = Math.max(270, Math.floor(cssH * dpr * renderScale));

  canvas.width = screenW;
  canvas.height = screenH;

  rayCount = Math.max(240, Math.min(960, Math.floor(screenW / 2)));
  columnWidth = screenW / rayCount;
  projectionPlane = screenW / (2 * Math.tan(HALF_FOV));
  depthBuffer = new Float32Array(rayCount);

  ctx.imageSmoothingEnabled = false;
}

function mapCell(x, y) {
  const mx = Math.floor(x);
  const my = Math.floor(y);

  if (mx < 0 || my < 0 || mx >= MAP_SIZE || my >= MAP_SIZE) {
    return "1";
  }

  return map[my][mx];
}

function isWall(x, y) {
  return mapCell(x, y) !== "0";
}

function canMove(x, y, radius = PLAYER_RADIUS) {
  return !isWall(x - radius, y - radius) &&
    !isWall(x + radius, y - radius) &&
    !isWall(x - radius, y + radius) &&
    !isWall(x + radius, y + radius);
}

function normalizeAngle(angle) {
  while (angle > Math.PI) angle -= TAU;
  while (angle < -Math.PI) angle += TAU;
  return angle;
}

function castRay(originX, originY, angle, maxDepth = MAX_DEPTH) {
  const rayDirX = Math.cos(angle);
  const rayDirY = Math.sin(angle);

  let mapX = Math.floor(originX);
  let mapY = Math.floor(originY);

  const deltaX = rayDirX === 0 ? 1e30 : Math.abs(1 / rayDirX);
  const deltaY = rayDirY === 0 ? 1e30 : Math.abs(1 / rayDirY);

  const stepX = rayDirX < 0 ? -1 : 1;
  const stepY = rayDirY < 0 ? -1 : 1;

  let sideX = rayDirX < 0
    ? (originX - mapX) * deltaX
    : (mapX + 1 - originX) * deltaX;

  let sideY = rayDirY < 0
    ? (originY - mapY) * deltaY
    : (mapY + 1 - originY) * deltaY;

  let side = 0;
  let tile = "0";
  let distance = 0;

  for (let i = 0; i < 64; i++) {
    if (sideX < sideY) {
      mapX += stepX;
      distance = sideX;
      sideX += deltaX;
      side = 0;
    } else {
      mapY += stepY;
      distance = sideY;
      sideY += deltaY;
      side = 1;
    }

    tile = mapCell(mapX, mapY);
    if (tile !== "0" || distance >= maxDepth) break;
  }

  const hitX = originX + rayDirX * distance;
  const hitY = originY + rayDirY * distance;
  const wallOffset = side === 0
    ? hitY - Math.floor(hitY)
    : hitX - Math.floor(hitX);

  return {
    distance: Math.min(distance, maxDepth),
    side,
    tile,
    wallOffset
  };
}

function hasLineOfSight(x1, y1, x2, y2) {
  const dx = x2 - x1;
  const dy = y2 - y1;
  const distance = Math.hypot(dx, dy);

  if (distance < 0.001) return true;

  const hit = castRay(x1, y1, Math.atan2(dy, dx), distance + 0.05);
  return hit.distance >= distance - 0.12;
}

function randomOpenPosition(minDistance = 6) {
  for (let i = 0; i < 200; i++) {
    const x = 1.5 + Math.random() * (MAP_SIZE - 3);
    const y = 1.5 + Math.random() * (MAP_SIZE - 3);

    if (
      canMove(x, y, 0.32) &&
      Math.hypot(x - player.x, y - player.y) >= minDistance
    ) {
      return { x, y };
    }
  }

  return { x: 20.5, y: 20.5 };
}

function spawnWave() {
  const count = Math.min(4 + wave * 2, 28);

  enemies.length = 0;

  for (let i = 0; i < count; i++) {
    const position = randomOpenPosition(5);

    enemies.push({
      x: position.x,
      y: position.y,
      radius: 0.25,
      health: 55 + wave * 11,
      maxHealth: 55 + wave * 11,
      speed: 0.72 + Math.min(wave * 0.04, 0.55) + Math.random() * 0.13,
      damage: 5 + Math.floor(wave * 0.85),
      attackTimer: Math.random(),
      hurtTimer: 0,
      phase: Math.random() * TAU,
      dead: false
    });
  }

  showMessage(`WAVE ${wave}`, 1.8);
  updateHUD();
}

function resetGame() {
  player.x = 2.5;
  player.y = 2.5;
  player.angle = 0;

  score = 0;
  wave = 1;
  health = 100;
  ammo = 30;
  reserve = 180;
  reloading = false;
  reloadTimer = 0;
  fireCooldown = 0;
  recoil = 0;
  verticalVelocity = 0;
  cameraHeight = 0;
  bobTime = 0;
  waveDelay = 0;

  particles.length = 0;
  spawnWave();
  updateHUD();
}

function startGame(reset) {
  if (reset) resetGame();

  state = "playing";
  ui.menu.classList.add("hidden");
  ui.pause.classList.add("hidden");
  ui.gameOver.classList.add("hidden");
  ui.hud.classList.remove("hidden");

  canvas.requestPointerLock();
}

function pauseGame() {
  if (state !== "playing") return;

  state = "paused";
  ui.pause.classList.remove("hidden");
}

function endGame() {
  state = "gameover";
  ui.finalScore.textContent = String(score);
  ui.finalWave.textContent = String(wave);
  ui.gameOver.classList.remove("hidden");

  if (document.pointerLockElement) {
    document.exitPointerLock();
  }
}

function updateHUD() {
  ui.score.textContent = String(score);
  ui.wave.textContent = String(wave);
  ui.enemies.textContent = String(enemies.filter(enemy => !enemy.dead).length);
  ui.health.textContent = String(Math.max(0, Math.ceil(health)));
  ui.ammo.textContent = String(ammo);
  ui.reserve.textContent = String(reserve);

  const healthPercent = Math.max(0, health);
  ui.healthBar.style.width = `${healthPercent}%`;
  ui.healthBar.style.background =
    healthPercent > 55 ? "#35e8ff" :
    healthPercent > 25 ? "#ffd166" :
    "#ff385f";
}

function showMessage(text, duration = 1) {
  ui.message.textContent = text;
  ui.message.classList.add("visible");
  messageTimer = duration;
}

function reload() {
  if (reloading || ammo === 30 || reserve <= 0 || state !== "playing") {
    return;
  }

  reloading = true;
  reloadTimer = 1.45;
  showMessage("RELOADING", 1.2);
}

function completeReload() {
  const required = 30 - ammo;
  const loaded = Math.min(required, reserve);

  ammo += loaded;
  reserve -= loaded;
  reloading = false;
  updateHUD();
}

function shoot() {
  if (state !== "playing" || fireCooldown > 0 || reloading) return;

  if (ammo <= 0) {
    showMessage("EMPTY - PRESS R", 0.7);
    fireCooldown = 0.2;
    return;
  }

  ammo--;
  fireCooldown = 0.105;
  recoil = Math.min(recoil + 1, 2.2);
  muzzleTimer = 0.07;

  const spread = (Math.random() - 0.5) * 0.013;
  const shotAngle = player.angle + spread;
  const wallDistance = castRay(player.x, player.y, shotAngle).distance;

  let target = null;
  let closestDistance = wallDistance;

  for (const enemy of enemies) {
    if (enemy.dead) continue;

    const dx = enemy.x - player.x;
    const dy = enemy.y - player.y;
    const distance = Math.hypot(dx, dy);
    const angleDifference = Math.abs(
      normalizeAngle(Math.atan2(dy, dx) - shotAngle)
    );

    const angularRadius = Math.atan2(enemy.radius * 1.35, distance);

    if (
      angleDifference <= angularRadius &&
      distance < closestDistance &&
      hasLineOfSight(player.x, player.y, enemy.x, enemy.y)
    ) {
      target = enemy;
      closestDistance = distance;
    }
  }

  if (target) {
    const headshot =
      Math.random() < 0.2 &&
      Math.abs(cameraHeight) < 0.1;

    const damage = headshot ? 64 : 34 + Math.random() * 9;

    target.health -= damage;
    target.hurtTimer = 0.13;
    hitTimer = 0.12;

    spawnParticles(target.x, target.y, headshot ? "#ffd166" : "#ff385f");

    if (target.health <= 0) {
      target.dead = true;
      score += headshot ? 175 : 100;
      showMessage(headshot ? "HEADSHOT +175" : "ELIMINATED +100", 0.75);
    } else if (headshot) {
      showMessage("HEADSHOT", 0.5);
    }
  } else {
    const impactDistance = Math.min(wallDistance, 16);
    spawnParticles(
      player.x + Math.cos(shotAngle) * impactDistance,
      player.y + Math.sin(shotAngle) * impactDistance,
      "#82d9e8",
      3
    );
  }

  updateHUD();

  if (ammo === 0 && reserve > 0) {
    setTimeout(() => {
      if (state === "playing" && ammo === 0) reload();
    }, 180);
  }
}

function spawnParticles(x, y, color, count = 7) {
  if (particles.length > 90) {
    particles.splice(0, particles.length - 90);
  }

  for (let i = 0; i < count; i++) {
    particles.push({
      x,
      y,
      z: 0.45 + Math.random() * 0.45,
      vx: (Math.random() - 0.5) * 1.8,
      vy: (Math.random() - 0.5) * 1.8,
      vz: Math.random() * 1.3,
      life: 0.35 + Math.random() * 0.35,
      size: 1 + Math.random() * 3,
      color
    });
  }
}

function damagePlayer(amount) {
  if (state !== "playing") return;

  health -= amount;
  damageTimer = 0.24;
  updateHUD();

  if (health <= 0) {
    health = 0;
    updateHUD();
    endGame();
  }
}

function updatePlayer(dt) {
  let forward = 0;
  let strafe = 0;

  if (keys.KeyW || keys.ArrowUp) forward += 1;
  if (keys.KeyS || keys.ArrowDown) forward -= 1;
  if (keys.KeyD) strafe += 1;
  if (keys.KeyA) strafe -= 1;

  const moving = forward !== 0 || strafe !== 0;
  const magnitude = Math.hypot(forward, strafe) || 1;
  const sprinting = moving && (keys.ShiftLeft || keys.ShiftRight);
  const speed = sprinting ? SPRINT_SPEED : MOVE_SPEED;

  forward /= magnitude;
  strafe /= magnitude;

  const sin = Math.sin(player.angle);
  const cos = Math.cos(player.angle);
  const dx = (cos * forward - sin * strafe) * speed * dt;
  const dy = (sin * forward + cos * strafe) * speed * dt;

  if (canMove(player.x + dx, player.y)) player.x += dx;
  if (canMove(player.x, player.y + dy)) player.y += dy;

  if (moving) {
    bobTime += dt * (sprinting ? 13 : 9);
  }

  if (verticalVelocity !== 0 || cameraHeight > 0) {
    verticalVelocity -= 5.7 * dt;
    cameraHeight += verticalVelocity * dt;

    if (cameraHeight <= 0) {
      cameraHeight = 0;
      verticalVelocity = 0;
    }
  }

  const bobX = moving ? Math.sin(bobTime) * 7 : 0;
  const bobY = moving ? Math.abs(Math.cos(bobTime)) * 6 : 0;
  const recoilY = recoil * 16;

  ui.weapon.style.transform =
    `translate(${bobX}px, ${bobY + recoilY}px) rotate(${recoil * 1.2}deg)`;
}

function updateEnemies(dt) {
  let alive = 0;

  for (const enemy of enemies) {
    if (enemy.dead) continue;

    alive++;
    enemy.hurtTimer = Math.max(0, enemy.hurtTimer - dt);
    enemy.attackTimer -= dt;
    enemy.phase += dt * 5;

    const dx = player.x - enemy.x;
    const dy = player.y - enemy.y;
    const distance = Math.hypot(dx, dy);
    const seesPlayer = distance < 13 &&
      hasLineOfSight(enemy.x, enemy.y, player.x, player.y);

    if (distance > 0.78 && seesPlayer) {
      const invDistance = 1 / Math.max(distance, 0.001);
      let moveX = dx * invDistance * enemy.speed * dt;
      let moveY = dy * invDistance * enemy.speed * dt;

      if (!canMove(enemy.x + moveX, enemy.y, enemy.radius)) {
        moveX = 0;
      }

      if (!canMove(enemy.x, enemy.y + moveY, enemy.radius)) {
        moveY = 0;
      }

      enemy.x += moveX;
      enemy.y += moveY;
    }

    if (distance <= 0.95 && enemy.attackTimer <= 0) {
      enemy.attackTimer = Math.max(0.5, 1.15 - wave * 0.02);
      damagePlayer(enemy.damage);
    }
  }

  if (alive === 0 && waveDelay <= 0) {
    waveDelay = 2.4;
    score += 250 * wave;
    reserve = Math.min(300, reserve + 30);
    showMessage(`WAVE ${wave} CLEARED`, 1.7);
    updateHUD();
  }
}

function updateParticles(dt) {
  for (let i = particles.length - 1; i >= 0; i--) {
    const particle = particles[i];

    particle.life -= dt;
    particle.x += particle.vx * dt;
    particle.y += particle.vy * dt;
    particle.z += particle.vz * dt;
    particle.vz -= 3.8 * dt;

    if (particle.life <= 0 || particle.z < 0) {
      particles.splice(i, 1);
    }
  }
}

function update(dt) {
  fireCooldown = Math.max(0, fireCooldown - dt);
  recoil = Math.max(0, recoil - dt * 8.5);

  if (reloading) {
    reloadTimer -= dt;
    if (reloadTimer <= 0) completeReload();
  }

  if (waveDelay > 0) {
    waveDelay -= dt;

    if (waveDelay <= 0) {
      wave++;
      spawnWave();
    }
  }

  updatePlayer(dt);
  updateEnemies(dt);
  updateParticles(dt);

  messageTimer -= dt;
  hitTimer -= dt;
  damageTimer -= dt;
  muzzleTimer -= dt;

  if (messageTimer <= 0) ui.message.classList.remove("visible");
  ui.hitMarker.classList.toggle("visible", hitTimer > 0);
  ui.damageFlash.style.opacity = damageTimer > 0 ? "1" : "0";
  ui.muzzleFlash.style.opacity = muzzleTimer > 0 ? "1" : "0";
}

function drawBackground() {
  const jumpOffset = cameraHeight * screenH * 0.18;
  const horizon = screenH * 0.5 + jumpOffset;

  const sky = ctx.createLinearGradient(0, 0, 0, horizon);
  sky.addColorStop(0, "#030912");
  sky.addColorStop(0.55, "#0b2333");
  sky.addColorStop(1, "#174554");

  ctx.fillStyle = sky;
  ctx.fillRect(0, 0, screenW, horizon);

  const floor = ctx.createLinearGradient(0, horizon, 0, screenH);
  floor.addColorStop(0, "#172329");
  floor.addColorStop(1, "#030608");

  ctx.fillStyle = floor;
  ctx.fillRect(0, horizon, screenW, screenH - horizon);

  ctx.strokeStyle = "rgba(35, 118, 132, 0.15)";
  ctx.lineWidth = 1;

  for (let i = 1; i < 12; i++) {
    const t = i / 12;
    const y = horizon + Math.pow(t, 1.9) * (screenH - horizon);
    ctx.beginPath();
    ctx.moveTo(0, y);
    ctx.lineTo(screenW, y);
    ctx.stroke();
  }
}

function wallColor(tile, shade, side) {
  const multiplier = Math.max(0.18, shade * (side ? 0.72 : 1));

  if (tile === "2") {
    return `rgb(${Math.floor(39 * multiplier)}, ${Math.floor(170 * multiplier)}, ${Math.floor(185 * multiplier)})`;
  }

  if (tile === "3") {
    return `rgb(${Math.floor(173 * multiplier)}, ${Math.floor(65 * multiplier)}, ${Math.floor(105 * multiplier)})`;
  }

  return `rgb(${Math.floor(92 * multiplier)}, ${Math.floor(122 * multiplier)}, ${Math.floor(137 * multiplier)})`;
}

function drawWalls() {
  const horizon = screenH * 0.5 + cameraHeight * screenH * 0.18;
  const startAngle = player.angle - HALF_FOV;

  for (let i = 0; i < rayCount; i++) {
    const rayAngle = startAngle + (i / rayCount) * FOV;
    const hit = castRay(player.x, player.y, rayAngle);
    const correctedDistance = Math.max(
      0.05,
      hit.distance * Math.cos(rayAngle - player.angle)
    );

    depthBuffer[i] = correctedDistance;

    const wallHeight = Math.min(
      screenH * 3,
      projectionPlane / correctedDistance
    );

    const top = horizon - wallHeight * 0.5;
    const distanceShade = 1 - Math.min(correctedDistance / MAX_DEPTH, 0.88);
    const stripe = (Math.floor(hit.wallOffset * 10) % 2) * 0.08;

    ctx.fillStyle = wallColor(
      hit.tile,
      distanceShade - stripe,
      hit.side
    );

    ctx.fillRect(
      Math.floor(i * columnWidth),
      Math.floor(top),
      Math.ceil(columnWidth + 1),
      Math.ceil(wallHeight)
    );

    if (hit.tile === "2" && hit.wallOffset > 0.46 && hit.wallOffset < 0.54) {
      ctx.fillStyle = `rgba(69, 242, 255, ${distanceShade * 0.8})`;
      ctx.fillRect(
        Math.floor(i * columnWidth),
        Math.floor(top),
        Math.ceil(columnWidth + 1),
        Math.max(1, Math.ceil(wallHeight))
      );
    }
  }
}

function projectEntity(x, y, z = 0.5) {
  const dx = x - player.x;
  const dy = y - player.y;
  const distance = Math.hypot(dx, dy);
  const relativeAngle = normalizeAngle(Math.atan2(dy, dx) - player.angle);

  if (Math.abs(relativeAngle) > HALF_FOV + 0.35) return null;

  const correctedDistance = distance * Math.cos(relativeAngle);
  if (correctedDistance <= 0.05) return null;

  return {
    distance,
    correctedDistance,
    relativeAngle,
    x: screenW * 0.5 + Math.tan(relativeAngle) * projectionPlane,
    y: screenH * 0.5 +
      cameraHeight * screenH * 0.18 -
      (z - 0.5) * projectionPlane / correctedDistance,
    scale: projectionPlane / correctedDistance
  };
}

function drawEnemy(enemy, projection) {
  const width = projection.scale * 0.52;
  const height = projection.scale * 1.08;
  const left = projection.x - width * 0.5;
  const top = projection.y - height * 0.53;
  const centerColumn = Math.floor(projection.x / columnWidth);

  if (
    centerColumn < 0 ||
    centerColumn >= rayCount ||
    projection.correctedDistance > depthBuffer[centerColumn] + 0.25
  ) {
    return;
  }

  const distanceAlpha = Math.max(0.25, 1 - projection.distance / 24);
  const hurt = enemy.hurtTimer > 0;
  const bodyColor = hurt ? "#ffffff" : "#9d253d";
  const darkColor = hurt ? "#ffc8c8" : "#38111d";
  const glowColor = hurt ? "#ffffff" : "#ff385f";
  const bob = Math.sin(enemy.phase) * height * 0.018;

  ctx.save();
  ctx.globalAlpha = distanceAlpha;

  ctx.shadowBlur = Math.min(25, width * 0.2);
  ctx.shadowColor = glowColor;

  ctx.fillStyle = darkColor;
  ctx.fillRect(
    left + width * 0.19,
    top + height * 0.43 + bob,
    width * 0.62,
    height * 0.45
  );

  ctx.fillStyle = bodyColor;
  ctx.fillRect(
    left + width * 0.26,
    top + height * 0.29 + bob,
    width * 0.48,
    height * 0.44
  );

  ctx.fillStyle = "#6e1729";
  ctx.fillRect(
    left + width * 0.13,
    top + height * 0.36 + bob,
    width * 0.16,
    height * 0.38
  );
  ctx.fillRect(
    left + width * 0.71,
    top + height * 0.36 + bob,
    width * 0.16,
    height * 0.38
  );

  ctx.fillStyle = "#171b22";
  ctx.fillRect(
    left + width * 0.28,
    top + height * 0.71 + bob,
    width * 0.18,
    height * 0.29
  );
  ctx.fillRect(
    left + width * 0.54,
    top + height * 0.71 + bob,
    width * 0.18,
    height * 0.29
  );

  ctx.beginPath();
  ctx.arc(
    projection.x,
    top + height * 0.19 + bob,
    width * 0.2,
    0,
    TAU
  );
  ctx.fillStyle = hurt ? "#fff" : "#5c1726";
  ctx.fill();

  ctx.shadowBlur = Math.min(18, width * 0.3);
  ctx.fillStyle = "#ffd166";
  ctx.fillRect(
    projection.x - width * 0.11,
    top + height * 0.16 + bob,
    width * 0.07,
    Math.max(2, height * 0.035)
  );
  ctx.fillRect(
    projection.x + width * 0.04,
    top + height * 0.16 + bob,
    width * 0.07,
    Math.max(2, height * 0.035)
  );

  if (projection.distance < 9) {
    const barWidth = width * 0.8;
    const healthRatio = Math.max(0, enemy.health / enemy.maxHealth);

    ctx.shadowBlur = 0;
    ctx.fillStyle = "rgba(0, 0, 0, 0.7)";
    ctx.fillRect(
      projection.x - barWidth * 0.5,
      top - height * 0.09,
      barWidth,
      Math.max(3, height * 0.025)
    );

    ctx.fillStyle = healthRatio > 0.45 ? "#ff385f" : "#ffd166";
    ctx.fillRect(
      projection.x - barWidth * 0.5,
      top - height * 0.09,
      barWidth * healthRatio,
      Math.max(3, height * 0.025)
    );
  }

  ctx.restore();
}

function drawEnemies() {
  const visible = [];

  for (const enemy of enemies) {
    if (enemy.dead) continue;

    const projection = projectEntity(enemy.x, enemy.y, 0.52);
    if (projection) visible.push({ enemy, projection });
  }

  visible.sort(
    (a, b) => b.projection.distance - a.projection.distance
  );

  for (const item of visible) {
    drawEnemy(item.enemy, item.projection);
  }
}

function drawParticles() {
  for (const particle of particles) {
    const projection = projectEntity(
      particle.x,
      particle.y,
      particle.z
    );

    if (!projection) continue;

    const column = Math.floor(projection.x / columnWidth);

    if (
      column < 0 ||
      column >= rayCount ||
      projection.correctedDistance > depthBuffer[column] + 0.15
    ) {
      continue;
    }

    const size = Math.max(
      1,
      particle.size * projection.scale * 0.025
    );

    ctx.globalAlpha = Math.min(1, particle.life * 3);
    ctx.fillStyle = particle.color;
    ctx.fillRect(
      projection.x - size * 0.5,
      projection.y - size * 0.5,
      size,
      size
    );
  }

  ctx.globalAlpha = 1;
}

function render() {
  drawBackground();
  drawWalls();
  drawEnemies();
  drawParticles();

  const vignette = ctx.createRadialGradient(
    screenW * 0.5,
    screenH * 0.5,
    screenH * 0.18,
    screenW * 0.5,
    screenH * 0.5,
    screenW * 0.72
  );

  vignette.addColorStop(0, "rgba(0,0,0,0)");
  vignette.addColorStop(1, "rgba(0,0,0,0.62)");

  ctx.fillStyle = vignette;
  ctx.fillRect(0, 0, screenW, screenH);
}

function gameLoop(time) {
  const dt = Math.min((time - previousTime) / 1000, 0.05);
  previousTime = time;

  if (state === "playing") {
    update(dt);
    render();
  } else if (state === "paused" || state === "gameover") {
    render();
  }

  animationFrame = requestAnimationFrame(gameLoop);
}

window.addEventListener("resize", resize);

ui.quality.addEventListener("change", resize);
ui.start.addEventListener("click", () => startGame(true));
ui.resume.addEventListener("click", () => startGame(false));
ui.restart.addEventListener("click", () => startGame(true));

document.addEventListener("keydown", event => {
  keys[event.code] = true;

  if (event.code === "KeyR") reload();

  if (
    event.code === "Space" &&
    state === "playing" &&
    cameraHeight === 0
  ) {
    verticalVelocity = 2.15;
  }

  if (event.code === "Escape" && state === "playing") {
    pauseGame();
  }
});

document.addEventListener("keyup", event => {
  keys[event.code] = false;
});

document.addEventListener("mousemove", event => {
  if (state !== "playing" || document.pointerLockElement !== canvas) {
    return;
  }

  player.angle = normalizeAngle(
    player.angle + event.movementX * 0.00215
  );
});

document.addEventListener("mousedown", event => {
  if (
    event.button === 0 &&
    state === "playing" &&
    document.pointerLockElement === canvas
  ) {
    shoot();
  }
});

document.addEventListener("contextmenu", event => {
  event.preventDefault();
});

document.addEventListener("pointerlockchange", () => {
  if (
    document.pointerLockElement !== canvas &&
    state === "playing"
  ) {
    pauseGame();
  }
});

window.addEventListener("blur", () => {
  if (state === "playing") pauseGame();
});

if (!ctx || !("pointerLockElement" in document)) {
  ui.menu.classList.add("hidden");
  ui.unsupported.classList.remove("hidden");
} else {
  resize();
  render();
  cancelAnimationFrame(animationFrame);
  animationFrame = requestAnimationFrame(gameLoop);
}
