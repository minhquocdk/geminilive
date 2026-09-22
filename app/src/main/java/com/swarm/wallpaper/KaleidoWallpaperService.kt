package com.swarm.wallpaper

import android.content.Context
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Paint
import android.graphics.Path
import android.graphics.RectF
import android.graphics.Typeface
import android.os.Handler
import android.os.Looper
import android.os.PowerManager
import android.os.SystemClock
import android.service.wallpaper.WallpaperService
import android.view.MotionEvent
import android.view.SurfaceHolder
import kotlin.math.PI
import kotlin.math.abs
import kotlin.math.acos
import kotlin.math.cos
import kotlin.math.exp
import kotlin.math.hypot
import kotlin.math.ln
import kotlin.math.max
import kotlin.math.min
import kotlin.math.pow
import kotlin.math.roundToInt
import kotlin.math.sin
import kotlin.math.sqrt
import kotlin.random.Random

// ───────────────────────── CẤU HÌNH (chỉnh ở đây) ─────────────────────────
private const val A_FPS = 60                 // fps bình thường
private const val A_FPS_SAVER = 15           // fps khi bật Tiết kiệm pin
private const val A_COLS = 48                // lưới rạn san hô
private const val A_ROWS = 48
private const val A_CELL = 11f               // kích thước 1 ô (đơn vị thế giới)
private const val A_LIFE_INTERVAL = 110L     // ms mỗi bước Conway
private const val A_MAX_AGE = 24
private const val A_TRAIL_FADE = 0.92f
private const val A_MIC_HUE = 168f           // màu gốc của pet
private const val A_DAY_LENGTH_MS = 150_000L // 1 vòng ngày/đêm
private const val A_DECISION_INTERVAL_MS = 400L
private const val A_NEEDS_TICK_MS = 1000L
private const val A_MAX_FOOD = 16
private const val A_FOOD_TTL = 12_000L
private const val A_CURVE_DRAW_MS = 5_000L
private const val A_GALLERY_MAX = 4
private const val A_ACTIVE_CURVE_MAX = 3
private const val A_POST_MEAL_PLAY_MS = 3_000L
private const val A_PET_BASE_SPEED = 0.35f
private const val A_MAX_WAVES = 4            // cùng bố cục GeminiWallpaperService
private const val A_WAVE_SPEED = 650f
private const val A_WAVE_MAX = 1_200f
private const val A_AUTO_WAVE_MS = 0L        // 0 = tắt, chỉ chạm mới đổi màu

private val LINE_COLORS = floatArrayOf(
    A_MIC_HUE, 220f, 48f, 300f, 120f, 20f
)

private val CURVE_TYPES = arrayOf(
    "rose", "butterfly", "lissajous", "heart", "spiral",
    "lorenz", "planet", "burst", "sun", "moon", "star", "cloud"
)
private val TIER_XP = intArrayOf(2, 5, 10, 18, 30, 60)
private val TIER_EMOTE = arrayOf("💧", "😕", "🙂", "😄", "✨", "🌟")

// ───────────────────────── SÓNG NỔI (tương tự GWave) ─────────────────────────
private class AWave(var radius: Float, val state: Int)

// ───────────────────────── MODEL ─────────────────────────
private class AFood(val x: Float, val y: Float, val born: Long, var hue: Float)

private class ATrail(
    val x: Float, val y: Float, val age: Int,
    var life: Float, val rainbow: Boolean, val hue: Float
)

private class ASparkle(val x: Float, val y: Float, var life: Float, val hue: Float)

private class ABubble(var x: Float, var y: Float, val r: Float, var life: Float)

private class ACurve(
    val type: String,
    val cx: Float, val cy: Float,
    val cxGrid: Float, val cyGrid: Float,
    val size: Float, val hue: Float,
    var startTime: Long, var durationMs: Long,
    val points: List<FloatArray?>,       // null = nhấc bút
    var drawnUpTo: Int = 0,
    var completed: Boolean = false,
    var tier: Int = 2,
    var golden: Boolean = false
) {
    var pausedForEat = false
    var pausedAt = 0L
    var savedProgress = 0f
}

private class APersonality(
    val curiosity: Float,
    val bravery: Float,
    val greed: Float,
    val social: Float
)

private class APet(val seed: String, val p: APersonality) {
    var x = 2f
    var y = A_ROWS / 2f
    var renderX = 2f
    var renderY = A_ROWS / 2f
    var hunger = 25f
    var energy = 88f
    var mood = 72f
    var state = "EXPLORE"
    var level = 1
    var xp = 0
    var fed = 0
    var lastReefTouch = 0L
    var lastPetAt = 0L
    var playUntil = 0L
    var justAte = false
    var resumeCurve = false
    var nextDecision = 0L
    var needsAcc = 0f
    var drawing = false
    var drawingCurve: ACurve? = null
    var strolling = false
    var strollTargetX = 0f
    var strollTargetY = 0f
    var strollUntil = 0L
    var strollNextAt = 0L
    var autoTargetX = 0f
    var autoTargetY = 0f
    var autoUntil = 0L
    var swimDistance = 0f

    fun levelFromXp(): Int = 1 + sqrt(max(0f, xp) / 45f).toInt()
}

// ───────────────────────── WALLPAPER SERVICE ─────────────────────────
class KaleidoWallpaperService : WallpaperService() {

    override fun onCreateEngine(): Engine = AquaEngine()

    private inner class AquaEngine : Engine() {
        private val handler = Handler(Looper.getMainLooper())
        private val pm = getSystemService(Context.POWER_SERVICE) as PowerManager

        private var shown = false
        private var surfaceReady = false
        private var w = 0
        private var h = 0
        private var dpr = 1f

        private val rnd = Random(SystemClock.uptimeMillis())

        // paint tái sử dụng
        private val fill = Paint(Paint.ANTI_ALIAS_FLAG)
        private val stroke = Paint(Paint.ANTI_ALIAS_FLAG).apply { style = Paint.Style.STROKE }
        private val textPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply {
            typeface = Typeface.MONOSPACE
            textSize = 26f
        }
        private val path = Path()
        private val rectF = RectF()

        // lưới Conway
        private lateinit var grid: Array<IntArray>
        private lateinit var nextGrid: Array<IntArray>
        private lateinit var age: Array<IntArray>
        private lateinit var nextAge: Array<IntArray>
        private var generation = 0
        private var lastLifeUpdate = 0L

        // thực thể
        private val trails = ArrayList<ATrail>(2600)
        private val food = ArrayList<AFood>(A_MAX_FOOD)
        private val sparkles = ArrayList<ASparkle>(128)
        private val bubbles = ArrayList<ABubble>(64)
        private val activeCurves = ArrayList<ACurve>(A_ACTIVE_CURVE_MAX)
        private val gallery = ArrayList<ACurve>(A_GALLERY_MAX)
        private val waves = ArrayList<AWave>(A_MAX_WAVES)
        private var colorWave: AWave? = null

        // thời gian
        private var startAt = 0L
        private var lastT = 0L
        private var animTime = 0f
        private var mathTime = 0f
        private var rotX = 0.55f
        private var rotY = 0f

        // pet
        private val petSeed = (1..999_999).random(rnd).toString(36).uppercase()
        private val personality = derivePersonality(petSeed)
        private val nestX = 5f + (hash32(petSeed) % (A_COLS - 10))
        private val nestY = 5f + ((hash32(petSeed).ushr(11)) % (A_ROWS - 10))
        private val pet = APet(petSeed, personality)

        // dự phòng tọa độ
        private val scratch = FloatArray(2)

        private val loop = object : Runnable {
            override fun run() {
                val t0 = SystemClock.uptimeMillis()
                drawFrame(t0)
                if (shown) {
                    val fps = if (pm.isPowerSaveMode) A_FPS_SAVER else A_FPS
                    handler.postDelayed(this, max(1L, 1000L / fps - (SystemClock.uptimeMillis() - t0)))
                }
            }
        }

        // ── tính cách từ seed ──
        private fun hash32(str: String): Int {
            var h = -2128831035  // 0x811c9dc5 as signed
            for (c in str) {
                h = h xor c.code
                h *= 16777619
            }
            return h
        }

        private fun derivePersonality(seed: String): APersonality {
            val n = hash32(seed)
            fun t(v: Int): Float = ((v and 0xFF).toFloat() / 255f)
            return APersonality(
                curiosity = t(n),
                bravery = t(n ushr 8),
                greed = t(n ushr 16),
                social = t(n ushr 24)
            )
        }

        init {
            resetGrid()
            pet.strollNextAt = 8_000L + (rnd.nextFloat() * 14_000L).toLong()
        }

        // ── lưới ──
        private fun resetGrid() {
            grid = Array(A_COLS) { IntArray(A_ROWS) { if (rnd.nextFloat() < 0.24f) 1 else 0 } }
            age = Array(A_COLS) { IntArray(A_ROWS) }
            nextGrid = Array(A_COLS) { IntArray(A_ROWS) }
            nextAge = Array(A_COLS) { IntArray(A_ROWS) }
            trails.clear()
            generation = 0
        }

        private fun updateGameOfLife() {
            for (x in 0 until A_COLS) {
                nextGrid[x].fill(0)
                nextAge[x].fill(0)
            }
            for (x in 0 until A_COLS) {
                for (y in 0 until A_ROWS) {
                    var n = 0
                    for (dx in -1..1) for (dy in -1..1) {
                        if (dx == 0 && dy == 0) continue
                        n += grid[(x + dx + A_COLS) % A_COLS][(y + dy + A_ROWS) % A_ROWS]
                    }
                    val alive = grid[x][y] == 1
                    val survives = alive && (n == 2 || n == 3)
                    val born = !alive && n == 3
                    if (survives || born) {
                        nextGrid[x][y] = 1
                        nextAge[x][y] = if (alive) min(A_MAX_AGE, age[x][y] + 1) else 1
                    } else if (alive) {
                        if (trails.size < 2600) trails.add(ATrail(x.toFloat(), y.toFloat(), age[x][y], 1f, false, 0f))
                    }
                }
            }
            val tg = grid; grid = nextGrid; nextGrid = tg
            val ta = age; age = nextAge; nextAge = ta
            generation++
        }

        // ── vòng đời Engine ──
        override fun onCreate(surfaceHolder: SurfaceHolder) {
            super.onCreate(surfaceHolder)
            setTouchEventsEnabled(true)
        }

        override fun onSurfaceCreated(holder: SurfaceHolder) {
            super.onSurfaceCreated(holder)
            surfaceReady = true
        }

        override fun onSurfaceChanged(holder: SurfaceHolder, format: Int, width: Int, height: Int) {
            super.onSurfaceChanged(holder, format, width, height)
            w = width
            h = height
            dpr = resources.displayMetrics.density
            textPaint.textSize = 12f * dpr
        }

        override fun onVisibilityChanged(visible: Boolean) {
            shown = visible
            handler.removeCallbacks(loop)
            if (visible) {
                val now = SystemClock.uptimeMillis()
                startAt = now
                lastT = now
                lastLifeUpdate = now
                handler.post(loop)
            }
        }

        override fun onSurfaceDestroyed(holder: SurfaceHolder) {
            shown = false
            surfaceReady = false
            handler.removeCallbacks(loop)
            super.onSurfaceDestroyed(holder)
        }

        override fun onDestroy() {
            shown = false
            handler.removeCallbacks(loop)
            super.onDestroy()
        }

        override fun onTouchEvent(event: MotionEvent) {
            if (event.actionMasked == MotionEvent.ACTION_DOWN) {
                onTap(event.x, event.y, SystemClock.uptimeMillis())
            }
            super.onTouchEvent(event)
        }

        override fun onCommand(
            action: String?, x: Int, y: Int, z: Int, extras: android.os.Bundle?, resultRequested: Boolean
        ): android.os.Bundle? {
            if (action == android.app.WallpaperManager.COMMAND_TAP) {
                onTap(w * 0.5f, h * 0.5f, SystemClock.uptimeMillis())
            }
            return super.onCommand(action, x, y, z, extras, resultRequested)
        }

        // ── chạm: nếu gần pet thì cưng, ngược lại thả đồ ăn ──
        private fun onTap(px: Float, py: Float, now: Long) {
            project3D((pet.renderX - A_COLS / 2f) * A_CELL, (pet.renderY - A_ROWS / 2f) * A_CELL, 22f, scratch)
            val hitR = max(26f * dpr, 7.5f * scratch[2] * 2.2f)
            val dx = scratch[0] - px
            val dy = scratch[1] - py
            if (hypot(dx, dy) <= hitR) {
                if (now - pet.lastPetAt > 500) {
                    pet.lastPetAt = now
                    pet.mood = min(100f, pet.mood + 4f)
                    pet.xp += 2
                    refreshLevel()
                    emitSparkles(pet.x, pet.y, 6, A_MIC_HUE)
                }
                return
            }
            val g = screenToGrid(px, py)
            if (food.size < A_MAX_FOOD) {
                food.add(AFood(g[0], g[1], now, (rnd.nextFloat() * 360f)))
                pet.mood = min(100f, pet.mood + 3f)
            }
            triggerWave(now)
        }

        private fun triggerWave(now: Long) {
            colorWave = AWave(0f, (colorWave?.state ?: 0) + 1)
            waves.add(colorWave!!)
            while (waves.size > A_MAX_WAVES) waves.removeAt(0)
            if (colorWave!!.state > 5) colorWave!!.state = 1
        }

        // ── tiện ích toạ độ ──
        private fun project3D(x0: Float, y0: Float, z0: Float, out: FloatArray) {
            val scene = max(A_COLS, A_ROWS) * A_CELL
            val fillX = 0.94f
            val fillY = fillX / 1.618f + 0.30f
            val rsx = max(0.45f, min(2.6f, (w * fillX) / scene))
            val rsy = max(0.45f, min(2.6f, (h * fillY) / scene))
            val rsZ = (rsx + rsy) / 2f
            val x = x0 * rsx
            val y = y0 * rsy
            val z = z0 * rsZ
            val cy = cos(rotY); val sy = sin(rotY)
            val cx = cos(rotX); val sx = sin(rotX)
            val x1 = x * cy + z * sy
            val z1 = -x * sy + z * cy
            val y2 = y * cx - z1 * sx
            val z2 = y * sx + z1 * cx
            val fov = 760f / (760f + z2 + 360f)
            out[0] = w / 2f + x1 * fov
            out[1] = h / 2f + y2 * fov
            out[2] = fov
        }

        private fun screenToGrid(px: Float, py: Float): FloatArray {
            var bestX = 0f; var bestY = 0f; var bestD = Float.MAX_VALUE
            val tmp = FloatArray(2)
            for (x in 0 until A_COLS) for (y in 0 until A_ROWS) {
                project3D((x - A_COLS / 2f) * A_CELL, (y - A_ROWS / 2f) * A_CELL, 0f, tmp)
                val dx = tmp[0] - px; val dy = tmp[1] - py
                val d = dx * dx + dy * dy
                if (d < bestD) { bestD = d; bestX = x.toFloat(); bestY = y.toFloat() }
            }
            return floatArrayOf(bestX, bestY)
        }

        // ── day/night ──
        private fun dayPhase(t: Long): Float = ((t.toFloat() / A_DAY_LENGTH_MS) % 1f + 1f) % 1f
        private fun nightFactor(t: Long): Float = 0.5f - 0.5f * cos((dayPhase(t) - 0.25f) * 2f * PI.toFloat())
        private fun isGoldenHour(t: Long): Boolean = abs(dayPhase(t) - 0.25f) < 0.06f

        // ── pet needs / brain ──
        private fun tickNeeds(dtScale: Float) {
            if (dtScale <= 0f) return
            pet.needsAcc += dtScale * 16.7f
            if (pet.needsAcc < A_NEEDS_TICK_MS) return
            val sec = (pet.needsAcc / A_NEEDS_TICK_MS).toInt()
            pet.needsAcc -= sec * A_NEEDS_TICK_MS
            if (pet.state == "SLEEPING") {
                pet.energy = min(100f, pet.energy + 3.0f * sec)
                return
            }
            pet.hunger = min(100f, pet.hunger + 0.72f * sec)
            pet.energy = max(0f, pet.energy - 0.24f * sec)
            val now = SystemClock.uptimeMillis()
            if (now < pet.playUntil) pet.energy = max(0f, pet.energy - 0.48f * sec)
            pet.mood = max(0f, pet.mood - 0.04f * sec)
        }

        private fun pickState(now: Long): String {
            val night = nightFactor(now)
            if (pet.state == "SLEEPING") return if (pet.energy >= 70f) "EXPLORE" else "SLEEPING"
            if (pet.energy < 14f + (1f - personality.bravery) * 6f + night * 12f) return "SLEEPING"
            if (food.isNotEmpty() && pet.hunger > 55f) return "HUNTING"
            return "EXPLORE"
        }

        private fun think(dtScale: Float, now: Long) {
            if (now < pet.nextDecision) return
            pet.nextDecision = now + A_DECISION_INTERVAL_MS
            val next = pickState(now)
            if (pet.state != next) pet.state = next
        }

        private fun updatePet(dtScale: Float, now: Long) {
            tickNeeds(dtScale)

            val dc = pet.drawingCurve
            if (pet.drawing && dc != null && !dc.completed) {
                if (!dc.pausedForEat && food.isNotEmpty() && pet.hunger > 55f) {
                    dc.pausedForEat = true
                    dc.pausedAt = now
                    dc.savedProgress = min(1f, (now - dc.startTime).toFloat() / dc.durationMs.toFloat())
                    pet.drawing = false
                    pet.state = "HUNTING"
                    return
                }
                val ang = now * 0.001f
                val r = dc.size / A_CELL * 0.25f
                pet.x = dc.cxGrid + cos(ang) * r
                pet.y = dc.cyGrid + sin(ang) * r
                return
            }

            // mục tiêu mong muốn
            var desiredX = pet.x
            var desiredY = pet.y

            when {
                pet.state == "SLEEPING" -> { desiredX = nestX; desiredY = nestY }
                pet.state == "HUNTING" && food.isNotEmpty() -> {
                    var best: AFood? = null
                    var bestD = Float.MAX_VALUE
                    for (f in food) {
                        val d = hypot(f.x - pet.x, f.y - pet.y)
                        if (d < bestD) { bestD = d; best = f }
                    }
                    if (best != null) { desiredX = best.x; desiredY = best.y }
                }
                else -> {
                    if (pet.strolling) {
                        if (now >= pet.strollUntil) {
                            pet.strolling = false
                            pet.strollNextAt = now + (12_000 + rnd.nextFloat() * 14_000).toLong() - (pet.mood * 60).toLong()
                        } else {
                            desiredX = pet.strollTargetX
                            desiredY = pet.strollTargetY
                        }
                    } else if (now >= pet.strollNextAt) {
                        pet.strolling = true
                        pet.strollUntil = now + (4_000 + rnd.nextFloat() * 4_000).toLong()
                        pet.strollTargetX = 2f + rnd.nextFloat() * (A_COLS - 5)
                        pet.strollTargetY = 2f + rnd.nextFloat() * (A_ROWS - 5)
                        desiredX = pet.strollTargetX
                        desiredY = pet.strollTargetY
                    }
                    if (!pet.strolling) {
                        val tgtDone = hypot(pet.autoTargetX - pet.x, pet.autoTargetY - pet.y) < 2f
                        if (tgtDone || now >= pet.autoUntil || (pet.autoTargetX == 0f && pet.autoTargetY == 0f)) {
                            val k = 5f
                            val rr = 17f * cos(k * mathTime * 0.7f)
                            pet.autoTargetX = (A_COLS / 2f + rr * cos(mathTime * 0.7f)).coerceIn(0f, (A_COLS - 1).toFloat())
                            pet.autoTargetY = (A_ROWS / 2f + rr * sin(mathTime * 0.7f)).coerceIn(0f, (A_ROWS - 1).toFloat())
                            pet.autoUntil = now + (2_500 + rnd.nextFloat() * 3_000).toLong()
                        }
                        desiredX = pet.autoTargetX
                        desiredY = pet.autoTargetY
                    }
                }
            }

            // post-meal play
            if (now < pet.playUntil && !pet.drawing && pet.state != "SLEEPING" && pet.state != "HUNTING") {
                val playA = now * 0.007f
                val hopR = 3.2f + sin(playA * 1.7f) * 1.6f
                desiredX = (pet.x + cos(playA * 2.1f) * hopR).coerceIn(0f, (A_COLS - 1).toFloat())
                desiredY = (pet.y + sin(playA * 3.3f) * hopR * 0.7f).coerceIn(0f, (A_ROWS - 1).toFloat())
                if (rnd.nextFloat() < 0.07f) {
                    sparkles.add(ASparkle(pet.x, pet.y, 0.9f, 48f))
                }
            }

            val speedF = (0.6f + personality.greed * 0.4f) *
                (0.5f + pet.energy / 200f) *
                (1f - pet.hunger / 300f) *
                (if (pet.state == "HUNTING") 1.35f else 1f)
            val prevX = pet.x; val prevY = pet.y
            val dx = desiredX - pet.x
            val dy = desiredY - pet.y
            val d = hypot(dx, dy)
            if (d > 0.01f) {
                val step = min(d, A_PET_BASE_SPEED * speedF * dtScale)
                pet.x += dx / d * step
                pet.y += dy / d * step
            }

            // rainbow trail
            pet.swimDistance += hypot(pet.x - prevX, pet.y - prevY)
            if (pet.swimDistance > 0.3f) {
                if (trails.size < 2600) {
                    trails.add(ATrail(
                        pet.x, pet.y, 0, 1f, true,
                        (now * 0.2f + generation * 9f + pet.x * 7f) % 360f
                    ))
                }
                pet.swimDistance = 0f
            }

            // chạm rạn san hô
            if (pet.state != "SLEEPING" && now - pet.lastReefTouch > 420) {
                pet.lastReefTouch = now
                val gx = pet.x.roundToInt().coerceIn(0, A_COLS - 1)
                val gy = pet.y.roundToInt().coerceIn(0, A_ROWS - 1)
                if (rnd.nextFloat() < 0.28f + personality.curiosity * 0.22f) {
                    grid[gx][gy] = 1
                    age[gx][gy] = max(1, age[gx][gy])
                    pet.mood = min(100f, pet.mood + 1f)
                    pet.xp += 2
                    sparkles.add(ASparkle(gx.toFloat(), gy.toFloat(), 1f, A_MIC_HUE))
                }
            }

            // ăn
            var idx = -1
            for (i in food.indices) {
                if (hypot(food[i].x - pet.x, food[i].y - pet.y) < 1.2f) { idx = i; break }
            }
            if (idx >= 0) {
                food.removeAt(idx)
                pet.hunger = max(0f, pet.hunger - 32f)
                pet.energy = min(100f, pet.energy + 12f)
                pet.mood = min(100f, pet.mood + 8f)
                pet.fed += 1
                pet.xp += 10
                refreshLevel()
                pet.justAte = true
                pet.resumeCurve = true
                pet.playUntil = now + A_POST_MEAL_PLAY_MS
            }
        }

        private fun refreshLevel() {
            val before = pet.level
            pet.level = pet.levelFromXp()
            if (pet.level > before) {
                for (i in 0 until 24) {
                    val ang = i / 24f * 2f * PI.toFloat()
                    val d = 1.5f + rnd.nextFloat() * 3.5f
                    sparkles.add(ASparkle(
                        (pet.x + cos(ang) * d).coerceIn(0f, (A_COLS - 1).toFloat()),
                        (pet.y + sin(ang) * d).coerceIn(0f, (A_ROWS - 1).toFloat()),
                        1f, (i * 15f + A_MIC_HUE) % 360f
                    ))
                }
                triggerWave(SystemClock.uptimeMillis())
            }
        }

        private fun emitSparkles(x: Float, y: Float, n: Int, hue: Float) {
            for (i in 0 until n) {
                sparkles.add(ASparkle(
                    (x + rnd.nextFloat() * 3f - 1.5f).coerceIn(0f, (A_COLS - 1).toFloat()),
                    (y + rnd.nextFloat() * 3f - 1.5f).coerceIn(0f, (A_ROWS - 1).toFloat()),
                    1f, (hue + rnd.nextFloat() * 60f) % 360f
                ))
            }
        }

        // ── hệ hoạ tiết đường cong (giống bản HTML) ──
        private fun computeCurvePoints(type: String, cx: Float, cy: Float, size: Float): List<FloatArray?> {
            val pts = ArrayList<FloatArray?>(1200)
            when (type) {
                "rose" -> {
                    val k = 3 + rnd.nextInt(6)
                    for (i in 0..800) {
                        val th = i / 800f * 2f * PI.toFloat()
                        val r = size * 0.5f * sin(k * th)
                        pts.add(floatArrayOf(cx + r * cos(th), cy + r * sin(th)))
                    }
                }
                "butterfly" -> {
                    val tMax = Math.PI.toFloat() * 12f
                    for (i in 0..1200) {
                        val th = i / 1200f * tMax
                        val r = size * 0.18f * (exp(cos(th)) - 2f * cos(4f * th) +
                            sin(th / 12f).pow(5))
                        pts.add(floatArrayOf(cx + r * cos(th), cy + r * sin(th)))
                    }
                }
                "lissajous" -> {
                    val a = 2 + rnd.nextInt(4)
                    val b = 3 + rnd.nextInt(5)
                    for (i in 0..600) {
                        val t = i / 600f * 2f * PI.toFloat()
                        pts.add(floatArrayOf(cx + size * 0.5f * sin(a * t), cy + size * 0.5f * sin(b * t)))
                    }
                }
                "heart" -> {
                    val s = size * 0.028f
                    for (i in 0..480) {
                        val t = i / 480f * 2f * PI.toFloat()
                        val x = 16f * sin(t).pow(3)
                        val y = -(13f * cos(t) - 5f * cos(2f * t) - 2f * cos(3f * t) - cos(4f * t))
                        pts.add(floatArrayOf(cx + x * s, cy + y * s))
                    }
                }
                "spiral" -> {
                    val turns = 2.5f + rnd.nextFloat() * 1.5f
                    val b = ln(1.618f) / (2f * PI.toFloat())
                    val thetaMax = turns * 2f * PI.toFloat()
                    val rMax = size * 0.45f
                    val a = rMax / exp(b * thetaMax)
                    val n = max(600, (turns * 320).toInt())
                    for (i in 0..n) {
                        val th = i / n.toFloat() * thetaMax
                        val r = a * exp(b * th)
                        pts.add(floatArrayOf(cx + r * cos(th), cy + r * sin(th)))
                    }
                }
                "lorenz" -> {
                    val sigma = 10f; val rho = 28f; val beta = 8f / 3f
                    val dt = 0.004f; val n = 2600
                    val k = size * 0.45f / 30f
                    var x = 0.1f; var y = 0f; var z = 0f
                    for (i in 0..n) {
                        pts.add(floatArrayOf(cx + x * k, cy + (z - 25f) * k))
                        val dx = sigma * (y - x)
                        val dy = x * (rho - z) - y
                        val dz = x * y - beta * z
                        x += dx * dt; y += dy * dt; z += dz * dt
                    }
                }
                "planet" -> {
                    val r = size * 0.28f
                    for (i in 0..360) {
                        val a = i / 360f * 2f * PI.toFloat()
                        pts.add(floatArrayOf(cx + r * cos(a), cy + r * sin(a)))
                    }
                    pts.add(null)
                    for (i in 0..300) {
                        val a = i / 300f * 2f * PI.toFloat()
                        pts.add(floatArrayOf(cx + r * 1.7f * cos(a), cy + r * 0.5f * sin(a)))
                    }
                }
                "burst" -> {
                    val outer = size * 0.42f; val inner = outer * 0.3f
                    for (i in 0..480) {
                        val t = i / 480f * 16f
                        val seg = t.toInt() % 16
                        val frac = t - t.toInt()
                        val ang = -PI.toFloat() / 2f + (seg + frac) * PI.toFloat() / 8f
                        val rad = if (seg % 2 == 0) outer + (inner - outer) * frac
                        else inner + (outer - inner) * frac
                        pts.add(floatArrayOf(cx + rad * cos(ang), cy + rad * sin(ang)))
                    }
                }
                "sun" -> {
                    for (i in 0..720) {
                        val th = i / 720f * 2f * PI.toFloat()
                        val r = size * 0.5f * (0.72f + 0.28f * abs(cos(6f * th)).pow(3))
                        pts.add(floatArrayOf(cx + r * cos(th), cy + r * sin(th)))
                    }
                }
                "moon" -> {
                    val r = size * 0.5f; val dd = r * 0.5f; val r2 = r * 0.75f
                    val alpha = acos(((r * r + dd * dd - r2 * r2) / (2f * r * dd)).coerceIn(-1f, 1f))
                    val phi = acos(((r * r - dd * dd - r2 * r2) / (2f * dd * r2)).coerceIn(-1f, 1f))
                    for (i in 0..360) {
                        val a = alpha + i / 360f * (2f * PI.toFloat() - 2f * alpha)
                        pts.add(floatArrayOf(cx + r * cos(a), cy + r * sin(a)))
                    }
                    pts.add(null)
                    for (i in 0..220) {
                        val p = -phi - i / 220f * (2f * PI.toFloat() - 2f * phi)
                        pts.add(floatArrayOf(cx + dd + r2 * cos(p), cy + r2 * sin(p)))
                    }
                }
                "star" -> {
                    val outer = size * 0.36f; val inner = outer * 0.42f
                    for (i in 0..400) {
                        val t = i / 400f * 10f
                        val seg = t.toInt() % 10
                        val frac = t - t.toInt()
                        val ease = frac * frac * (3f - 2f * frac)
                        val ang = -PI.toFloat() / 2f + (seg + ease) * PI.toFloat() / 5f
                        val rad = if (seg % 2 == 0) outer + (inner - outer) * ease
                        else inner + (outer - inner) * ease
                        pts.add(floatArrayOf(cx + rad * cos(ang), cy + rad * sin(ang)))
                    }
                }
                "cloud" -> {
                    val r = size * 0.5f; val baseY = r * 0.32f
                    val bumps = arrayOf(
                        floatArrayOf(-r * 0.95f, r * 0.62f),
                        floatArrayOf(-r * 0.28f, r * 0.98f),
                        floatArrayOf(r * 0.42f, r * 0.8f),
                        floatArrayOf(r * 1.0f, r * 0.5f)
                    )
                    for (i in 0..180) {
                        val x = -r * 1.45f + i / 180f * r * 2.9f
                        var top = baseY
                        for (b in bumps) {
                            val dx = x - b[0]
                            if (dx > -b[1] && dx < b[1]) {
                                val y = baseY - sqrt(b[1] * b[1] - dx * dx)
                                if (y < top) top = y
                            }
                        }
                        pts.add(floatArrayOf(cx + x, cy + top))
                    }
                    for (i in 0..24) {
                        pts.add(floatArrayOf(cx + r * 1.45f - i / 24f * r * 2.9f, cy + baseY))
                    }
                }
            }
            return pts
        }

        private fun startCurveForPet(now: Long) {
            if (activeCurves.size >= A_ACTIVE_CURVE_MAX) return
            val type = CURVE_TYPES[rnd.nextInt(CURVE_TYPES.size)]
            val tmp = FloatArray(2)
            project3D((pet.x - A_COLS / 2f) * A_CELL, (pet.y - A_ROWS / 2f) * A_CELL, 22f, tmp)
            val size = 40f + rnd.nextFloat() * 40f * (1f + pet.level / 40f)
            val hue = (A_MIC_HUE + personality.curiosity * 80f) % 360f
            val points = computeCurvePoints(type, tmp[0], tmp[1], size)
            val ac = ACurve(
                type = type,
                cx = tmp[0], cy = tmp[1],
                cxGrid = pet.x, cyGrid = pet.y,
                size = size, hue = hue,
                startTime = now, durationMs = A_CURVE_DRAW_MS,
                points = points,
                golden = isGoldenHour(now)
            )
            activeCurves.add(ac)
            pet.drawingCurve = ac
            pet.drawing = true
        }

        private fun maybeStartCurveDrawing(now: Long) {
            val ac = pet.drawingCurve
            if (ac != null && ac.pausedForEat && !ac.completed) {
                val snackDone = pet.resumeCurve && (pet.hunger < 35f || food.isEmpty()) && now >= pet.playUntil
                val breakOver = now - ac.pausedAt > 12_000
                if ((snackDone || breakOver) && pet.state != "SLEEPING") {
                    ac.startTime = now - (ac.savedProgress * ac.durationMs).toLong()
                    ac.pausedForEat = false
                    pet.drawing = true
                    pet.resumeCurve = false
                    pet.justAte = false
                }
                return
            }
            if (pet.justAte && pet.state != "HUNTING" && pet.energy > 30f && now >= pet.playUntil) {
                pet.justAte = false
                startCurveForPet(now)
            }
        }

        // ── cập nhật hoạ tiết đang vẽ ──
        private fun updateActiveCurves(now: Long) {
            val it = activeCurves.iterator()
            while (it.hasNext()) {
                val ac = it.next()
                val elapsed = now - ac.startTime
                val progress = if (ac.pausedForEat) ac.savedProgress
                else min(1f, elapsed.toFloat() / ac.durationMs.toFloat())
                val target = (progress * ac.points.size).toInt()
                if (target > ac.drawnUpTo) ac.drawnUpTo = target
                if (progress >= 1f && !ac.completed) {
                    ac.completed = true
                    ac.tier = rollTier(ac.golden)
                    if (gallery.size >= A_GALLERY_MAX) gallery.removeAt(0)
                    gallery.add(ac)
                    for (i in 0 until 30) {
                        val ang = i / 30f * 2f * PI.toFloat()
                        val d = 2f + rnd.nextFloat() * 3f
                        sparkles.add(ASparkle(
                            (ac.cxGrid + cos(ang) * d).coerceIn(0f, (A_COLS - 1).toFloat()),
                            (ac.cyGrid + sin(ang) * d).coerceIn(0f, (A_ROWS - 1).toFloat()),
                            1f, (ac.hue + i * 12f) % 360f
                        ))
                    }
                    pet.xp += TIER_XP[ac.tier]
                    refreshLevel()
                    if (pet.drawingCurve === ac) {
                        pet.drawing = false
                        pet.drawingCurve = null
                    }
                    it.remove()
                }
            }
        }

        private fun rollTier(golden: Boolean): Int {
            var score = rnd.nextFloat()
            score += pet.mood / 200f + pet.level / 150f + pet.energy / 400f - pet.hunger / 300f
            if (golden) score += 0.12f
            return when {
                score < 0.25f -> 0
                score < 0.45f -> 1
                score < 0.62f -> 2
                score < 0.78f -> 3
                score < 0.95f -> 4
                else -> 5
            }
        }

        // ── loop vẽ ──
        private fun drawFrame(now: Long) {
            if (!surfaceReady || w == 0 || h == 0) return
            val holder = surfaceHolder
            var canvas: Canvas? = null
            try {
                canvas = holder.lockCanvas()
                if (canvas == null) return

                val dt = ((now - lastT) / 1000f).coerceIn(0f, 0.1f)
                lastT = now
                animTime += dt
                mathTime += 0.025f

                if (now - lastLifeUpdate >= A_LIFE_INTERVAL) {
                    updateGameOfLife()
                    lastLifeUpdate = now
                }

                val dtScale = (dt * 60f)
                think(dtScale, now)
                updatePet(dtScale, now)
                maybeStartCurveDrawing(now)
                updateActiveCurves(now)

                val ease = min(1f, 0.2f * dtScale)
                pet.renderX += (pet.x - pet.renderX) * ease
                pet.renderY += (pet.y - pet.renderY) * ease

                // xoá nền
                canvas.drawColor(Color.rgb(2, 2, 8))

                // xoay nhẹ
                rotY += 0.002f
                rotX = sin(rotY * 0.55f) * 0.06f + 0.55f

                drawSkyBody(canvas, now)
                drawTrails(canvas, now)
                drawGrid(canvas, now)
                drawFood(canvas, now)
                drawPet(canvas, now)
                drawActiveCurves(canvas, now)
                drawGallery(canvas, now)
                drawSparkles(canvas, now)
                drawBubbles(canvas, now)
                drawStatus(canvas, now)

                updateWaves(dt)

            } catch (e: Exception) {
                // bỏ qua
            } finally {
                if (canvas != null) {
                    try { holder.unlockCanvasAndPost(canvas) } catch (_: Exception) {}
                }
            }
        }

        private fun updateWaves(dt: Float) {
            val it = waves.iterator()
            while (it.hasNext()) {
                val wv = it.next()
                wv.radius += dt * A_WAVE_SPEED
                if (wv.radius >= A_WAVE_MAX) it.remove()
            }
            if (waves.isEmpty()) colorWave = null
        }

        // ── vẽ từng phần ──
        private fun drawSkyBody(canvas: Canvas, now: Long) {
            val phase = dayPhase(now)
            val night = nightFactor(now)
            val isNight = phase >= 0.5f
            val halfT = if (isNight) (phase - 0.5f) * 2f else phase * 2f
            val margin = max(46f * dpr, w * 0.06f)
            val cx = margin + halfT * (w - margin * 2)
            val cy = 96f * dpr - sin(halfT * PI.toFloat()) * 60f * dpr
            val r = (18f + 3f * sin(mathTime * 1.618f)) * dpr

            fill.style = Paint.Style.FILL
            if (!isNight) {
                fill.color = Color.argb(220, 255, 200, 60)
                fill.setShadowLayer(18f, 0f, 0f, Color.argb(180, 255, 200, 60))
            } else {
                fill.color = Color.argb(210, 200, 220, 255)
                fill.setShadowLayer(16f, 0f, 0f, Color.argb(180, 200, 220, 255))
            }
            canvas.drawCircle(cx, cy, r, fill)
            fill.clearShadowLayer()

            // quầng + nan hoa
            if (!isNight) {
                stroke.color = Color.argb(120, 255, 210, 80)
                stroke.strokeWidth = 2f * dpr
                canvas.drawCircle(cx, cy, r * 1.85f, stroke)
                stroke.color = Color.argb(200, 255, 220, 120)
                stroke.strokeWidth = 1.6f * dpr
                for (i in 0 until 12) {
                    val ang = i * PI.toFloat() / 6f + mathTime * 0.3f
                    val l = r * (1.5f + 0.12f * sin(mathTime * 3f + i))
                    canvas.drawLine(
                        cx + cos(ang) * r * 1.2f, cy + sin(ang) * r * 1.2f,
                        cx + cos(ang) * l, cy + sin(ang) * l, stroke
                    )
                }
            } else {
                fill.color = Color.argb((night * 45).toInt().coerceIn(0, 255), 200, 220, 255)
                canvas.drawCircle(cx, cy, r * 1.55f, fill)
            }

            // dial vòng tiến trình
            stroke.strokeWidth = 2.5f * dpr
            stroke.color = Color.argb(20, 255, 255, 255)
            canvas.drawCircle(cx, cy, r * 2.9f, stroke)
            stroke.color = if (night > 0.5f) Color.argb(140, 200, 220, 255) else Color.argb(140, 255, 210, 90)
            rectF.set(cx - r * 2.9f, cy - r * 2.9f, cx + r * 2.9f, cy + r * 2.9f)
            canvas.drawArc(rectF, -90f, phase * 360f, false, stroke)
        }

        private fun drawTrails(canvas: Canvas, now: Long) {
            val night = nightFactor(now)
            val it = trails.iterator()
            while (it.hasNext()) {
                val t = it.next()
                t.life *= A_TRAIL_FADE
                if (t.life <= 0.035f) { it.remove(); continue }
                val tmp = FloatArray(2)
                val z = if (t.rainbow) 12f else -10f - min(35f, t.age * 1.2f)
                project3D((t.x - A_COLS / 2f) * A_CELL, (t.y - A_ROWS / 2f) * A_CELL, z, tmp)
                if (t.rainbow) {
                    val a = (0.65f * (1f + night * 0.6f) * t.life * max(0.3f, tmp[2])).coerceIn(0f, 1f)
                    fill.color = Color.HSVToColor((a * 255f).toInt(), floatArrayOf(t.hue, 1f, 0.7f))
                    fill.setShadowLayer(6f * t.life, 0f, 0f, fill.color)
                    canvas.drawCircle(tmp[0], tmp[1], max(1.2f, 4.5f * t.life * tmp[2]) * dpr, fill)
                    fill.clearShadowLayer()
                } else {
                    val a = (0.16f + night * 0.12f) * t.life * max(0.3f, tmp[2])
                    fill.color = Color.argb((a * 255f).toInt().coerceIn(0, 255), 117, 88, 255)
                    canvas.drawCircle(tmp[0], tmp[1], max(0.6f, 2.2f * tmp[2]) * dpr, fill)
                }
            }
        }

        private fun drawGrid(canvas: Canvas, now: Long) {
            val night = nightFactor(now)
            val tmp = FloatArray(2)
            val cw = colorWave
            for (x in 0 until A_COLS) {
                for (y in 0 until A_ROWS) {
                    if (grid[x][y] == 0) continue
                    val a = age[x][y]
                    val pz = min(52f, a * 2.1f)
                    project3D((x - A_COLS / 2f) * A_CELL, (y - A_ROWS / 2f) * A_CELL, pz, tmp)
                    val alpha = (min(0.82f, 0.22f + a / A_MAX_AGE.toFloat() * 0.65f) * max(0.3f, tmp[2]))
                        .coerceIn(0f, 1f)
                    var hue = (A_MIC_HUE + x * 1.4f + y * 0.8f + mathTime * 8f) % 360f
                    if (cw != null) {
                        val waveAge = (now - startAt) / 1000f
                        if (waveAge < 1.8f) {
                            val ringDist = abs(hypot((x - pet.x), (y - pet.y)) - cw.radius / A_CELL)
                            if (ringDist < 3f) {
                                val s = (1f - ringDist / 3f) * (1f - waveAge / 1.8f)
                                hue = (hue + 180f * s) % 360f
                            }
                        }
                    }
                    val light = 0.58f * (1f - night * 0.35f)
                    fill.color = Color.HSVToColor((alpha * 255f).toInt(), floatArrayOf(hue, 0.92f, light))
                    fill.setShadowLayer(6f, 0f, 0f, fill.color)
                    canvas.drawCircle(tmp[0], tmp[1], max(1.1f, (2.2f + a * 0.055f) * tmp[2]) * dpr, fill)
                    fill.clearShadowLayer()
                }
            }
        }

        private fun drawFood(canvas: Canvas, now: Long) {
            val it = food.iterator()
            while (it.hasNext()) {
                val f = it.next()
                if (now - f.born >= A_FOOD_TTL) { it.remove(); continue }
                val life = 1f - (now - f.born).toFloat() / A_FOOD_TTL
                val tmp = FloatArray(2)
                project3D((f.x - A_COLS / 2f) * A_CELL, (f.y - A_ROWS / 2f) * A_CELL, 28f, tmp)
                val hue = (f.hue + (1f - life) * 80f) % 360f
                val radius = 4.5f * (0.75f + life * 0.25f) * tmp[2] * dpr
                fill.color = Color.HSVToColor(
                    ((0.28f + 0.72f * life) * 255f).toInt().coerceIn(0, 255),
                    floatArrayOf(hue, 0.96f, 0.7f)
                )
                fill.setShadowLayer(12f, 0f, 0f, fill.color)
                canvas.drawCircle(tmp[0], tmp[1], radius, fill)
                fill.clearShadowLayer()
            }
        }

        private fun drawPet(canvas: Canvas, now: Long) {
            val swimAmp = if (pet.state == "SLEEPING") 0.01f else 1f
            val swimX = pet.renderX + sin(mathTime * 2.3f) * 0.04f * swimAmp
            val swimY = pet.renderY + cos(mathTime * 1.9f) * 0.03f
            val tmp = FloatArray(2)
            project3D(
                (swimX - A_COLS / 2f) * A_CELL,
                (swimY - A_ROWS / 2f) * A_CELL,
                22f + sin(mathTime * 3f) * 2f, tmp
            )
            val lv = pet.level
            val bodyGrow = 1f + min(lv, 40) * 0.006f
            val sleepCurl = if (pet.state == "SLEEPING") 0.9f else 1f
            val bodyR = max(0.1f, (7.5f + sin(mathTime * 6f) * (if (pet.state == "SLEEPING") 0.25f else 1.1f)) *
                tmp[2] * bodyGrow * sleepCurl) * dpr
            val extraEyes = (if (lv >= 25) 1 else 0) + (if (lv >= 70) 1 else 0)
            val halo = lv >= 50

            // quầng ngoài
            stroke.color = Color.HSVToColor(
                ((0.12f + min(0.3f, lv * 0.004f)) * 255f).toInt().coerceIn(0, 255),
                floatArrayOf(A_MIC_HUE, 1f, 0.7f)
            )
            stroke.strokeWidth = (1.2f + min(2f, lv * 0.025f)) * dpr
            canvas.drawCircle(tmp[0], tmp[1], bodyR * (2.0f + min(1.2f, lv * 0.012f)), stroke)
            if (halo) {
                stroke.color = Color.HSVToColor(
                    (0.34f * 255f).toInt(),
                    floatArrayOf((A_MIC_HUE + 55f) % 360f, 0.95f, 0.74f)
                )
                stroke.strokeWidth = 1.4f * dpr
                rectF.set(tmp[0] - bodyR * 2.55f, tmp[1] - bodyR * 0.95f,
                    tmp[0] + bodyR * 2.55f, tmp[1] + bodyR * 0.95f)
                canvas.drawOval(rectF, stroke)
            }

            // thân
            fill.color = Color.HSVToColor(
                (0.96f * 255f).toInt(), floatArrayOf(A_MIC_HUE, 0.95f, 0.68f)
            )
            fill.setShadowLayer(18f + min(18f, lv * 0.22f), 0f, 0f, fill.color)
            rectF.set(tmp[0] - bodyR * 1.35f, tmp[1] - bodyR * 0.78f,
                tmp[0] + bodyR * 1.35f, tmp[1] + bodyR * 0.78f)
            canvas.save()
            canvas.rotate(sin(mathTime) * 15f, tmp[0], tmp[1])
            canvas.drawOval(rectF, fill)
            canvas.restore()
            fill.clearShadowLayer()

            // mắt
            var lookX = 0.45f; var lookY = -0.12f
            val eyePaint = Paint(Paint.ANTI_ALIAS_FLAG)
            val eyeHue = (A_MIC_HUE + 145f) % 360f
            eyePaint.color = Color.HSVToColor(
                (0.95f * 255f).toInt(), floatArrayOf(eyeHue, 0.95f, 0.64f)
            )
            if (pet.state == "SLEEPING") {
                stroke.color = eyePaint.color
                stroke.strokeWidth = max(1.5f * dpr, bodyR * 0.08f)
                path.reset()
                path.moveTo(tmp[0] + bodyR * 0.25f, tmp[1] - bodyR * 0.05f)
                path.quadraticBezierTo(
                    tmp[0] + bodyR * 0.45f, tmp[1] + bodyR * 0.08f,
                    tmp[0] + bodyR * 0.65f, tmp[1] - bodyR * 0.05f
                )
                canvas.drawPath(path, stroke)
            } else {
                val eyeR = bodyR * 0.22f
                canvas.drawCircle(tmp[0] + bodyR * lookX, tmp[1] + bodyR * lookY, eyeR, eyePaint)
                fill.color = Color.argb(210, 3, 8, 18)
                canvas.drawCircle(
                    tmp[0] + bodyR * (lookX + 0.045f),
                    tmp[1] + bodyR * (lookY + 0.015f),
                    eyeR * 0.42f, fill
                )
            }
            for (e in 0 until extraEyes) {
                val ey = tmp[1] + (if (e == 0) 1f else -1f) * bodyR * 0.28f
                canvas.drawCircle(tmp[0] + bodyR * 0.18f, ey, bodyR * 0.12f, eyePaint)
            }

            // bờm
            val maneCount = min(7, 4 + lv / 25)
            stroke.strokeCap = Paint.Cap.ROUND
            for (m in 0 until maneCount) {
                val hue = (m * (360f / maneCount) + now * 0.1f) % 360f
                val spread = (m - (maneCount - 1) / 2f) * 0.25f
                val sx = tmp[0] - bodyR * 0.20f + spread * bodyR * 0.50f
                val sy = tmp[1] - bodyR * 0.58f
                val cx2 = sx - bodyR * (0.68f + min(0.24f, lv * 0.003f))
                val cy2 = sy - bodyR * 0.45f + sin(mathTime * 5f + m) * bodyR * 0.34f
                val ex = sx - bodyR * (1.25f + min(0.45f, lv * 0.006f))
                val ey = sy - bodyR * 0.18f + cos(mathTime * 4f + m) * bodyR * 0.42f
                stroke.color = Color.HSVToColor(
                    (0.92f * 255f).toInt(), floatArrayOf(hue, 0.95f, 0.68f)
                )
                stroke.strokeWidth = max(1.4f * dpr, bodyR * (0.12f + min(0.035f, lv * 0.0006f)))
                path.reset()
                path.moveTo(sx, sy)
                path.quadraticBezierTo(cx2, cy2, ex, ey)
                canvas.drawPath(path, stroke)
            }

            // chân
            val legPositions = floatArrayOf(-0.42f, -0.15f, 0.15f, 0.42f)
            val activeSwing = if (pet.state == "SLEEPING") 0.08f else 1f
            for (l in 0 until 4) {
                val sx = tmp[0] + legPositions[l] * bodyR
                val sy = tmp[1] + bodyR * 0.48f
                val legSwing = sin(mathTime * 8f + l * 1.2f) * bodyR * 0.32f * activeSwing
                stroke.color = Color.HSVToColor(
                    (0.85f * 255f).toInt(),
                    floatArrayOf((A_MIC_HUE + l * 12f) % 360f, 0.85f, 0.65f)
                )
                stroke.strokeWidth = max(1.2f * dpr, bodyR * 0.11f)
                path.reset()
                path.moveTo(sx, sy)
                path.quadraticBezierTo(
                    sx + legSwing * 0.5f, sy + bodyR * 0.42f,
                    sx + legSwing, sy + bodyR * 0.76f
                )
                canvas.drawPath(path, stroke)
            }

            // bong bóng ngẫu nhiên
            if (rnd.nextFloat() < 0.06f) {
                bubbles.add(ABubble(tmp[0], tmp[1], (1f + rnd.nextFloat() * 2f) * dpr, 1f))
            }
        }

        private fun drawActiveCurves(canvas: Canvas, now: Long) {
            for (ac in activeCurves) {
                val elapsed = now - ac.startTime
                val breathe = 1f + 0.1f * sin(elapsed * 0.001f)
                val tmp = FloatArray(2)
                project3D((ac.cxGrid - A_COLS / 2f) * A_CELL, (ac.cyGrid - A_ROWS / 2f) * A_CELL, 22f, tmp)
                val dx = tmp[0] - ac.cx
                val dy = tmp[1] - ac.cy

                val activeHue = (ac.hue + elapsed * 0.022f) % 360f
                stroke.strokeWidth = 2.5f * dpr
                stroke.strokeCap = Paint.Cap.ROUND
                stroke.strokeJoin = Paint.Join.ROUND
                path.reset()
                var started = false
                var seg = false
                val upto = min(ac.drawnUpTo, ac.points.size - 1)
                for (i in 0..upto) {
                    val p = ac.points[i] ?: run { seg = false; continue }
                    val px = ac.cx + (p[0] - ac.cx) * breathe + dx
                    val py = ac.cy + (p[1] - ac.cy) * breathe + dy
                    if (!seg) { path.moveTo(px, py); seg = true } else path.lineTo(px, py)
                    started = true
                }
                if (started) {
                    stroke.color = Color.HSVToColor(
                        (0.85f * 255f).toInt(), floatArrayOf(activeHue, 1f, 0.65f)
                    )
                    stroke.setShadowLayer(12f, 0f, 0f, stroke.color)
                    canvas.drawPath(path, stroke)
                    stroke.clearShadowLayer()
                }

                // bút vẽ
                if (!ac.completed) {
                    var penIdx = ac.drawnUpTo
                    while (penIdx > 0 && ac.points[penIdx] == null) penIdx--
                    val pen = ac.points.getOrNull(penIdx)
                    if (pen != null) {
                        val px = ac.cx + (pen[0] - ac.cx) * breathe + dx
                        val py = ac.cy + (pen[1] - ac.cy) * breathe + dy
                        val penPulse = 0.6f + 0.4f * (0.5f + 0.5f * sin(mathTime * 1.618f))
                        fill.color = Color.HSVToColor(
                            (penPulse * 255f).toInt().coerceIn(0, 255),
                            floatArrayOf(activeHue, 1f, 0.75f)
                        )
                        fill.setShadowLayer(18f * penPulse, 0f, 0f, fill.color)
                        canvas.drawCircle(px, py, 5f * penPulse * dpr, fill)
                        fill.clearShadowLayer()
                    }
                }
            }
        }

        private fun drawGallery(canvas: Canvas, now: Long) {
            for (gc in gallery) {
                val elapsed = now - gc.startTime
                val breathe = 1f + 0.1f * sin(elapsed * 0.001f)
                val tmp = FloatArray(2)
                project3D((gc.cxGrid - A_COLS / 2f) * A_CELL, (gc.cyGrid - A_ROWS / 2f) * A_CELL, 22f, tmp)
                val dx = tmp[0] - gc.cx
                val dy = tmp[1] - gc.cy
                val hueShift = (elapsed * 0.02f) % 360f
                stroke.color = Color.HSVToColor(
                    (0.4f * 255f).toInt(),
                    floatArrayOf((gc.hue + hueShift) % 360f, 1f, 0.6f)
                )
                stroke.strokeWidth = 1.2f * dpr
                stroke.strokeCap = Paint.Cap.ROUND
                path.reset()
                var seg = false
                for (p in gc.points) {
                    if (p == null) { seg = false; continue }
                    val px = gc.cx + (p[0] - gc.cx) * breathe + dx
                    val py = gc.cy + (p[1] - gc.cy) * breathe + dy
                    if (!seg) { path.moveTo(px, py); seg = true } else path.lineTo(px, py)
                }
                canvas.drawPath(path, stroke)
            }
        }

        private fun drawSparkles(canvas: Canvas, now: Long) {
            val it = sparkles.iterator()
            while (it.hasNext()) {
                val s = it.next()
                s.life *= 0.95f
                if (s.life <= 0.05f) { it.remove(); continue }
                val tmp = FloatArray(2)
                project3D(
                    (s.x - A_COLS / 2f) * A_CELL, (s.y - A_ROWS / 2f) * A_CELL,
                    28f + sin(mathTime * 10f) * 4f, tmp
                )
                fill.color = Color.HSVToColor(
                    (s.life * 255f).toInt().coerceIn(0, 255),
                    floatArrayOf(s.hue, 1f, 0.7f)
                )
                fill.setShadowLayer(8f * s.life, 0f, 0f, fill.color)
                canvas.drawCircle(tmp[0], tmp[1], max(1f, 3f * s.life * tmp[2]) * dpr, fill)
                fill.clearShadowLayer()
            }
        }

        private fun drawBubbles(canvas: Canvas, now: Long) {
            val it = bubbles.iterator()
            while (it.hasNext()) {
                val b = it.next()
                b.y -= 0.35f * dpr
                b.life *= 0.985f
                if (b.life <= 0.05f) { it.remove(); continue }
                stroke.color = Color.HSVToColor(
                    (b.life * 0.45f * 255f).toInt().coerceIn(0, 255),
                    floatArrayOf(A_MIC_HUE, 0.95f, 0.72f)
                )
                stroke.strokeWidth = 1.2f * dpr
                canvas.drawCircle(b.x, b.y, b.r, stroke)
            }
        }

        private fun drawStatus(canvas: Canvas, now: Long) {
            textPaint.color = Color.argb(230, 0, 255, 204)
            textPaint.setShadowLayer(6f, 0f, 0f, Color.argb(255, 0, 255, 204))
            val isNight = nightFactor(now) > 0.5f
            val label = "LV${pet.level} · H${pet.hunger.toInt()} E${pet.energy.toInt()} M${pet.mood.toInt()} · ${pet.state}" +
                (if (isNight) " 🌙" else " ☀️")
            canvas.drawText(label, 12f * dpr, max(34f * dpr, h * 0.06f), textPaint)
            textPaint.clearShadowLayer()
        }
    }
}
