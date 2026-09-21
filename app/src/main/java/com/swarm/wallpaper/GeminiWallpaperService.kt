package com.swarm.wallpaper

import android.app.WallpaperManager
import android.content.Context
import android.graphics.Color
import android.hardware.Sensor
import android.hardware.SensorEvent
import android.hardware.SensorEventListener
import android.hardware.SensorManager
import android.opengl.EGL14
import android.opengl.EGLConfig
import android.opengl.EGLContext
import android.opengl.EGLDisplay
import android.opengl.EGLSurface
import android.opengl.GLES20
import android.opengl.Matrix
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.os.PowerManager
import android.os.SystemClock
import android.service.wallpaper.WallpaperService
import android.view.MotionEvent
import android.view.SurfaceHolder
import android.view.VelocityTracker
import android.view.ViewConfiguration
import java.nio.ByteBuffer
import java.nio.ByteOrder
import java.nio.FloatBuffer
import kotlin.math.PI
import kotlin.math.abs
import kotlin.math.atan2
import kotlin.math.cos
import kotlin.math.exp
import kotlin.math.floor
import kotlin.math.hypot
import kotlin.math.max
import kotlin.math.min
import kotlin.math.sin
import kotlin.math.sqrt
import kotlin.random.Random

/**
 * Alien Aquarium — optimized Android live-wallpaper port of the HTML prototype.
 *
 * Optimization strategy borrowed from gemlive.kt:
 * - EGL/OpenGL ES 2.0 renderer; reef/effects are GPU point batches instead of Canvas arcs.
 * - Static grid coordinates live in one VBO; only compact dynamic attributes are rebuilt.
 * - Game of Life updates at ~9 Hz; pet decisions at 2.5 Hz; needs at 1 Hz.
 * - Adaptive 60/30/15 fps depending on interaction and Battery Saver.
 * - Sensor registration only while visible.
 * - Touch orbit + inertial continuation; launcher offsets as fallback.
 * - No per-frame heap churn in hot rendering paths where practical.
 *
 * This file intentionally focuses on the aquarium simulation/live-wallpaper experience.
 * Browser-only features from the HTML (DOM buttons, PNG download, localStorage gallery UI)
 * are translated to wallpaper-appropriate interactions instead of copied literally.
 */

// ───────────────────────── CONFIG ─────────────────────────
private const val COLS = 48
private const val ROWS = 48
private const val CELL_SIZE = 11f
private const val CELL_COUNT = COLS * ROWS
private const val MAX_AGE = 24

private const val FPS_IDLE = 30
private const val FPS_INTERACTION = 60
private const val FPS_SAVER = 15
private const val LIFE_INTERVAL_MS = 110L
private const val NEEDS_TICK_MS = 1000L
private const val DECISION_INTERVAL_MS = 400L
private const val SAVE_INTERVAL_MS = 2500L
private const val FOOD_TTL_MS = 12_000L
private const val MAX_FOOD = 16
private const val MAX_TRAILS = 1000
private const val MAX_SPARKLES = 256
private const val MAX_CURVE_POINTS = 520
private const val OFFLINE_CAP_MS = 4L * 60L * 60L * 1000L
private const val DAY_LENGTH_MS = 150_000L
private const val POST_MEAL_PLAY_MS = 3000L
private const val FRENZY_MS = 20_000L
private const val FRENZY_EVERY_MS = 120_000L

private const val PET_BASE_SPEED = 0.35f
private const val MIC_HUE = 168f

private const val TILT_MAX_DEG = 12f
private const val TILT_GAIN = 0.65f
private const val TILT_SMOOTH_HZ = 5f
private const val DRAG_DEG_PER_SCREEN = 125f
private const val INERTIA_FRICTION = 3.8f
private const val INERTIA_STOP_DPS = 2f
private const val AUTO_DELAY_MS = 1100L
private const val AUTO_YAW_DPS = 2.8f

private const val PREFS = "alienAquariumLiteV2"

private fun clamp(v: Float, lo: Float, hi: Float) = max(lo, min(hi, v))
private fun clampI(v: Int, lo: Int, hi: Int) = max(lo, min(hi, v))
private fun hueRgb(hue: Float, sat: Float = 0.92f, light: Float = 0.58f): FloatArray {
    val c = (1f - abs(2f * light - 1f)) * sat
    val hp = ((hue % 360f) + 360f) % 360f / 60f
    val x = c * (1f - abs(hp % 2f - 1f))
    val (r1, g1, b1) = when {
        hp < 1f -> floatArrayOf(c, x, 0f)
        hp < 2f -> floatArrayOf(x, c, 0f)
        hp < 3f -> floatArrayOf(0f, c, x)
        hp < 4f -> floatArrayOf(0f, x, c)
        hp < 5f -> floatArrayOf(x, 0f, c)
        else -> floatArrayOf(c, 0f, x)
    }
    val m = light - c * .5f
    return floatArrayOf(r1 + m, g1 + m, b1 + m)
}

private enum class PetState { EXPLORE, HUNTING, SLEEPING }
private data class Food(var x: Float, var y: Float, var born: Long, var hue: Float, var value: Int = 2)
private data class Trail(var x: Float, var y: Float, var life: Float, var hue: Float, var rainbow: Boolean)
private data class Sparkle(var x: Float, var y: Float, var life: Float, var hue: Float)
private data class CurvePoint(var x: Float, var y: Float, var born: Long, var hue: Float)

private const val VERT = """
attribute vec4 aPosSize;   // xyz in aquarium world, w = point size
attribute vec4 aColor;     // rgba
uniform mat4 uMV;
uniform mat4 uProj;
uniform float uPointScale;
varying vec4 vColor;
void main() {
    vec4 mv = uMV * vec4(aPosSize.xyz, 1.0);
    gl_Position = uProj * mv;
    gl_PointSize = max(1.0, aPosSize.w * uPointScale * (420.0 / max(80.0, -mv.z)));
    vColor = aColor;
}
"""

private const val FRAG = """
precision mediump float;
varying vec4 vColor;
void main() {
    vec2 p = gl_PointCoord * 2.0 - 1.0;
    float d = dot(p, p);
    if (d > 1.0) discard;
    float edge = smoothstep(1.0, 0.62, d);
    float glow = smoothstep(1.0, 0.0, d);
    gl_FragColor = vec4(vColor.rgb * (0.82 + glow * 0.45), vColor.a * edge);
}
"""

class GeminiWallpaperService : WallpaperService() {
    override fun onCreateEngine(): Engine = AquariumEngine()

    private inner class AquariumEngine : Engine() {
        private val handler = Handler(Looper.getMainLooper())
        private val power = getSystemService(Context.POWER_SERVICE) as PowerManager
        private val prefs = getSharedPreferences(PREFS, Context.MODE_PRIVATE)
        private val sensors = getSystemService(Context.SENSOR_SERVICE) as SensorManager
        private val gravitySensor = sensors.getDefaultSensor(Sensor.TYPE_GRAVITY)
            ?: sensors.getDefaultSensor(Sensor.TYPE_ACCELEROMETER)
        private val touchSlop = ViewConfiguration.get(this@GeminiWallpaperService).scaledTouchSlop.toFloat()

        private var shown = false
        private var glReady = false
        private var dpy: EGLDisplay = EGL14.EGL_NO_DISPLAY
        private var ctx: EGLContext = EGL14.EGL_NO_CONTEXT
        private var surf: EGLSurface = EGL14.EGL_NO_SURFACE
        private var program = 0
        private var dynamicVbo = 0
        private var locPosSize = -1
        private var locColor = -1
        private var locMV = -1
        private var locProj = -1
        private var locPointScale = -1

        private var width = 0
        private var height = 0
        private var pixelRatio = 1f
        private val proj = FloatArray(16)
        private val mv = FloatArray(16)
        private val rotTmp = FloatArray(16)
        private val userRotation = FloatArray(16).also { Matrix.setIdentityM(it, 0) }

        // Interleaved x,y,z,size,r,g,b,a. Capacity covers reef + effects with headroom.
        private val maxPoints = CELL_COUNT + MAX_TRAILS + MAX_SPARKLES + MAX_FOOD + MAX_CURVE_POINTS + 32
        private val gpuData: FloatBuffer = ByteBuffer.allocateDirect(maxPoints * 8 * 4)
            .order(ByteOrder.nativeOrder()).asFloatBuffer()

        // ── Reef: flat arrays reduce indirection/GC versus Array<Array<Int>> ──
        private var grid = ByteArray(CELL_COUNT)
        private var nextGrid = ByteArray(CELL_COUNT)
        private var age = ByteArray(CELL_COUNT)
        private var nextAge = ByteArray(CELL_COUNT)
        private var population = 0
        private var generation = 0

        private val food = ArrayList<Food>(MAX_FOOD)
        private val trails = ArrayList<Trail>(MAX_TRAILS)
        private val sparkles = ArrayList<Sparkle>(MAX_SPARKLES)
        private val curvePoints = ArrayList<CurvePoint>(MAX_CURVE_POINTS)

        // ── Pet ──
        private var petX = 2f
        private var petY = ROWS * .5f
        private var petRenderX = petX
        private var petRenderY = petY
        private var hunger = prefs.getFloat("hunger", 25f)
        private var energy = prefs.getFloat("energy", 88f)
        private var mood = prefs.getFloat("mood", 72f)
        private var xp = prefs.getInt("xp", 0)
        private var level = levelFromXp(xp)
        private var fed = prefs.getInt("fed", 0)
        private var state = PetState.EXPLORE
        private var playUntil = 0L
        private var nextDecision = 0L
        private var nextStrollAt = 8_000L + Random.nextLong(14_000L)
        private var strollUntil = 0L
        private var targetX = COLS * .5f
        private var targetY = ROWS * .5f
        private var drawingUntil = 0L
        private var drawingHue = MIC_HUE
        private var curvePhase = 0f
        private val seed = prefs.getString("seed", null) ?: Random.nextLong().toString(36)
        private val personality = derivePersonality(seed)
        private val nestX = 5f + ((hash32(seed).ushr(3) % (COLS - 10)).toFloat())
        private val nestY = 5f + ((hash32(seed).ushr(11) % (ROWS - 10)).toFloat())

        // ── Timing ──
        private var lastFrameAt = 0L
        private var lastLifeAt = 0L
        private var lastNeedsAt = 0L
        private var lastSaveAt = 0L
        private var mathTime = 0f
        private var nextFrenzyAt = 45_000L
        private var frenzyUntil = 0L
        private var nextFrenzyCurveAt = 0L

        // ── Input / sensor ──
        private var sensorRegistered = false
        private val gravity = FloatArray(3)
        private var haveGravity = false
        private var lastSensorNs = 0L
        private var targetPitch = 0f
        private var targetRoll = 0f
        private var tiltPitch = 0f
        private var tiltRoll = 0f
        private var touching = false
        private var downX = 0f
        private var downY = 0f
        private var lastTouchX = 0f
        private var lastTouchY = 0f
        private var dragDistance = 0f
        private var velocityTracker: VelocityTracker? = null
        private var yawVel = 0f
        private var pitchVel = 0f
        private var lastMotionAt = 0L
        private var lastOffsetX = -1f
        private var lastOffsetAt = 0L
        private var offsetYaw = 0f

        private val sensorListener = object : SensorEventListener {
            override fun onSensorChanged(event: SensorEvent) {
                if (!shown || event.values.size < 3) return
                val dt = if (lastSensorNs == 0L) .02f
                else ((event.timestamp - lastSensorNs) * 1e-9f).coerceIn(.001f, .1f)
                lastSensorNs = event.timestamp
                val hz = if (event.sensor.type == Sensor.TYPE_GRAVITY) 7f else 3.5f
                val a = 1f - exp((-2f * PI.toFloat() * hz * dt))
                if (!haveGravity) {
                    for (i in 0..2) gravity[i] = event.values[i]
                    haveGravity = true
                } else {
                    for (i in 0..2) gravity[i] += (event.values[i] - gravity[i]) * a
                }
                val gx = gravity[0]; val gy = gravity[1]; val gz = gravity[2]
                val rawRoll = Math.toDegrees(atan2(gx.toDouble(), sqrt((gy * gy + gz * gz).toDouble()))).toFloat()
                val rawPitch = Math.toDegrees(atan2((-gy).toDouble(), sqrt((gx * gx + gz * gz).toDouble()))).toFloat()
                targetRoll = clamp(-rawRoll * TILT_GAIN, -TILT_MAX_DEG, TILT_MAX_DEG)
                targetPitch = clamp(-rawPitch * TILT_GAIN, -TILT_MAX_DEG, TILT_MAX_DEG)
            }
            override fun onAccuracyChanged(sensor: Sensor?, accuracy: Int) = Unit
        }

        private val loop = object : Runnable {
            override fun run() {
                val t0 = SystemClock.uptimeMillis()
                drawFrame(t0)
                if (!shown) return
                val interaction = touching || abs(yawVel) >= INERTIA_STOP_DPS || abs(pitchVel) >= INERTIA_STOP_DPS ||
                    (t0 - lastOffsetAt in 0..180L)
                val fps = when {
                    interaction -> FPS_INTERACTION
                    power.isPowerSaveMode -> FPS_SAVER
                    else -> FPS_IDLE
                }
                val spent = SystemClock.uptimeMillis() - t0
                handler.postDelayed(this, max(1L, 1000L / fps - spent))
            }
        }

        init {
            reseed()
            applyOfflineDecay()
        }

        override fun onCreate(surfaceHolder: SurfaceHolder) {
            super.onCreate(surfaceHolder)
            setTouchEventsEnabled(true)
        }

        override fun onSurfaceCreated(holder: SurfaceHolder) {
            super.onSurfaceCreated(holder)
            if (initEgl(holder)) glReady = initGl()
        }

        override fun onSurfaceChanged(holder: SurfaceHolder, format: Int, w: Int, h: Int) {
            super.onSurfaceChanged(holder, format, w, h)
            width = max(1, w)
            height = max(1, h)
            pixelRatio = resources.displayMetrics.density.coerceAtMost(3f)
            val aspect = width.toFloat() / height.toFloat()
            Matrix.perspectiveM(proj, 0, 58f, aspect, 0.1f, 3000f)
        }

        override fun onVisibilityChanged(visible: Boolean) {
            shown = visible
            handler.removeCallbacks(loop)
            if (visible) {
                val now = SystemClock.uptimeMillis()
                lastFrameAt = now; lastLifeAt = now; lastNeedsAt = now; lastMotionAt = now
                registerSensors()
                handler.post(loop)
            } else {
                unregisterSensors(); savePet(true)
                velocityTracker?.recycle(); velocityTracker = null; touching = false
            }
        }

        override fun onSurfaceDestroyed(holder: SurfaceHolder) {
            shown = false
            handler.removeCallbacks(loop)
            unregisterSensors()
            releaseGl()
            super.onSurfaceDestroyed(holder)
        }

        override fun onDestroy() {
            shown = false
            handler.removeCallbacks(loop)
            unregisterSensors()
            savePet(true)
            velocityTracker?.recycle(); velocityTracker = null
            releaseGl()
            super.onDestroy()
        }

        // ───────────────────────── INTERACTION ─────────────────────────
        override fun onTouchEvent(event: MotionEvent) {
            velocityTracker?.addMovement(event)
            when (event.actionMasked) {
                MotionEvent.ACTION_DOWN -> {
                    velocityTracker?.recycle()
                    velocityTracker = VelocityTracker.obtain().also { it.addMovement(event) }
                    touching = true
                    downX = event.x; downY = event.y
                    lastTouchX = event.x; lastTouchY = event.y
                    dragDistance = 0f; yawVel = 0f; pitchVel = 0f
                    lastMotionAt = SystemClock.uptimeMillis()
                }
                MotionEvent.ACTION_MOVE -> {
                    val dx = event.x - lastTouchX
                    val dy = event.y - lastTouchY
                    dragDistance += hypot(dx, dy)
                    applyOrbitDelta(dx / width * DRAG_DEG_PER_SCREEN, dy / height * DRAG_DEG_PER_SCREEN)
                    lastTouchX = event.x; lastTouchY = event.y
                    lastMotionAt = SystemClock.uptimeMillis()
                }
                MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {
                    val wasTap = dragDistance < touchSlop && abs(event.x - downX) < touchSlop && abs(event.y - downY) < touchSlop
                    if (event.actionMasked == MotionEvent.ACTION_UP && wasTap) onTap(event.x, event.y)
                    else {
                        velocityTracker?.computeCurrentVelocity(1000)
                        yawVel = (((velocityTracker?.xVelocity ?: 0f) / width) * DRAG_DEG_PER_SCREEN).coerceIn(-320f, 320f)
                        pitchVel = (((velocityTracker?.yVelocity ?: 0f) / height) * DRAG_DEG_PER_SCREEN).coerceIn(-220f, 220f)
                    }
                    touching = false
                    velocityTracker?.recycle(); velocityTracker = null
                    lastMotionAt = SystemClock.uptimeMillis()
                }
            }
            super.onTouchEvent(event)
        }

        override fun onOffsetsChanged(xOffset: Float, yOffset: Float, xOffsetStep: Float, yOffsetStep: Float, xPixelOffset: Int, yPixelOffset: Int) {
            val now = SystemClock.uptimeMillis()
            if (!touching && lastOffsetX >= 0f) {
                val dx = xOffset - lastOffsetX
                if (abs(dx) < .5f) {
                    offsetYaw += dx * 60f
                    if (abs(dx) > .0005f) {
                        val dt = ((now - lastOffsetAt) / 1000f).coerceIn(.008f, .12f)
                        yawVel = (yawVel * .55f + (dx / dt * 60f) * .45f).coerceIn(-280f, 280f)
                        lastMotionAt = now
                    }
                }
            }
            lastOffsetX = xOffset; lastOffsetAt = now
            super.onOffsetsChanged(xOffset, yOffset, xOffsetStep, yOffsetStep, xPixelOffset, yPixelOffset)
        }

        override fun onCommand(action: String?, x: Int, y: Int, z: Int, extras: Bundle?, resultRequested: Boolean): Bundle? {
            if (action == WallpaperManager.COMMAND_TAP) onTap(x.toFloat(), y.toFloat())
            return super.onCommand(action, x, y, z, extras, resultRequested)
        }

        private fun onTap(sx: Float, sy: Float) {
            val gx = clamp((sx / max(1, width) * COLS), 0f, (COLS - 1).toFloat())
            val gy = clamp((sy / max(1, height) * ROWS), 0f, (ROWS - 1).toFloat())
            // Petting wins if tap is close to rendered pet; otherwise feed.
            val dx = gx - petRenderX; val dy = gy - petRenderY
            if (dx * dx + dy * dy < 10f) {
                mood = min(100f, mood + 5f); xp += 2
                repeat(12) { addSparkle(petX + Random.nextFloat() * 2f - 1f, petY + Random.nextFloat() * 2f - 1f, MIC_HUE + it * 17f) }
            } else if (food.size < MAX_FOOD) {
                food.add(Food(gx, gy, SystemClock.uptimeMillis(), Random.nextFloat() * 360f, 2))
            }
        }

        private fun applyOrbitDelta(yawDeg: Float, pitchDeg: Float) {
            if (yawDeg != 0f) Matrix.rotateM(userRotation, 0, yawDeg, 0f, 1f, 0f)
            if (pitchDeg != 0f) Matrix.rotateM(userRotation, 0, pitchDeg, 1f, 0f, 0f)
        }

        // ───────────────────────── SIMULATION ─────────────────────────
        private fun reseed() {
            for (i in 0 until CELL_COUNT) {
                grid[i] = if (Random.nextFloat() < .24f) 1 else 0
                age[i] = 0
            }
            generation = 0
        }

        private fun updateLife() {
            population = 0
            java.util.Arrays.fill(nextGrid, 0)
            java.util.Arrays.fill(nextAge, 0)
            for (x in 0 until COLS) for (y in 0 until ROWS) {
                var n = 0
                for (dx in -1..1) for (dy in -1..1) {
                    if (dx == 0 && dy == 0) continue
                    val nx = (x + dx + COLS) % COLS
                    val ny = (y + dy + ROWS) % ROWS
                    n += grid[nx * ROWS + ny].toInt()
                }
                val i = x * ROWS + y
                val alive = grid[i].toInt() != 0
                val live2 = (alive && (n == 2 || n == 3)) || (!alive && n == 3)
                if (live2) {
                    nextGrid[i] = 1
                    nextAge[i] = if (alive) min(MAX_AGE, age[i].toInt() + 1).toByte() else 1
                    population++
                } else if (alive) {
                    addTrail(x.toFloat(), y.toFloat(), 265f, false)
                }
            }
            val tg = grid; grid = nextGrid; nextGrid = tg
            val ta = age; age = nextAge; nextAge = ta
            generation++
        }

        private fun updateNeeds(seconds: Int) {
            if (state == PetState.SLEEPING) {
                energy = min(100f, energy + 3f * seconds)
                return
            }
            hunger = min(100f, hunger + .72f * seconds)
            energy = max(0f, energy - .24f * seconds)
            if (SystemClock.uptimeMillis() < playUntil) energy = max(0f, energy - .48f * seconds)
            mood = max(0f, mood - .04f * seconds)
        }

        private fun pickState(now: Long): PetState {
            val night = nightFactor(now)
            if (state == PetState.SLEEPING) return if (energy >= 70f) PetState.EXPLORE else PetState.SLEEPING
            if (energy < 14f + (1f - personality[1]) * 6f + night * 12f) return PetState.SLEEPING
            if (food.isNotEmpty() && hunger > 35f) return PetState.HUNTING
            return PetState.EXPLORE
        }

        private fun updatePet(dtScale: Float, now: Long) {
            if (now >= nextDecision) {
                nextDecision = now + DECISION_INTERVAL_MS
                state = pickState(now)
            }

            if (drawingUntil > now && state != PetState.HUNTING && state != PetState.SLEEPING) {
                curvePhase += .055f * dtScale
                val rr = 5.5f
                targetX = COLS * .5f + cos(curvePhase) * rr
                targetY = ROWS * .5f + sin(curvePhase * 1.3f) * rr
                if (curvePoints.size < MAX_CURVE_POINTS) {
                    val petals = 5f
                    val r = 11f * cos(petals * curvePhase)
                    val cx = COLS * .5f + cos(curvePhase) * r
                    val cy = ROWS * .5f + sin(curvePhase) * r
                    curvePoints.add(CurvePoint(cx, cy, now, drawingHue))
                }
            } else if (state == PetState.SLEEPING) {
                targetX = nestX; targetY = nestY
            } else if (state == PetState.HUNTING && food.isNotEmpty()) {
                var best = food[0]; var bd = Float.MAX_VALUE
                for (f in food) {
                    val d = hypot(f.x - petX, f.y - petY)
                    if (d < bd) { bd = d; best = f }
                }
                targetX = best.x; targetY = best.y
            } else {
                if (now >= nextStrollAt || now >= strollUntil) {
                    nextStrollAt = now + 12_000L + Random.nextLong(14_000L) - (mood * 60f).toLong()
                    strollUntil = now + 4000L + Random.nextLong(4000L)
                    targetX = 2f + Random.nextFloat() * (COLS - 5)
                    targetY = 2f + Random.nextFloat() * (ROWS - 5)
                }
                if (now < playUntil) {
                    val a = now * .007f
                    targetX = clamp(petX + cos(a * 2.1f) * 4f, 0f, (COLS - 1).toFloat())
                    targetY = clamp(petY + sin(a * 3.3f) * 3f, 0f, (ROWS - 1).toFloat())
                    if (Random.nextFloat() < .08f) addSparkle(petX, petY, 48f)
                }
            }

            val greed = personality[2]
            val speedF = (.6f + greed * .4f) * (.5f + energy / 200f) * (1f - hunger / 300f) * if (state == PetState.HUNTING) 1.35f else 1f
            val dx = targetX - petX; val dy = targetY - petY
            val d = hypot(dx, dy)
            if (d > .01f) {
                val step = min(d, PET_BASE_SPEED * speedF * dtScale)
                petX += dx / d * step; petY += dy / d * step
                if (Random.nextFloat() < .22f) addTrail(petX, petY, (now * .2f + generation * 9f + petX * 7f) % 360f, true)
            }

            if (state != PetState.SLEEPING && Random.nextFloat() < .015f) {
                val ix = clampI(petX.toInt(), 0, COLS - 1); val iy = clampI(petY.toInt(), 0, ROWS - 1)
                val idx = ix * ROWS + iy
                grid[idx] = 1; age[idx] = max(1, age[idx].toInt()).toByte()
                mood = min(100f, mood + 1f); xp += 2
            }

            var eaten = -1
            for (i in food.indices) if (hypot(food[i].x - petX, food[i].y - petY) < 1.2f) { eaten = i; break }
            if (eaten >= 0) {
                val v = food[eaten].value
                food.removeAt(eaten)
                hunger = max(0f, hunger - 32f * v)
                energy = min(100f, energy + 12f * v)
                mood = min(100f, mood + 8f * v)
                fed += v; xp += 10 * v; level = levelFromXp(xp)
                playUntil = now + POST_MEAL_PLAY_MS
                repeat(18) { addSparkle(petX, petY, MIC_HUE + it * 11f) }
                if (Random.nextFloat() < .72f) startCurve(now)
            }

            val ease = min(1f, .2f * dtScale)
            petRenderX += (petX - petRenderX) * ease
            petRenderY += (petY - petRenderY) * ease
        }

        private fun startCurve(now: Long) {
            drawingUntil = now + if (frenzyUntil > now) 1400L else 6500L
            drawingHue = Random.nextFloat() * 360f
            curvePhase = Random.nextFloat() * PI.toFloat() * 2f
        }

        private fun tickFrenzy(now: Long) {
            if (frenzyUntil == 0L && now >= nextFrenzyAt && state != PetState.SLEEPING) {
                frenzyUntil = now + FRENZY_MS
                nextFrenzyCurveAt = now
                nextFrenzyAt = now + FRENZY_EVERY_MS
            }
            if (frenzyUntil > 0L && now >= frenzyUntil) frenzyUntil = 0L
            if (frenzyUntil > now && now >= nextFrenzyCurveAt) {
                nextFrenzyCurveAt = now + 950L
                startCurve(now)
                xp += 4
            }
        }

        private fun ageEffects(now: Long, dt: Float) {
            for (i in trails.indices.reversed()) {
                val t = trails[i]; t.life *= exp(-3.2f * dt)
                if (t.life < .035f) trails.removeAt(i)
            }
            for (i in sparkles.indices.reversed()) {
                val s = sparkles[i]; s.life *= exp(-3.0f * dt)
                if (s.life < .05f) sparkles.removeAt(i)
            }
            for (i in food.indices.reversed()) if (now - food[i].born > FOOD_TTL_MS) food.removeAt(i)
            for (i in curvePoints.indices.reversed()) if (now - curvePoints[i].born > 11_000L) curvePoints.removeAt(i)
        }

        private fun addTrail(x: Float, y: Float, hue: Float, rainbow: Boolean) {
            if (trails.size >= MAX_TRAILS) trails.removeAt(0)
            trails.add(Trail(x, y, 1f, hue, rainbow))
        }

        private fun addSparkle(x: Float, y: Float, hue: Float) {
            if (sparkles.size >= MAX_SPARKLES) sparkles.removeAt(0)
            sparkles.add(Sparkle(x, y, 1f, hue))
        }

        // ───────────────────────── RENDER ─────────────────────────
        private fun drawFrame(now: Long) {
            if (!glReady || width <= 0 || height <= 0) return
            val dt = ((now - lastFrameAt) / 1000f).coerceIn(0f, .05f)
            val dtScale = if (dt <= 0f) 1f else dt / .0167f
            lastFrameAt = now
            mathTime += dt

            if (now - lastLifeAt >= LIFE_INTERVAL_MS) {
                updateLife(); lastLifeAt = now
            }
            if (now - lastNeedsAt >= NEEDS_TICK_MS) {
                val sec = max(1, ((now - lastNeedsAt) / 1000L).toInt())
                updateNeeds(sec); lastNeedsAt += sec * 1000L
            }
            tickFrenzy(now)
            updatePet(dtScale, now)
            ageEffects(now, dt)
            if (now - lastSaveAt >= SAVE_INTERVAL_MS) savePet(false)

            val tiltA = 1f - exp((-2f * PI.toFloat() * TILT_SMOOTH_HZ * dt))
            tiltPitch += (targetPitch - tiltPitch) * tiltA
            tiltRoll += (targetRoll - tiltRoll) * tiltA
            if (!touching) {
                if (yawVel != 0f || pitchVel != 0f) applyOrbitDelta(yawVel * dt, pitchVel * dt)
                val damp = exp(-INERTIA_FRICTION * dt)
                yawVel *= damp; pitchVel *= damp
                if (abs(yawVel) < INERTIA_STOP_DPS) yawVel = 0f
                if (abs(pitchVel) < INERTIA_STOP_DPS) pitchVel = 0f
            }
            val inertial = abs(yawVel) + abs(pitchVel) > INERTIA_STOP_DPS * 1.5f
            if (!touching && !inertial && now - lastMotionAt >= AUTO_DELAY_MS) applyOrbitDelta(AUTO_YAW_DPS * dt, 0f)

            if (!EGL14.eglMakeCurrent(dpy, surf, surf, ctx)) return
            GLES20.glViewport(0, 0, width, height)
            val night = nightFactor(now)
            val bg = .006f + night * .008f
            GLES20.glClearColor(bg, bg, .025f + night * .025f, 1f)
            GLES20.glClear(GLES20.GL_COLOR_BUFFER_BIT)

            Matrix.setIdentityM(mv, 0)
            val aspect = width.toFloat() / height.toFloat()
            val camZ = max(740f, 455f / max(.52f, aspect))
            Matrix.translateM(mv, 0, 0f, 0f, -camZ)
            Matrix.rotateM(mv, 0, 31.5f + tiltPitch, 1f, 0f, 0f)
            Matrix.rotateM(mv, 0, tiltRoll + offsetYaw, 0f, 1f, 0f)
            Matrix.multiplyMM(rotTmp, 0, mv, 0, userRotation, 0)
            System.arraycopy(rotTmp, 0, mv, 0, 16)

            val count = buildGpuBatch(now, night)
            if (count > 0) {
                GLES20.glUseProgram(program)
                GLES20.glUniformMatrix4fv(locMV, 1, false, mv, 0)
                GLES20.glUniformMatrix4fv(locProj, 1, false, proj, 0)
                GLES20.glUniform1f(locPointScale, pixelRatio)
                GLES20.glEnable(GLES20.GL_BLEND)
                GLES20.glBlendFunc(GLES20.GL_SRC_ALPHA, GLES20.GL_ONE_MINUS_SRC_ALPHA)
                GLES20.glBindBuffer(GLES20.GL_ARRAY_BUFFER, dynamicVbo)
                gpuData.position(0)
                GLES20.glBufferSubData(GLES20.GL_ARRAY_BUFFER, 0, count * 8 * 4, gpuData)
                GLES20.glEnableVertexAttribArray(locPosSize)
                GLES20.glVertexAttribPointer(locPosSize, 4, GLES20.GL_FLOAT, false, 32, 0)
                GLES20.glEnableVertexAttribArray(locColor)
                GLES20.glVertexAttribPointer(locColor, 4, GLES20.GL_FLOAT, false, 32, 16)
                GLES20.glDrawArrays(GLES20.GL_POINTS, 0, count)
                GLES20.glDisableVertexAttribArray(locPosSize)
                GLES20.glDisableVertexAttribArray(locColor)
            }
            EGL14.eglSwapBuffers(dpy, surf)
        }

        private fun buildGpuBatch(now: Long, night: Float): Int {
            gpuData.clear()
            var count = 0
            fun putPoint(x: Float, y: Float, z: Float, size: Float, r: Float, g: Float, b: Float, a: Float) {
                if (count >= maxPoints) return
                gpuData.put(x).put(y).put(z).put(size).put(r).put(g).put(b).put(a)
                count++
            }

            // Reef. CPU computes color/age, GPU does projection + point rasterization.
            val wave = (now * .008f) % 360f
            for (x in 0 until COLS) for (y in 0 until ROWS) {
                val i = x * ROWS + y
                if (grid[i].toInt() == 0) continue
                val a = age[i].toInt()
                val z = min(52f, a * 2.1f)
                val hue = (MIC_HUE + x * 1.4f + y * .8f + wave) % 360f
                val rgb = hueRgb(hue, .92f, .58f * (1f - night * .28f))
                val alpha = min(.84f, .22f + a / MAX_AGE.toFloat() * .65f)
                putPoint((x - COLS / 2f) * CELL_SIZE, (y - ROWS / 2f) * CELL_SIZE, z,
                    3.4f + a * .08f, rgb[0], rgb[1], rgb[2], alpha)
            }

            for (t in trails) {
                val rgb = if (t.rainbow) hueRgb(t.hue, 1f, .65f) else floatArrayOf(.46f, .34f, 1f)
                putPoint((t.x - COLS / 2f) * CELL_SIZE, (t.y - ROWS / 2f) * CELL_SIZE,
                    if (t.rainbow) 12f else -14f, if (t.rainbow) 6.5f * t.life + 1.5f else 3.1f,
                    rgb[0], rgb[1], rgb[2], t.life * if (t.rainbow) .72f else .24f)
            }

            for (f in food) {
                val life = (1f - (now - f.born).toFloat() / FOOD_TTL_MS).coerceIn(0f, 1f)
                val rgb = hueRgb((f.hue + (1f - life) * 80f) % 360f, .96f, .64f)
                putPoint((f.x - COLS / 2f) * CELL_SIZE, (f.y - ROWS / 2f) * CELL_SIZE, 28f,
                    8f + f.value * 1.2f, rgb[0], rgb[1], rgb[2], .3f + .7f * life)
            }

            for (c in curvePoints) {
                val life = (1f - (now - c.born).toFloat() / 11_000f).coerceIn(0f, 1f)
                val rgb = hueRgb(c.hue, 1f, .67f)
                putPoint((c.x - COLS / 2f) * CELL_SIZE, (c.y - ROWS / 2f) * CELL_SIZE, 34f,
                    5.4f, rgb[0], rgb[1], rgb[2], .78f * life)
            }

            for (s in sparkles) {
                val rgb = hueRgb(s.hue, 1f, .72f)
                putPoint((s.x - COLS / 2f) * CELL_SIZE, (s.y - ROWS / 2f) * CELL_SIZE,
                    31f + sin(mathTime * 10f) * 4f, 6f * s.life + 1f, rgb[0], rgb[1], rgb[2], s.life)
            }

            // Pet: layered point-sprite body + eye + level halo markers.
            val swimX = petRenderX + sin(mathTime * 2.3f) * .04f
            val swimY = petRenderY + cos(mathTime * 1.9f) * .03f
            val bodyGrow = 1f + min(level, 40) * .006f
            val baseX = (swimX - COLS / 2f) * CELL_SIZE
            val baseY = (swimY - ROWS / 2f) * CELL_SIZE
            val petRgb = hueRgb(MIC_HUE, .95f, .68f)
            putPoint(baseX, baseY, 25f, 21f * bodyGrow, petRgb[0], petRgb[1], petRgb[2], .96f)
            val eyeRgb = hueRgb((MIC_HUE + 145f) % 360f, .95f, .66f)
            if (state != PetState.SLEEPING) {
                putPoint(baseX + 5f, baseY - 1.4f, 29f, 5f, eyeRgb[0], eyeRgb[1], eyeRgb[2], 1f)
                putPoint(baseX + 5.6f, baseY - 1.2f, 30f, 2.1f, .02f, .05f, .09f, .9f)
            }
            if (level >= 25) putPoint(baseX + 1f, baseY - 6f, 28f, 3f, eyeRgb[0], eyeRgb[1], eyeRgb[2], .9f)
            if (level >= 70) putPoint(baseX + 1f, baseY + 6f, 28f, 3f, eyeRgb[0], eyeRgb[1], eyeRgb[2], .9f)
            if (level >= 50) {
                val haloRgb = hueRgb((MIC_HUE + 55f) % 360f, .95f, .74f)
                for (i in 0 until 12) {
                    val a = i / 12f * PI.toFloat() * 2f + mathTime * .35f
                    putPoint(baseX + cos(a) * 20f, baseY + sin(a) * 8f, 24f, 2.3f,
                        haloRgb[0], haloRgb[1], haloRgb[2], .34f)
                }
            }

            gpuData.flip()
            return count
        }

        // ───────────────────────── EGL / GL ─────────────────────────
        private fun initEgl(holder: SurfaceHolder): Boolean {
            dpy = EGL14.eglGetDisplay(EGL14.EGL_DEFAULT_DISPLAY)
            if (dpy == EGL14.EGL_NO_DISPLAY) return false
            val ver = IntArray(2)
            if (!EGL14.eglInitialize(dpy, ver, 0, ver, 1)) return false
            val attrs = intArrayOf(
                EGL14.EGL_RENDERABLE_TYPE, EGL14.EGL_OPENGL_ES2_BIT,
                EGL14.EGL_RED_SIZE, 8, EGL14.EGL_GREEN_SIZE, 8, EGL14.EGL_BLUE_SIZE, 8, EGL14.EGL_ALPHA_SIZE, 8,
                EGL14.EGL_NONE
            )
            val cfgs = arrayOfNulls<EGLConfig>(1); val n = IntArray(1)
            if (!EGL14.eglChooseConfig(dpy, attrs, 0, cfgs, 0, 1, n, 0) || n[0] == 0) return false
            val cfg = cfgs[0] ?: return false
            ctx = EGL14.eglCreateContext(dpy, cfg, EGL14.EGL_NO_CONTEXT,
                intArrayOf(EGL14.EGL_CONTEXT_CLIENT_VERSION, 2, EGL14.EGL_NONE), 0)
            surf = EGL14.eglCreateWindowSurface(dpy, cfg, holder.surface, intArrayOf(EGL14.EGL_NONE), 0)
            if (ctx == EGL14.EGL_NO_CONTEXT || surf == EGL14.EGL_NO_SURFACE) return false
            return EGL14.eglMakeCurrent(dpy, surf, surf, ctx)
        }

        private fun compile(type: Int, source: String): Int {
            val s = GLES20.glCreateShader(type)
            GLES20.glShaderSource(s, source); GLES20.glCompileShader(s)
            val ok = IntArray(1); GLES20.glGetShaderiv(s, GLES20.GL_COMPILE_STATUS, ok, 0)
            if (ok[0] == 0) { GLES20.glDeleteShader(s); return 0 }
            return s
        }

        private fun initGl(): Boolean {
            val vs = compile(GLES20.GL_VERTEX_SHADER, VERT); val fs = compile(GLES20.GL_FRAGMENT_SHADER, FRAG)
            if (vs == 0 || fs == 0) return false
            program = GLES20.glCreateProgram()
            GLES20.glAttachShader(program, vs); GLES20.glAttachShader(program, fs); GLES20.glLinkProgram(program)
            GLES20.glDeleteShader(vs); GLES20.glDeleteShader(fs)
            val ok = IntArray(1); GLES20.glGetProgramiv(program, GLES20.GL_LINK_STATUS, ok, 0)
            if (ok[0] == 0) return false
            locPosSize = GLES20.glGetAttribLocation(program, "aPosSize")
            locColor = GLES20.glGetAttribLocation(program, "aColor")
            locMV = GLES20.glGetUniformLocation(program, "uMV")
            locProj = GLES20.glGetUniformLocation(program, "uProj")
            locPointScale = GLES20.glGetUniformLocation(program, "uPointScale")
            val ids = IntArray(1); GLES20.glGenBuffers(1, ids, 0); dynamicVbo = ids[0]
            GLES20.glBindBuffer(GLES20.GL_ARRAY_BUFFER, dynamicVbo)
            GLES20.glBufferData(GLES20.GL_ARRAY_BUFFER, maxPoints * 8 * 4, null, GLES20.GL_DYNAMIC_DRAW)
            return true
        }

        private fun releaseGl() {
            try {
                if (dpy != EGL14.EGL_NO_DISPLAY) {
                    if (ctx != EGL14.EGL_NO_CONTEXT && surf != EGL14.EGL_NO_SURFACE) {
                        EGL14.eglMakeCurrent(dpy, surf, surf, ctx)
                        if (dynamicVbo != 0) GLES20.glDeleteBuffers(1, intArrayOf(dynamicVbo), 0)
                        if (program != 0) GLES20.glDeleteProgram(program)
                    }
                    EGL14.eglMakeCurrent(dpy, EGL14.EGL_NO_SURFACE, EGL14.EGL_NO_SURFACE, EGL14.EGL_NO_CONTEXT)
                    if (surf != EGL14.EGL_NO_SURFACE) EGL14.eglDestroySurface(dpy, surf)
                    if (ctx != EGL14.EGL_NO_CONTEXT) EGL14.eglDestroyContext(dpy, ctx)
                    EGL14.eglTerminate(dpy)
                }
            } catch (_: Exception) { }
            dpy = EGL14.EGL_NO_DISPLAY; surf = EGL14.EGL_NO_SURFACE; ctx = EGL14.EGL_NO_CONTEXT
            glReady = false
        }

        // ───────────────────────── PERSISTENCE / HELPERS ─────────────────────────
        private fun registerSensors() {
            if (!sensorRegistered && gravitySensor != null) {
                sensorRegistered = sensors.registerListener(sensorListener, gravitySensor, SensorManager.SENSOR_DELAY_GAME)
                lastSensorNs = 0L
            }
        }

        private fun unregisterSensors() {
            if (sensorRegistered) sensors.unregisterListener(sensorListener)
            sensorRegistered = false; lastSensorNs = 0L; haveGravity = false
        }

        private fun savePet(force: Boolean) {
            val now = SystemClock.uptimeMillis()
            if (!force && now - lastSaveAt < SAVE_INTERVAL_MS) return
            lastSaveAt = now
            prefs.edit()
                .putString("seed", seed)
                .putLong("savedAt", System.currentTimeMillis())
                .putFloat("hunger", hunger).putFloat("energy", energy).putFloat("mood", mood)
                .putInt("xp", xp).putInt("level", level).putInt("fed", fed)
                .apply()
        }

        private fun applyOfflineDecay() {
            val savedAt = prefs.getLong("savedAt", System.currentTimeMillis())
            val elapsed = (System.currentTimeMillis() - savedAt).coerceIn(0L, OFFLINE_CAP_MS)
            if (elapsed <= 0L) return
            val sec = elapsed / 1000f
            hunger = min(100f, hunger + .72f * sec)
            energy = max(0f, energy - .24f * sec)
            mood = max(0f, mood - .04f * sec)
        }

        private fun nightFactor(now: Long): Float {
            val p = ((now % DAY_LENGTH_MS).toFloat() / DAY_LENGTH_MS)
            return (.5f - .5f * cos((p - .25f) * PI.toFloat() * 2f))
        }

        private fun levelFromXp(v: Int): Int = 1 + floor(sqrt(max(0, v) / 45.0)).toInt()

        private fun hash32(s: String): Int {
            var h = 0x811c9dc5.toInt()
            for (ch in s) { h = h xor ch.code; h *= 16777619 }
            return h
        }

        private fun derivePersonality(s: String): FloatArray {
            val n = hash32(s)
            return floatArrayOf(
                (n and 255) / 255f,
                ((n ushr 8) and 255) / 255f,
                ((n ushr 16) and 255) / 255f,
                ((n ushr 24) and 255) / 255f
            )
        }
    }
}
