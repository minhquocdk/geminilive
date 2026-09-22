package com.swarm.wallpaper

import android.app.WallpaperManager
import android.content.Context
import android.graphics.Bitmap
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Paint
import android.graphics.Typeface
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
import android.opengl.GLUtils
import android.opengl.Matrix
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.os.PowerManager
import android.os.SystemClock
import android.service.wallpaper.WallpaperService
import android.view.MotionEvent
import android.view.SurfaceHolder
import java.nio.ByteBuffer
import java.nio.ByteOrder
import java.nio.FloatBuffer
import java.text.SimpleDateFormat
import java.util.Date
import java.util.Locale
import kotlin.math.PI
import kotlin.math.abs
import kotlin.math.atan2
import kotlin.math.cos
import kotlin.math.exp
import kotlin.math.max
import kotlin.math.min
import kotlin.math.sin
import kotlin.math.sqrt
import kotlin.random.Random

// ───────────────────────── ALIEN AQUARIUM / TUNING ─────────────────────────
private const val A_TOTAL_PARTICLES = 20000
private const val A_BG_PARTICLES = 14000
private const val A_DYNAMIC_PARTICLES = A_TOTAL_PARTICLES - A_BG_PARTICLES
private const val A_STRIDE_FLOATS = 9
private const val A_STRIDE_BYTES = A_STRIDE_FLOATS * 4

private const val A_FPS = 60
private const val A_FPS_FRENZY = 60
private const val A_FPS_SAVER = 15
private const val A_FRENZY_MS = 20000L

private const val A_SIZE_BOOST = 1.52f
private const val A_SYMBOLS = "⌖⎋⍕⌬⧉⧇⧻⧼⧽"
private const val A_SYMBOLS_FALLBACK = "✦✧◆◇○△□+×"

// Giữ parallax từ gemlive.kt, bỏ touch orbit / inertia / launcher offset.
private const val A_TILT_MAX_DEG = 16f
private const val A_TILT_GAIN = 0.68f
private const val A_TILT_SMOOTH_HZ = 4.8f

private const val A_PET_SPEED = 23f
private const val A_FOOD_DRAW_MS = 2600L
private const val A_FOOD_EAT_MS = 1100L
private const val A_FOOD_MIN_WAIT_MS = 7000L
private const val A_FOOD_MAX_WAIT_MS = 13500L

private const val KIND_BG = 0f
private const val KIND_DYNAMIC = 1f
private const val KIND_FRENZY = 2f

private data class Spark(
    var x: Float, var y: Float, var z: Float,
    var life: Float, val hue: Float, val seed: Float
)

private data class Tile(
    var value: Int,
    var x: Float, var y: Float, var z: Float,
    var vx: Float, var vy: Float,
    var born: Long,
    var dead: Boolean = false
)

private data class Burst(
    val x: Float, val y: Float, val z: Float,
    val born: Long, val hue: Float, val petals: Int
)

private const val VERT = """
attribute vec4 aP;       // xyz + point size
attribute float aSym;    // glyph atlas index
attribute vec4 aM;       // hue, alpha, kind, seed

uniform mat4 uMV;
uniform mat4 uProj;
uniform float uTime;
uniform float uPR;
uniform float uFrenzy;

varying float vSym;
varying vec4 vColor;

vec3 hsv2rgb(vec3 c) {
    vec4 K = vec4(1.0, 0.6666667, 0.3333333, 3.0);
    vec3 p = abs(fract(c.xxx + K.xyz) * 6.0 - K.www);
    return c.z * mix(K.xxx, clamp(p - K.xxx, 0.0, 1.0), c.y);
}

void main() {
    vec3 p = aP.xyz;
    float kind = aM.z;
    float seed = aM.w;

    // Background chỉ lay động rất nhẹ; pet/clock không bị bóp méo.
    if (kind < 0.5) {
        float depth = clamp((p.z + 110.0) / 230.0, 0.0, 1.0);
        p.x += sin(uTime * (0.22 + seed * 0.13) + seed * 19.0 + p.y * 0.018) * (0.8 + depth * 2.4);
        p.y += cos(uTime * 0.17 + seed * 13.0 + p.x * 0.012) * (0.25 + depth * 0.7);
    }

    vec4 mv = uMV * vec4(p, 1.0);
    float perspective = 300.0 / max(150.0, -mv.z);
    float pulse = kind > 1.5 ? (1.0 + 0.24 * sin(uTime * 9.0 + seed * 25.0)) : 1.0;
    gl_PointSize = max(1.0, aP.w * uPR * perspective * pulse);
    gl_Position = uProj * mv;

    float h = fract(aM.x + (kind > 1.5 ? uFrenzy * 0.21 + uTime * 0.035 : 0.0));
    float sat = kind > 1.5 ? 0.92 : (kind > 0.5 ? 0.82 : 0.72);
    float val = kind > 1.5 ? 1.0 : (kind > 0.5 ? 0.94 : 0.74);
    vec3 rgb = hsv2rgb(vec3(h, sat, val));

    // Xa hơn thì dịu để tạo chiều sâu.
    float depthFade = clamp(1.25 - (-mv.z) / 780.0, 0.30, 1.0);
    vColor = vec4(rgb, aM.y * depthFade);
    vSym = aSym;
}
"""

private const val FRAG = """
precision mediump float;
varying float vSym;
varying vec4 vColor;
uniform sampler2D uTex;

void main() {
    vec2 uv = gl_PointCoord;
    uv.x = (uv.x + vSym) / 16.0;
    vec4 t = texture2D(uTex, uv);
    if (t.a < 0.08) discard;
    gl_FragColor = vec4(vColor.rgb, vColor.a * t.a);
}
"""

class GlyphSpaceWallpaperService : WallpaperService() {

    override fun onCreateEngine(): Engine = AquariumEngine()

    private inner class AquariumEngine : Engine() {
        private val handler = Handler(Looper.getMainLooper())
        private val pm = getSystemService(Context.POWER_SERVICE) as PowerManager
        private val pixelRatio = resources.displayMetrics.density
        private val sensorManager = getSystemService(Context.SENSOR_SERVICE) as SensorManager
        private val gravitySensor = sensorManager.getDefaultSensor(Sensor.TYPE_GRAVITY)
            ?: sensorManager.getDefaultSensor(Sensor.TYPE_ACCELEROMETER)

        private var shown = false
        private var glReady = false

        private var dpy: EGLDisplay = EGL14.EGL_NO_DISPLAY
        private var ctx: EGLContext = EGL14.EGL_NO_CONTEXT
        private var surf: EGLSurface = EGL14.EGL_NO_SURFACE

        private var prog = 0
        private var staticVbo = 0
        private var dynamicVbo = 0
        private var tex = 0
        private var symbolCount = 1

        private var locP = 0
        private var locSym = 0
        private var locM = 0
        private var locMV = 0
        private var locProj = 0
        private var locTime = 0
        private var locPR = 0
        private var locFrenzy = 0
        private var locTex = 0

        private var w = 0
        private var h = 0
        private var camZ = 390f
        private val proj = FloatArray(16)
        private val mv = FloatArray(16)

        private var lastT = 0L
        private var animTime = 0f

        // Sensor parallax only.
        private var sensorRegistered = false
        private val gravity = FloatArray(3)
        private var haveGravity = false
        private var lastSensorNs = 0L
        private var targetPitch = 0f
        private var targetRoll = 0f
        private var tiltPitch = 0f
        private var tiltRoll = 0f

        // Pet autonomous swim.
        private var petX = -45f
        private var petY = 12f
        private var petZ = 34f
        private var petVX = 0f
        private var petVY = 0f
        private var targetX = 48f
        private var targetY = -6f
        private var nextTargetAt = 0L
        private var petPhase = 0f

        // "Pet tự vẽ food": vẽ doodle trước, sau đó tự bơi tới ăn.
        private var foodMode = 0 // 0 none, 1 drawing, 2 ready/eating
        private var foodX = 0f
        private var foodY = 0f
        private var foodZ = 24f
        private var foodStartedAt = 0L
        private var nextFoodAt = 0L

        // Persistent clock art, rebuilt only when minute changes.
        private var lastClockMinute = -1
        private val clockDots = ArrayList<FloatArray>(360)

        // 2048 frenzy: tap only.
        private var frenzyUntil = 0L
        private var nextTileAt = 0L
        private var nextBurstAt = 0L
        private val tiles = ArrayList<Tile>(20)
        private val bursts = ArrayList<Burst>(12)
        private val sparks = ArrayList<Spark>(180)

        // Reused buffers/templates; no large per-frame allocation.
        private lateinit var dynamicBuffer: FloatBuffer
        private var dynamicCount = 0
        private val petTemplate = FloatArray(420 * 4)

        private val clockFormat = SimpleDateFormat("dd/MM HH:mm", Locale.US)

        private val sensorListener = object : SensorEventListener {
            override fun onSensorChanged(event: SensorEvent) {
                if (!shown || event.values.size < 3) return
                val nowNs = event.timestamp
                val dt = if (lastSensorNs == 0L) 0.02f
                else ((nowNs - lastSensorNs) * 1e-9f).coerceIn(0.001f, 0.1f)
                lastSensorNs = nowNs

                val hz = if (event.sensor.type == Sensor.TYPE_GRAVITY) 7f else 3.5f
                val a = 1f - exp((-2f * PI.toFloat() * hz * dt))
                if (!haveGravity) {
                    gravity[0] = event.values[0]
                    gravity[1] = event.values[1]
                    gravity[2] = event.values[2]
                    haveGravity = true
                } else {
                    for (i in 0..2) gravity[i] += (event.values[i] - gravity[i]) * a
                }

                val gx = gravity[0]
                val gy = gravity[1]
                val gz = gravity[2]
                val rawRoll = Math.toDegrees(
                    atan2(gx.toDouble(), sqrt((gy * gy + gz * gz).toDouble()))
                ).toFloat()
                val rawPitch = Math.toDegrees(
                    atan2((-gy).toDouble(), sqrt((gx * gx + gz * gz).toDouble()))
                ).toFloat()

                targetRoll = (-rawRoll * A_TILT_GAIN).coerceIn(-A_TILT_MAX_DEG, A_TILT_MAX_DEG)
                targetPitch = (-rawPitch * A_TILT_GAIN).coerceIn(-A_TILT_MAX_DEG, A_TILT_MAX_DEG)
            }

            override fun onAccuracyChanged(sensor: Sensor?, accuracy: Int) = Unit
        }

        private val loop = object : Runnable {
            override fun run() {
                val t0 = SystemClock.uptimeMillis()
                drawFrame(t0)
                if (shown) {
                    val frenzy = t0 < frenzyUntil
                    val fps = when {
                        frenzy -> A_FPS_FRENZY
                        pm.isPowerSaveMode -> A_FPS_SAVER
                        else -> A_FPS
                    }
                    val spent = SystemClock.uptimeMillis() - t0
                    handler.postDelayed(this, max(1L, 1000L / fps - spent))
                }
            }
        }

        init {
            buildPetTemplate()
        }

        override fun onCreate(surfaceHolder: SurfaceHolder) {
            super.onCreate(surfaceHolder)
            setTouchEventsEnabled(true)
        }

        override fun onSurfaceCreated(holder: SurfaceHolder) {
            super.onSurfaceCreated(holder)
            if (initEGL(holder)) glReady = initGL()
        }

        override fun onSurfaceChanged(holder: SurfaceHolder, format: Int, width: Int, height: Int) {
            super.onSurfaceChanged(holder, format, width, height)
            w = width
            h = height
            val aspect = max(0.30f, w.toFloat() / max(1, h).toFloat())
            // Aquarium cao, ưu tiên fit chiều dọc nhưng vẫn đủ bề ngang trên màn portrait.
            camZ = max(360f, 215f / aspect)
            Matrix.perspectiveM(proj, 0, 60f, aspect, 0.1f, 1800f)
        }

        override fun onVisibilityChanged(visible: Boolean) {
            shown = visible
            handler.removeCallbacks(loop)
            if (visible) {
                val now = SystemClock.uptimeMillis()
                lastT = now
                nextTargetAt = now + 2000L
                nextFoodAt = now + 3500L
                lastClockMinute = -1 // clock art immediately on resume
                registerSensors()
                handler.post(loop)
            } else {
                unregisterSensors()
            }
        }

        override fun onSurfaceDestroyed(holder: SurfaceHolder) {
            shown = false
            handler.removeCallbacks(loop)
            unregisterSensors()
            releaseGL()
            super.onSurfaceDestroyed(holder)
        }

        override fun onDestroy() {
            shown = false
            handler.removeCallbacks(loop)
            unregisterSensors()
            releaseGL()
            super.onDestroy()
        }

        private fun registerSensors() {
            if (!sensorRegistered && gravitySensor != null) {
                sensorRegistered = sensorManager.registerListener(
                    sensorListener, gravitySensor, SensorManager.SENSOR_DELAY_GAME
                )
                lastSensorNs = 0L
            }
        }

        private fun unregisterSensors() {
            if (sensorRegistered) sensorManager.unregisterListener(sensorListener)
            sensorRegistered = false
            lastSensorNs = 0L
        }

        // Tap = 2048 frenzy. MOVE không xoay scene; launcher offset cũng không override.
        override fun onTouchEvent(event: MotionEvent) {
            if (event.actionMasked == MotionEvent.ACTION_UP) {
                triggerFrenzy(SystemClock.uptimeMillis())
            }
            super.onTouchEvent(event)
        }

        override fun onCommand(
            action: String?, x: Int, y: Int, z: Int, extras: Bundle?, resultRequested: Boolean
        ): Bundle? {
            if (action == WallpaperManager.COMMAND_TAP) triggerFrenzy(SystemClock.uptimeMillis())
            return super.onCommand(action, x, y, z, extras, resultRequested)
        }

        private var lastTapAt = 0L
        private fun triggerFrenzy(now: Long) {
            // Một số launcher gửi cả MotionEvent và COMMAND_TAP.
            if (now - lastTapAt < 250L) return
            lastTapAt = now
            frenzyUntil = now + A_FRENZY_MS
            nextTileAt = now
            nextBurstAt = now
            tiles.clear()
            bursts.clear()
            for (i in 0 until 18) spawnSpark(petX, petY, petZ, ((i * 0.055f) % 1f))
        }

        // ───────────────────────── GL SETUP ─────────────────────────
        private fun initEGL(holder: SurfaceHolder): Boolean {
            dpy = EGL14.eglGetDisplay(EGL14.EGL_DEFAULT_DISPLAY)
            if (dpy == EGL14.EGL_NO_DISPLAY) return false
            val ver = IntArray(2)
            if (!EGL14.eglInitialize(dpy, ver, 0, ver, 1)) return false
            val attr = intArrayOf(
                EGL14.EGL_RENDERABLE_TYPE, EGL14.EGL_OPENGL_ES2_BIT,
                EGL14.EGL_RED_SIZE, 8,
                EGL14.EGL_GREEN_SIZE, 8,
                EGL14.EGL_BLUE_SIZE, 8,
                EGL14.EGL_ALPHA_SIZE, 8,
                EGL14.EGL_NONE
            )
            val cfgs = arrayOfNulls<EGLConfig>(1)
            val n = IntArray(1)
            if (!EGL14.eglChooseConfig(dpy, attr, 0, cfgs, 0, 1, n, 0) || n[0] == 0) return false
            val cfg = cfgs[0] ?: return false
            ctx = EGL14.eglCreateContext(
                dpy, cfg, EGL14.EGL_NO_CONTEXT,
                intArrayOf(EGL14.EGL_CONTEXT_CLIENT_VERSION, 2, EGL14.EGL_NONE), 0
            )
            surf = EGL14.eglCreateWindowSurface(dpy, cfg, holder.surface, intArrayOf(EGL14.EGL_NONE), 0)
            if (ctx == EGL14.EGL_NO_CONTEXT || surf == EGL14.EGL_NO_SURFACE) return false
            return EGL14.eglMakeCurrent(dpy, surf, surf, ctx)
        }

        private fun compile(type: Int, src: String): Int {
            val s = GLES20.glCreateShader(type)
            GLES20.glShaderSource(s, src)
            GLES20.glCompileShader(s)
            val st = IntArray(1)
            GLES20.glGetShaderiv(s, GLES20.GL_COMPILE_STATUS, st, 0)
            if (st[0] == 0) {
                GLES20.glDeleteShader(s)
                return 0
            }
            return s
        }

        private fun initGL(): Boolean {
            val vs = compile(GLES20.GL_VERTEX_SHADER, VERT)
            val fs = compile(GLES20.GL_FRAGMENT_SHADER, FRAG)
            if (vs == 0 || fs == 0) return false

            prog = GLES20.glCreateProgram()
            GLES20.glAttachShader(prog, vs)
            GLES20.glAttachShader(prog, fs)
            GLES20.glLinkProgram(prog)
            GLES20.glDeleteShader(vs)
            GLES20.glDeleteShader(fs)
            val st = IntArray(1)
            GLES20.glGetProgramiv(prog, GLES20.GL_LINK_STATUS, st, 0)
            if (st[0] == 0) return false

            locP = GLES20.glGetAttribLocation(prog, "aP")
            locSym = GLES20.glGetAttribLocation(prog, "aSym")
            locM = GLES20.glGetAttribLocation(prog, "aM")
            locMV = GLES20.glGetUniformLocation(prog, "uMV")
            locProj = GLES20.glGetUniformLocation(prog, "uProj")
            locTime = GLES20.glGetUniformLocation(prog, "uTime")
            locPR = GLES20.glGetUniformLocation(prog, "uPR")
            locFrenzy = GLES20.glGetUniformLocation(prog, "uFrenzy")
            locTex = GLES20.glGetUniformLocation(prog, "uTex")

            symbolCount = buildAtlas()
            buildStaticAquarium()

            dynamicBuffer = ByteBuffer
                .allocateDirect(A_DYNAMIC_PARTICLES * A_STRIDE_BYTES)
                .order(ByteOrder.nativeOrder())
                .asFloatBuffer()

            val ids = IntArray(1)
            GLES20.glGenBuffers(1, ids, 0)
            dynamicVbo = ids[0]
            GLES20.glBindBuffer(GLES20.GL_ARRAY_BUFFER, dynamicVbo)
            GLES20.glBufferData(
                GLES20.GL_ARRAY_BUFFER,
                A_DYNAMIC_PARTICLES * A_STRIDE_BYTES,
                null,
                GLES20.GL_DYNAMIC_DRAW
            )
            GLES20.glBindBuffer(GLES20.GL_ARRAY_BUFFER, 0)
            return true
        }

        private fun buildAtlas(): Int {
            val p = Paint(Paint.ANTI_ALIAS_FLAG).apply {
                typeface = Typeface.create(Typeface.SERIF, Typeface.BOLD)
                textSize = 42f
                color = Color.WHITE
                textAlign = Paint.Align.CENTER
            }
            var syms = A_SYMBOLS.map { it.toString() }.filter { p.hasGlyph(it) }
            if (syms.isEmpty()) syms = A_SYMBOLS_FALLBACK.map { it.toString() }.filter { p.hasGlyph(it) }
            if (syms.isEmpty()) syms = listOf("+")
            syms = syms.take(16)

            val bmp = Bitmap.createBitmap(1024, 64, Bitmap.Config.ARGB_8888)
            val cv = Canvas(bmp)
            val fm = p.fontMetrics
            val baseY = 32f - (fm.ascent + fm.descent) / 2f
            syms.forEachIndexed { i, s -> cv.drawText(s, i * 64f + 32f, baseY, p) }

            val ids = IntArray(1)
            GLES20.glGenTextures(1, ids, 0)
            tex = ids[0]
            GLES20.glBindTexture(GLES20.GL_TEXTURE_2D, tex)
            GLUtils.texImage2D(GLES20.GL_TEXTURE_2D, 0, bmp, 0)
            GLES20.glGenerateMipmap(GLES20.GL_TEXTURE_2D)
            GLES20.glTexParameteri(GLES20.GL_TEXTURE_2D, GLES20.GL_TEXTURE_MIN_FILTER, GLES20.GL_LINEAR_MIPMAP_LINEAR)
            GLES20.glTexParameteri(GLES20.GL_TEXTURE_2D, GLES20.GL_TEXTURE_MAG_FILTER, GLES20.GL_LINEAR)
            GLES20.glTexParameteri(GLES20.GL_TEXTURE_2D, GLES20.GL_TEXTURE_WRAP_S, GLES20.GL_CLAMP_TO_EDGE)
            GLES20.glTexParameteri(GLES20.GL_TEXTURE_2D, GLES20.GL_TEXTURE_WRAP_T, GLES20.GL_CLAMP_TO_EDGE)
            bmp.recycle()
            return syms.size
        }

        /**
         * Static background = old gemlive particle budget repurposed into an aquarium volume:
         * deep water dust + sea floor + branching reef/coral. One immutable VBO / one draw call.
         */
        private fun buildStaticAquarium() {
            val buf = ByteBuffer
                .allocateDirect(A_BG_PARTICLES * A_STRIDE_BYTES)
                .order(ByteOrder.nativeOrder())
                .asFloatBuffer()

            var count = 0
            fun put(x: Float, y: Float, z: Float, size: Float, hue: Float, alpha: Float, kind: Float, seed: Float) {
                if (count >= A_BG_PARTICLES) return
                buf.put(x); buf.put(y); buf.put(z); buf.put(size)
                buf.put(Random.nextInt(max(1, symbolCount)).toFloat())
                buf.put(hue); buf.put(alpha); buf.put(kind); buf.put(seed)
                count++
            }

            // 1) Water volume / plankton: sparse, deep, not a flat starfield.
            repeat(5400) {
                val depth = Random.nextFloat()
                val x = (Random.nextFloat() * 2f - 1f) * (118f + depth * 24f)
                val y = -170f + Random.nextFloat() * 330f
                val z = -120f + depth * 155f
                val hue = (0.46f + Random.nextFloat() * 0.14f) % 1f
                put(x, y, z, 2.0f + Random.nextFloat() * 2.2f, hue, 0.14f + depth * 0.28f, KIND_BG, Random.nextFloat())
            }

            // 2) Sea floor: denser toward bottom, slight bowl curvature.
            repeat(3300) {
                val x = (Random.nextFloat() * 2f - 1f) * 122f
                val z = -80f + Random.nextFloat() * 155f
                val bowl = (x * x) / 5200f + (z * z) / 12000f
                val y = 144f + bowl + Random.nextFloat() * 24f
                val hue = 0.48f + Random.nextFloat() * 0.20f
                put(x, y, z, 2.5f + Random.nextFloat() * 2.8f, hue % 1f, 0.34f + Random.nextFloat() * 0.34f, KIND_BG, Random.nextFloat())
            }

            // 3) Coral branches. Curves are pre-baked once; shader adds tiny water sway.
            val coralCenters = arrayOf(
                floatArrayOf(-88f, 143f, -24f, 0.48f),
                floatArrayOf(-48f, 150f, 24f, 0.79f),
                floatArrayOf(10f, 146f, -35f, 0.91f),
                floatArrayOf(55f, 148f, 38f, 0.55f),
                floatArrayOf(91f, 151f, -6f, 0.68f)
            )
            for (c in coralCenters) {
                repeat(760) { i ->
                    val branch = i % 7
                    val t = Random.nextFloat()
                    val ang = branch / 7f * (PI.toFloat() * 2f) + c[0] * 0.007f
                    val rise = 78f * t
                    val spread = (10f + branch * 1.7f) * sin(t * PI.toFloat())
                    val x = c[0] + cos(ang) * spread + sin(t * 7f + branch) * 3f
                    val y = c[1] - rise + sin(t * 9f + branch * 0.7f) * 2.5f
                    val z = c[2] + sin(ang) * spread * 0.7f
                    val hue = (c[3] + t * 0.10f + Random.nextFloat() * 0.035f) % 1f
                    put(x, y, z, 3f + (1f - t) * 1.9f, hue, 0.50f + t * 0.28f, KIND_BG, Random.nextFloat())
                }
            }

            // Fill exact budget with small near-reef sparks.
            while (count < A_BG_PARTICLES) {
                val a = Random.nextFloat() * PI.toFloat() * 2f
                val r = 35f + Random.nextFloat() * 80f
                put(
                    cos(a) * r,
                    95f + Random.nextFloat() * 65f,
                    sin(a) * r * 0.55f,
                    2.2f + Random.nextFloat() * 2f,
                    (0.48f + Random.nextFloat() * 0.42f) % 1f,
                    0.32f + Random.nextFloat() * 0.32f,
                    KIND_BG,
                    Random.nextFloat()
                )
            }

            buf.position(0)
            val ids = IntArray(1)
            GLES20.glGenBuffers(1, ids, 0)
            staticVbo = ids[0]
            GLES20.glBindBuffer(GLES20.GL_ARRAY_BUFFER, staticVbo)
            GLES20.glBufferData(
                GLES20.GL_ARRAY_BUFFER,
                A_BG_PARTICLES * A_STRIDE_BYTES,
                buf,
                GLES20.GL_STATIC_DRAW
            )
            GLES20.glBindBuffer(GLES20.GL_ARRAY_BUFFER, 0)
        }

        private fun releaseGL() {
            try {
                if (dpy != EGL14.EGL_NO_DISPLAY) {
                    if (ctx != EGL14.EGL_NO_CONTEXT && surf != EGL14.EGL_NO_SURFACE) {
                        EGL14.eglMakeCurrent(dpy, surf, surf, ctx)
                        if (staticVbo != 0) GLES20.glDeleteBuffers(1, intArrayOf(staticVbo), 0)
                        if (dynamicVbo != 0) GLES20.glDeleteBuffers(1, intArrayOf(dynamicVbo), 0)
                        if (tex != 0) GLES20.glDeleteTextures(1, intArrayOf(tex), 0)
                        if (prog != 0) GLES20.glDeleteProgram(prog)
                    }
                    EGL14.eglMakeCurrent(dpy, EGL14.EGL_NO_SURFACE, EGL14.EGL_NO_SURFACE, EGL14.EGL_NO_CONTEXT)
                    if (surf != EGL14.EGL_NO_SURFACE) EGL14.eglDestroySurface(dpy, surf)
                    if (ctx != EGL14.EGL_NO_CONTEXT) EGL14.eglDestroyContext(dpy, ctx)
                }
            } catch (_: Exception) {
            }
            surf = EGL14.EGL_NO_SURFACE
            ctx = EGL14.EGL_NO_CONTEXT
            staticVbo = 0
            dynamicVbo = 0
            tex = 0
            prog = 0
            glReady = false
        }

        // ───────────────────────── SIMULATION ─────────────────────────
        private fun buildPetTemplate() {
            // Store local x,y,z + seed. Ellipsoid + fins/tail, deterministic after service creation.
            for (i in 0 until 420) {
                val k = i * 4
                val seed = Random.nextFloat()
                val u = Random.nextFloat() * 2f - 1f
                val a = Random.nextFloat() * PI.toFloat() * 2f
                val rr = sqrt(max(0f, 1f - u * u))
                var x = cos(a) * rr * 14f
                var y = u * 7.5f
                var z = sin(a) * rr * 6f

                when {
                    i >= 330 && i < 385 -> { // tail fan
                        val t = (i - 330) / 55f
                        x = -13f - t * 10f
                        y = (Random.nextFloat() * 2f - 1f) * (3f + t * 9f)
                        z = (Random.nextFloat() * 2f - 1f) * (2f + t * 4f)
                    }
                    i >= 385 -> { // dorsal / ventral fins
                        x = (Random.nextFloat() * 2f - 1f) * 5f
                        y = if (i % 2 == 0) -7f - Random.nextFloat() * 6f else 7f + Random.nextFloat() * 6f
                        z = (Random.nextFloat() * 2f - 1f) * 4f
                    }
                }
                petTemplate[k] = x
                petTemplate[k + 1] = y
                petTemplate[k + 2] = z
                petTemplate[k + 3] = seed
            }
        }

        private fun chooseTarget(now: Long) {
            targetX = -86f + Random.nextFloat() * 172f
            targetY = -88f + Random.nextFloat() * 165f
            nextTargetAt = now + 2800L + Random.nextLong(4200L)
        }

        private fun startFoodDrawing(now: Long) {
            foodMode = 1
            foodStartedAt = now
            val a = Random.nextFloat() * PI.toFloat() * 2f
            val d = 28f + Random.nextFloat() * 28f
            foodX = (petX + cos(a) * d).coerceIn(-92f, 92f)
            foodY = (petY + sin(a) * d).coerceIn(-104f, 112f)
            foodZ = 25f + Random.nextFloat() * 14f
            targetX = foodX
            targetY = foodY
        }

        private fun updatePet(now: Long, dt: Float) {
            petPhase += dt

            if (foodMode == 0 && now >= nextFoodAt && now >= frenzyUntil) startFoodDrawing(now)

            if (foodMode == 1) {
                // Pet orbits the doodle while "drawing" it.
                val p = ((now - foodStartedAt).toFloat() / A_FOOD_DRAW_MS).coerceIn(0f, 1f)
                val a = p * PI.toFloat() * 5.5f
                targetX = foodX + cos(a) * (16f - p * 7f)
                targetY = foodY + sin(a) * (11f - p * 4f)
                if (p >= 1f) {
                    foodMode = 2
                    foodStartedAt = now
                    targetX = foodX
                    targetY = foodY
                }
            } else if (foodMode == 2) {
                targetX = foodX
                targetY = foodY
                val d = hypot2(foodX - petX, foodY - petY)
                if (d < 8f || now - foodStartedAt > A_FOOD_EAT_MS + 3600L) {
                    repeat(16) { spawnSpark(foodX, foodY, foodZ, 0.12f + it * 0.025f) }
                    foodMode = 0
                    nextFoodAt = now + A_FOOD_MIN_WAIT_MS + Random.nextLong(A_FOOD_MAX_WAIT_MS - A_FOOD_MIN_WAIT_MS)
                    chooseTarget(now)
                }
            } else if (now >= nextTargetAt || hypot2(targetX - petX, targetY - petY) < 7f) {
                chooseTarget(now)
            }

            val dx = targetX - petX
            val dy = targetY - petY
            val d = max(0.001f, hypot2(dx, dy))
            val desiredVX = dx / d * A_PET_SPEED
            val desiredVY = dy / d * A_PET_SPEED
            val steer = 1f - exp(-2.6f * dt)
            petVX += (desiredVX - petVX) * steer
            petVY += (desiredVY - petVY) * steer

            if (now < frenzyUntil) {
                val a = animTime * 5.4f
                petVX += cos(a) * 12f * dt
                petVY += sin(a * 1.37f) * 12f * dt
            }

            petX = (petX + petVX * dt).coerceIn(-101f, 101f)
            petY = (petY + petVY * dt).coerceIn(-118f, 126f)
            petZ = 28f + sin(petPhase * 0.9f) * 8f

            if (Random.nextFloat() < dt * 7f) {
                sparks.add(Spark(petX - petVX * 0.18f, petY - petVY * 0.18f, petZ, 1f, (0.47f + animTime * 0.018f) % 1f, Random.nextFloat()))
                if (sparks.size > 180) sparks.removeAt(0)
            }
        }

        private fun updateFrenzy(now: Long, dt: Float) {
            if (now >= frenzyUntil) {
                if (tiles.isNotEmpty()) tiles.removeAll { now - it.born > 1500L }
                bursts.removeAll { now - it.born > 1800L }
                return
            }

            if (now >= nextTileAt) {
                nextTileAt = now + 115L + Random.nextLong(120L)
                val vals = intArrayOf(2, 4, 8, 16, 32, 64)
                tiles.add(
                    Tile(
                        vals[Random.nextInt(vals.size)],
                        petX + (Random.nextFloat() * 2f - 1f) * 16f,
                        petY + (Random.nextFloat() * 2f - 1f) * 13f,
                        petZ + 9f,
                        (Random.nextFloat() * 2f - 1f) * 10f,
                        -8f - Random.nextFloat() * 16f,
                        now
                    )
                )
                if (tiles.size > 24) tiles.removeAt(0)
            }

            if (now >= nextBurstAt) {
                nextBurstAt = now + 900L
                bursts.add(Burst(petX, petY, petZ - 3f, now, Random.nextFloat(), 4 + Random.nextInt(5)))
                if (bursts.size > 12) bursts.removeAt(0)
            }

            for (t in tiles) {
                t.x += t.vx * dt
                t.y += t.vy * dt
                t.z += dt * 10f
                t.vx *= exp(-1.1f * dt)
                t.vy *= exp(-1.1f * dt)
            }

            for (i in 0 until tiles.size) {
                val a = tiles[i]
                if (a.dead) continue
                for (j in i + 1 until tiles.size) {
                    val b = tiles[j]
                    if (!b.dead && a.value == b.value && a.value < 2048 && hypot2(a.x - b.x, a.y - b.y) < 14f) {
                        a.value *= 2
                        a.born = now
                        a.vx *= -0.35f
                        a.vy = -18f
                        b.dead = true
                        repeat(7) { spawnSpark(a.x, a.y, a.z, ((kLog2(a.value) * 0.07f) + it * 0.02f) % 1f) }
                    }
                }
            }
            tiles.removeAll { it.dead || now - it.born > 1500L }
            bursts.removeAll { now - it.born > 1800L }
        }

        private fun updateSparks(dt: Float) {
            for (s in sparks) {
                s.life -= dt * 0.72f
                s.y -= dt * 4f
                s.z += sin(animTime * 2f + s.seed * 8f) * dt * 2f
            }
            sparks.removeAll { it.life <= 0f }
        }

        private fun spawnSpark(x: Float, y: Float, z: Float, hue: Float) {
            if (sparks.size >= 180) sparks.removeAt(0)
            sparks.add(
                Spark(
                    x + (Random.nextFloat() * 2f - 1f) * 5f,
                    y + (Random.nextFloat() * 2f - 1f) * 5f,
                    z + (Random.nextFloat() * 2f - 1f) * 4f,
                    1f,
                    hue,
                    Random.nextFloat()
                )
            )
        }

        // ───────────────────────── CLOCK ART ─────────────────────────
        private val digitRows = arrayOf(
            intArrayOf(7, 5, 5, 5, 7), // 0
            intArrayOf(2, 6, 2, 2, 7), // 1
            intArrayOf(7, 1, 7, 4, 7), // 2
            intArrayOf(7, 1, 7, 1, 7), // 3
            intArrayOf(5, 5, 7, 1, 1), // 4
            intArrayOf(7, 4, 7, 1, 7), // 5
            intArrayOf(7, 4, 7, 5, 7), // 6
            intArrayOf(7, 1, 1, 1, 1), // 7
            intArrayOf(7, 5, 7, 5, 7), // 8
            intArrayOf(7, 5, 7, 1, 7)  // 9
        )

        private fun rebuildClock(nowWall: Long) {
            clockDots.clear()
            val text = clockFormat.format(Date(nowWall))
            // dd/MM HH:mm = 11 chars. 3 cols per digit, separators narrower.
            val unit = 4.7f
            var cursor = 0f
            val widths = FloatArray(text.length)
            for (i in text.indices) {
                widths[i] = when (text[i]) {
                    ':', '/' -> 1.6f
                    ' ' -> 2.0f
                    else -> 3.6f
                }
            }
            val total = widths.sum() * unit
            cursor = -total * 0.5f

            for (ch in text) {
                when {
                    ch in '0'..'9' -> {
                        val rows = digitRows[ch - '0']
                        for (ry in 0..4) {
                            for (rx in 0..2) {
                                if ((rows[ry] and (1 shl (2 - rx))) != 0) {
                                    clockDots.add(floatArrayOf(cursor + rx * unit, -116f + ry * unit, -5f, 0.11f))
                                }
                            }
                        }
                        cursor += 3.6f * unit
                    }
                    ch == ':' -> {
                        clockDots.add(floatArrayOf(cursor, -108f, -5f, 0.11f))
                        clockDots.add(floatArrayOf(cursor, -98f, -5f, 0.11f))
                        cursor += 1.6f * unit
                    }
                    ch == '/' -> {
                        for (i in 0..3) clockDots.add(floatArrayOf(cursor + i * 1.3f, -94f - i * 5.2f, -5f, 0.11f))
                        cursor += 1.6f * unit
                    }
                    else -> cursor += 2.0f * unit
                }
            }
        }

        // ───────────────────────── DYNAMIC PARTICLES ─────────────────────────
        private fun putDyn(
            x: Float, y: Float, z: Float, size: Float,
            sym: Float, hue: Float, alpha: Float, kind: Float, seed: Float
        ) {
            if (dynamicCount >= A_DYNAMIC_PARTICLES) return
            dynamicBuffer.put(x); dynamicBuffer.put(y); dynamicBuffer.put(z); dynamicBuffer.put(size)
            dynamicBuffer.put(sym); dynamicBuffer.put(hue); dynamicBuffer.put(alpha); dynamicBuffer.put(kind); dynamicBuffer.put(seed)
            dynamicCount++
        }

        private fun buildDynamicParticles(now: Long) {
            dynamicBuffer.clear()
            dynamicCount = 0

            // Clock is persistent artwork, but minute key updates only once/minute.
            val wall = System.currentTimeMillis()
            val minute = ((wall / 60000L) % 1440L).toInt()
            if (minute != lastClockMinute) {
                lastClockMinute = minute
                rebuildClock(wall)
            }
            val clockBreath = 0.78f + 0.22f * sin(animTime * 1.7f)
            for ((i, p) in clockDots.withIndex()) {
                putDyn(
                    p[0], p[1], p[2],
                    4.8f + clockBreath * 0.9f,
                    (i % max(1, symbolCount)).toFloat(),
                    (p[3] + animTime * 0.006f) % 1f,
                    0.58f,
                    KIND_DYNAMIC,
                    (i * 0.037f) % 1f
                )
            }

            // Pet: all pixels are the same symbol atlas, never a separate sprite.
            val headingLeft = petVX < 0f
            for (i in 0 until 420) {
                val k = i * 4
                var lx = petTemplate[k]
                val ly = petTemplate[k + 1]
                val lz = petTemplate[k + 2]
                val seed = petTemplate[k + 3]
                if (headingLeft) lx = -lx
                val swim = sin(animTime * 7f + lx * 0.18f + seed * 5f)
                val x = petX + lx + if (abs(lx) > 13f) swim * 2.3f else swim * 0.6f
                val y = petY + ly + sin(animTime * 2.2f + seed * 8f) * 0.8f
                val z = petZ + lz
                val hue = (0.46f + seed * 0.26f + animTime * 0.008f) % 1f
                putDyn(x, y, z, 5.2f + seed * 2.0f, (i % max(1, symbolCount)).toFloat(), hue, 0.88f, KIND_DYNAMIC, seed)
            }

            // Eye/highlight clusters still use atlas glyphs.
            val front = if (headingLeft) -1f else 1f
            repeat(18) { i ->
                val a = i / 18f * PI.toFloat() * 2f
                putDyn(
                    petX + front * 9.5f + cos(a) * 2.1f,
                    petY - 2.3f + sin(a) * 2.1f,
                    petZ + 5.2f,
                    5.7f,
                    (i % max(1, symbolCount)).toFloat(),
                    0.13f,
                    0.98f,
                    KIND_DYNAMIC,
                    i / 18f
                )
            }

            // Food doodle grows along a spiral while the pet orbits it.
            if (foodMode != 0) {
                val prog = if (foodMode == 1) ((now - foodStartedAt).toFloat() / A_FOOD_DRAW_MS).coerceIn(0f, 1f) else 1f
                val n = (prog * 230).toInt().coerceAtLeast(1)
                for (i in 0 until n) {
                    val t = i / 229f
                    val a = t * PI.toFloat() * 7.5f
                    val r = 2f + t * 11f
                    val x = foodX + cos(a) * r
                    val y = foodY + sin(a) * r * 0.72f
                    val z = foodZ + sin(a * 0.5f) * 3f
                    putDyn(x, y, z, 4.9f + sin(t * PI.toFloat()) * 1.8f, (i % max(1, symbolCount)).toFloat(), (0.07f + t * 0.12f) % 1f, 0.90f, KIND_DYNAMIC, t)
                }
            }

            // Swim trail / eating sparkle.
            for ((i, s) in sparks.withIndex()) {
                putDyn(
                    s.x, s.y, s.z,
                    3.2f + s.life * 4.0f,
                    (i % max(1, symbolCount)).toFloat(),
                    s.hue,
                    s.life.coerceIn(0f, 1f) * 0.75f,
                    KIND_DYNAMIC,
                    s.seed
                )
            }

            // Frenzy curve art: pet emits short rose/spiral glyph drawings every ~0.9s.
            for ((bi, b) in bursts.withIndex()) {
                val age = ((now - b.born).toFloat() / 1800f).coerceIn(0f, 1f)
                val visible = min(1f, age * 2.2f)
                val alpha = (1f - age) * 0.86f
                val points = (visible * 250).toInt()
                for (i in 0 until points) {
                    val t = i / 249f * PI.toFloat() * 2f
                    val rr = 18f * cos(b.petals * t * 0.5f) * (0.35f + age * 0.9f)
                    putDyn(
                        b.x + cos(t) * rr,
                        b.y + sin(t) * rr,
                        b.z + sin(t * 2f) * 4f,
                        4.2f,
                        ((i + bi) % max(1, symbolCount)).toFloat(),
                        (b.hue + t / (PI.toFloat() * 2f) * 0.24f) % 1f,
                        alpha,
                        KIND_FRENZY,
                        (i * 0.013f) % 1f
                    )
                }
            }

            // 2048 tiles: digits themselves are 3x5 glyph-particle matrices, not digit glyphs.
            for ((ti, t) in tiles.withIndex()) {
                val age = ((now - t.born).toFloat() / 1500f).coerceIn(0f, 1f)
                val str = t.value.toString()
                val scale = 2.4f + min(2.0f, kLog2(t.value) * 0.13f)
                val width = (str.length * 4 - 1) * scale
                var ox = -width * 0.5f
                for (ch in str) {
                    val rows = digitRows[ch - '0']
                    for (ry in 0..4) for (rx in 0..2) {
                        if ((rows[ry] and (1 shl (2 - rx))) != 0) {
                            putDyn(
                                t.x + ox + rx * scale,
                                t.y + (ry - 2) * scale,
                                t.z + age * 18f,
                                4.4f + scale * 0.7f,
                                ((ti + rx + ry) % max(1, symbolCount)).toFloat(),
                                (0.08f + kLog2(t.value) * 0.035f) % 1f,
                                1f - age,
                                KIND_FRENZY,
                                (rx * 0.17f + ry * 0.11f) % 1f
                            )
                        }
                    }
                    ox += 4f * scale
                }
            }

            dynamicBuffer.flip()
        }

        // ───────────────────────── DRAW ─────────────────────────
        private fun drawFrame(now: Long) {
            if (!glReady || w <= 0 || h <= 0) return
            try {
                val dt = ((now - lastT) / 1000f).coerceIn(0f, 0.08f)
                lastT = now
                animTime += dt

                val tiltA = 1f - exp((-2f * PI.toFloat() * A_TILT_SMOOTH_HZ * dt))
                tiltPitch += (targetPitch - tiltPitch) * tiltA
                tiltRoll += (targetRoll - tiltRoll) * tiltA

                updatePet(now, dt)
                updateFrenzy(now, dt)
                updateSparks(dt)
                buildDynamicParticles(now)

                if (!EGL14.eglMakeCurrent(dpy, surf, surf, ctx)) return
                GLES20.glViewport(0, 0, w, h)
                GLES20.glClearColor(0.004f, 0.008f, 0.020f, 1f)
                GLES20.glClear(GLES20.GL_COLOR_BUFFER_BIT)

                Matrix.setIdentityM(mv, 0)
                Matrix.translateM(mv, 0, 0f, 0f, -camZ)
                Matrix.rotateM(mv, 0, tiltPitch, 1f, 0f, 0f)
                Matrix.rotateM(mv, 0, tiltRoll, 0f, 1f, 0f)
                Matrix.rotateM(mv, 0, -tiltRoll * 0.14f, 0f, 0f, 1f)
                // Aquarium tự thở/xoay cực nhẹ; không liên quan touch/launcher offset.
                Matrix.rotateM(mv, 0, sin(animTime * 0.11f) * 2.4f, 0f, 1f, 0f)

                GLES20.glUseProgram(prog)
                GLES20.glUniformMatrix4fv(locMV, 1, false, mv, 0)
                GLES20.glUniformMatrix4fv(locProj, 1, false, proj, 0)
                GLES20.glUniform1f(locTime, animTime)
                GLES20.glUniform1f(locPR, pixelRatio * A_SIZE_BOOST)
                val frenzyPower = if (now < frenzyUntil) ((frenzyUntil - now).toFloat() / A_FRENZY_MS).coerceIn(0f, 1f) else 0f
                GLES20.glUniform1f(locFrenzy, frenzyPower)

                GLES20.glActiveTexture(GLES20.GL_TEXTURE0)
                GLES20.glBindTexture(GLES20.GL_TEXTURE_2D, tex)
                GLES20.glUniform1i(locTex, 0)

                GLES20.glEnable(GLES20.GL_BLEND)
                GLES20.glBlendFuncSeparate(
                    GLES20.GL_SRC_ALPHA, GLES20.GL_ONE,
                    GLES20.GL_ZERO, GLES20.GL_ONE
                )

                // Draw 1: static aquarium background.
                bindParticleVbo(staticVbo)
                GLES20.glDrawArrays(GLES20.GL_POINTS, 0, A_BG_PARTICLES)

                // Draw 2: pet + food + clock + trail + frenzy.
                if (dynamicCount > 0) {
                    GLES20.glBindBuffer(GLES20.GL_ARRAY_BUFFER, dynamicVbo)
                    GLES20.glBufferSubData(
                        GLES20.GL_ARRAY_BUFFER,
                        0,
                        dynamicCount * A_STRIDE_BYTES,
                        dynamicBuffer
                    )
                    bindParticleVbo(dynamicVbo)
                    GLES20.glDrawArrays(GLES20.GL_POINTS, 0, dynamicCount)
                }

                disableAttribs()
                EGL14.eglSwapBuffers(dpy, surf)
            } catch (_: Exception) {
                // Live wallpaper should survive a bad frame/context transition.
            }
        }

        private fun bindParticleVbo(vbo: Int) {
            GLES20.glBindBuffer(GLES20.GL_ARRAY_BUFFER, vbo)
            GLES20.glEnableVertexAttribArray(locP)
            GLES20.glVertexAttribPointer(locP, 4, GLES20.GL_FLOAT, false, A_STRIDE_BYTES, 0)
            GLES20.glEnableVertexAttribArray(locSym)
            GLES20.glVertexAttribPointer(locSym, 1, GLES20.GL_FLOAT, false, A_STRIDE_BYTES, 16)
            GLES20.glEnableVertexAttribArray(locM)
            GLES20.glVertexAttribPointer(locM, 4, GLES20.GL_FLOAT, false, A_STRIDE_BYTES, 20)
        }

        private fun disableAttribs() {
            GLES20.glDisableVertexAttribArray(locP)
            GLES20.glDisableVertexAttribArray(locSym)
            GLES20.glDisableVertexAttribArray(locM)
            GLES20.glBindBuffer(GLES20.GL_ARRAY_BUFFER, 0)
        }

        private fun hypot2(x: Float, y: Float): Float = sqrt(x * x + y * y)
        private fun kLog2(v: Int): Float = (kotlin.math.ln(max(1, v).toFloat()) / kotlin.math.ln(2f))
    }
}
