package com.swarm.wallpaper

import android.app.WallpaperManager
import android.content.Context
import android.graphics.Bitmap
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Paint
import android.graphics.Typeface
import android.opengl.EGL14
import android.opengl.EGLConfig
import android.opengl.EGLContext
import android.opengl.EGLDisplay
import android.opengl.EGLSurface
import android.opengl.GLES20
import android.opengl.GLUtils
import android.opengl.Matrix
import android.hardware.Sensor
import android.hardware.SensorEvent
import android.hardware.SensorEventListener
import android.hardware.SensorManager
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.os.PowerManager
import android.os.SystemClock
import android.service.wallpaper.WallpaperService
import android.view.MotionEvent
import android.view.VelocityTracker
import android.view.ViewConfiguration
import android.view.SurfaceHolder
import java.nio.ByteBuffer
import java.nio.ByteOrder
import kotlin.math.PI
import kotlin.math.exp
import kotlin.math.abs
import kotlin.math.atan2
import kotlin.math.max
import kotlin.math.sqrt
import kotlin.random.Random

// ───────────────────────── CẤU HÌNH (chỉnh ở đây) ─────────────────────────
private const val G_PARTICLES = 80000     // số hạt, khớp gem80k.html
private const val G_FPS = 30              // fps bình thường
private const val G_FPS_INTERACTION = 60  // 60fps khi vuốt / quán tính / launcher đang scroll
private const val G_FPS_SAVER = 15        // fps khi bật Tiết kiệm pin (khi không tương tác)
private const val G_AUTO_WAVE_MS = 0L  // tự bắn sóng đổi màu mỗi N ms (0 = tắt, chỉ chạm mới đổi)
private const val G_SPARK_N = 0.7f        // độ "nhọn" của hình sparkle
private const val G_SIZE_BOOST = 1.0f     // nhân kích thước ký tự cho dễ nhìn trên màn hình nhỏ
private const val G_SYMBOLS = "⌖⎋⍕⌬⧉⧇⧻⧼⧽"
private const val G_SYMBOLS_FALLBACK = "✦✧◆◇○△□+×"

// Chuyển động: tinh chỉnh nhẹ cho Xperia XZ3 / Snapdragon 845 / màn 2K.
private const val G_TILT_MAX_DEG = 18f          // giới hạn góc parallax do nghiêng máy
private const val G_TILT_GAIN = 0.72f           // độ bám theo trọng lực (đối trọng)
private const val G_TILT_SMOOTH_HZ = 5.0f       // low-pass; thấp hơn = mềm hơn
private const val G_DRAG_DEG_PER_SCREEN = 150f  // vuốt hết bề ngang ~= 150 độ
private const val G_INERTIA_FRICTION = 3.6f     // hãm quán tính (1/s)
private const val G_INERTIA_STOP_DPS = 2.0f     // dưới ngưỡng này coi như dừng
private const val G_AUTO_DELAY_MS = 1100L       // giữ yên bao lâu mới bắt đầu auto rotate
private const val G_AUTO_YAW_DPS = 4.2f         // tự xoay rất nhẹ khi máy đứng yên
private const val G_STILL_TILT_EPS_DEG = 0.18f  // biến thiên tilt nhỏ hơn mức này = gần như yên

private class GWave(var radius: Float, val state: Int)

// ───────────────────────── SHADER ─────────────────────────
// Toàn bộ công thức hình học + màu + sóng từ file HTML gốc, chạy trên GPU.
private const val VERT = """
attribute vec4 aP;        // x=angle, y=rad, z=zOffset, w=speedScale
attribute float aSym;
uniform mat4 uMV;
uniform mat4 uProj;
uniform float uShape;
uniform float uState;
uniform float uPR;
uniform vec4 uWave[4];    // radius, state, width, active
uniform vec3 uCore[4];
uniform vec3 uAccent[4];
varying vec3 vColor;
varying float vSym;

void main() {
    float ang = aP.x;
    float rad = aP.y;
    float ca = cos(ang);
    float sa = sin(ang);
    float e = 2.0 / uShape;
    float o = pow(max(abs(ca), 0.0001), e) * sign(ca);
    float s = pow(max(abs(sa), 0.0001), e) * sign(sa);
    float c2 = cos(2.0 * ang);
    float rounding = 0.18 * c2 * c2;
    float k = 120.0 * (1.0 + rad - 0.04);
    float x = (o * (1.0 - rounding) + ca * rounding) * k;
    float y = (s * (1.0 - rounding) + sa * rounding) * k;
    float z = aP.z * 96.0;
    float dist = max(length(vec3(x, y, z)), 0.001);

    float state = uState;
    float boost = 1.0;
    for (int i = 0; i < 4; i++) {
        vec4 w = uWave[i];
        if (w.w > 0.5) {
            if (dist < w.x) state = w.y;
            float d = abs(dist - w.x);
            if (d < w.z) boost = max(boost, 1.0 + (1.0 - d / w.z) * 2.0);
        }
    }
    int si = int(state + 0.5);
    vec3 col = mix(uCore[si], uAccent[si], rad);
    if (boost > 1.0) col = min(vec3(1.0), col * boost);
    vColor = col;

    float fade = 1.0 - clamp((dist - 40.0) / 220.0, 0.0, 1.0);
    float size = aP.w * (0.8 + fade * 1.8) * (boost > 1.0 ? 1.4 : 1.0);

    vec4 mv = uMV * vec4(x, y, z, 1.0);
    gl_PointSize = size * uPR * (300.0 / -mv.z);
    gl_Position = uProj * mv;
    vSym = aSym;
}
"""

private const val FRAG = """
precision mediump float;
varying vec3 vColor;
varying float vSym;
uniform sampler2D uTex;
uniform float uSymCount;

void main() {
    vec2 uv = gl_PointCoord;
    uv.x = (uv.x + vSym) / uSymCount;
    vec4 t = texture2D(uTex, uv);
    if (t.a < 0.1) discard;
    gl_FragColor = vec4(vColor, t.a);
}
"""

// ───────────────────────── WALLPAPER SERVICE ─────────────────────────
class GeminiWallpaperService : WallpaperService() {

    override fun onCreateEngine(): Engine = GemEngine()

    private inner class GemEngine : Engine() {
        private val handler = Handler(Looper.getMainLooper())
        private val pm = getSystemService(Context.POWER_SERVICE) as PowerManager
        private val pixelRatio = resources.displayMetrics.density.coerceAtMost(2f)
        private val sensorManager = getSystemService(Context.SENSOR_SERVICE) as SensorManager
        private val gravitySensor = sensorManager.getDefaultSensor(Sensor.TYPE_GRAVITY)
            ?: sensorManager.getDefaultSensor(Sensor.TYPE_ACCELEROMETER)
        private val touchSlop = ViewConfiguration.get(this@GeminiWallpaperService).scaledTouchSlop.toFloat()

        private var shown = false
        private var glReady = false

        private var dpy: EGLDisplay = EGL14.EGL_NO_DISPLAY
        private var ctx: EGLContext = EGL14.EGL_NO_CONTEXT
        private var surf: EGLSurface = EGL14.EGL_NO_SURFACE

        private var prog = 0
        private var vbo = 0
        private var tex = 0
        private var locP = 0
        private var locSym = 0
        private var locMV = 0
        private var locProj = 0
        private var locShape = 0
        private var locState = 0
        private var locPR = 0
        private var locWave = 0
        private var locCore = 0
        private var locAccent = 0
        private var locTex = 0
        private var locSymCount = 0
        private var symbolCount = 1

        private var w = 0
        private var h = 0
        private var camZ = 240f
        private val proj = FloatArray(16)
        private val mv = FloatArray(16)

        private var startAt = 0L
        private var lastT = 0L
        private var animTime = 0f
        private var morph = (-PI / 2).toFloat()
        private var stateIndex = 0
        private var lastWaveAt = 0L
        private val waves = ArrayList<GWave>()
        private val waveArr = FloatArray(16)
        private val coreArr = FloatArray(12)
        private val accentArr = FloatArray(12)

        // ── tương tác / cảm biến ──
        private var sensorRegistered = false
        private val gravity = FloatArray(3)
        private var haveGravity = false
        private var lastSensorNs = 0L
        private var tiltPitch = 0f
        private var tiltRoll = 0f
        private var targetPitch = 0f
        private var targetRoll = 0f
        private var lastRawPitch = 0f
        private var lastRawRoll = 0f
        private var lastMotionAt = 0L

        private var touching = false
        private var downX = 0f
        private var downY = 0f
        private var lastTouchX = 0f
        private var lastTouchY = 0f
        private var dragDistance = 0f
        // Hướng xoay do người dùng được tích lũy trực tiếp bằng ma trận 3D.
        // Không còn clamp pitch ±75° nên có thể xoay xuyên qua các cực / lật tự do.
        private val userRotation = FloatArray(16).also { Matrix.setIdentityM(it, 0) }
        private val rotTmp = FloatArray(16)
        private var yawVel = 0f
        private var pitchVel = 0f
        private var velocityTracker: VelocityTracker? = null

        private var lastOffsetX = -1f
        private var lastOffsetAt = 0L
        private var offsetYaw = 0f

        private val sensorListener = object : SensorEventListener {
            override fun onSensorChanged(event: SensorEvent) {
                if (!shown || event.values.size < 3) return
                val nowNs = event.timestamp
                val dt = if (lastSensorNs == 0L) 0.02f else ((nowNs - lastSensorNs) * 1e-9f).coerceIn(0.001f, 0.1f)
                lastSensorNs = nowNs

                // TYPE_GRAVITY đã lọc sẵn. Với accelerometer fallback, low-pass mạnh hơn một chút.
                val a = if (event.sensor.type == Sensor.TYPE_GRAVITY) {
                    1f - exp((-2f * PI.toFloat() * 7f * dt))
                } else {
                    1f - exp((-2f * PI.toFloat() * 3.5f * dt))
                }
                if (!haveGravity) {
                    gravity[0] = event.values[0]; gravity[1] = event.values[1]; gravity[2] = event.values[2]
                    haveGravity = true
                } else {
                    for (i in 0..2) gravity[i] += (event.values[i] - gravity[i]) * a
                }

                // Chỉ cần pitch/roll theo trọng lực. Không dùng compass/yaw để tránh rung và drift.
                val gx = gravity[0]
                val gy = gravity[1]
                val gz = gravity[2]
                val rawRoll = Math.toDegrees(atan2(gx.toDouble(), sqrt((gy * gy + gz * gz).toDouble()))).toFloat()
                val rawPitch = Math.toDegrees(atan2((-gy).toDouble(), sqrt((gx * gx + gz * gz).toDouble()))).toFloat()

                targetRoll = (-rawRoll * G_TILT_GAIN).coerceIn(-G_TILT_MAX_DEG, G_TILT_MAX_DEG)
                targetPitch = (-rawPitch * G_TILT_GAIN).coerceIn(-G_TILT_MAX_DEG, G_TILT_MAX_DEG)

                val moved = abs(rawRoll - lastRawRoll) + abs(rawPitch - lastRawPitch)
                if (moved > G_STILL_TILT_EPS_DEG) lastMotionAt = SystemClock.uptimeMillis()
                lastRawRoll = rawRoll
                lastRawPitch = rawPitch
            }

            override fun onAccuracyChanged(sensor: Sensor?, accuracy: Int) = Unit
        }

        private val loop = object : Runnable {
            override fun run() {
                val t0 = SystemClock.uptimeMillis()
                drawFrame(t0)
                if (shown) {
                    // Khi người dùng đang điều khiển vật thể, ưu tiên độ trễ thấp / chuyển động mượt.
                    // Giữ 60fps xuyên suốt cả pha quán tính; Xperia Home đôi khi chỉ gửi offset
                    // nên coi offset vừa thay đổi trong 180ms là một gesture đang diễn ra.
                    val interactionActive = touching ||
                        abs(yawVel) >= G_INERTIA_STOP_DPS ||
                        abs(pitchVel) >= G_INERTIA_STOP_DPS ||
                        (t0 - lastOffsetAt in 0..180L)
                    val fps = when {
                        interactionActive -> G_FPS_INTERACTION
                        pm.isPowerSaveMode -> G_FPS_SAVER
                        else -> G_FPS
                    }
                    handler.postDelayed(this, max(1L, 1000L / fps - (SystemClock.uptimeMillis() - t0)))
                }
            }
        }

        init {
            fillColors(coreArr, listOf("#00B95C", "#FFCC00", "#FF4641", "#3186FF"))
            fillColors(accentArr, listOf("#00A5B7", "#FF6B2B", "#D8627E", "#A975AA"))
        }

        private fun fillColors(dst: FloatArray, hex: List<String>) {
            hex.forEachIndexed { i, s ->
                val c = Color.parseColor(s)
                dst[i * 3] = Color.red(c) / 255f
                dst[i * 3 + 1] = Color.green(c) / 255f
                dst[i * 3 + 2] = Color.blue(c) / 255f
            }
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
            val aspect = w.toFloat() / h.toFloat()
            // Khớp gem80k.html: PerspectiveCamera(75, aspect, 0.1, 2000), camera.position.z = 240.
            camZ = 240f
            Matrix.perspectiveM(proj, 0, 75f, aspect, 0.1f, 2000f)
        }

        override fun onVisibilityChanged(visible: Boolean) {
            shown = visible
            handler.removeCallbacks(loop)
            if (visible) {
                val now = SystemClock.uptimeMillis()
                startAt = now
                lastT = now
                lastWaveAt = now
                lastMotionAt = now
                registerSensors()
                handler.post(loop)
            } else {
                unregisterSensors()
                velocityTracker?.recycle()
                velocityTracker = null
                touching = false
            }
        }

        private fun registerSensors() {
            if (!sensorRegistered && gravitySensor != null) {
                // GAME delay ~20 ms: đủ mượt ở 30 fps nhưng không ép sensor chạy quá nhanh.
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
            velocityTracker?.recycle()
            velocityTracker = null
            releaseGL()
            super.onDestroy()
        }

        // Orbit/trackball nhẹ: mỗi delta được nhân vào orientation hiện tại.
        // Xoay theo local axes giúp kéo xuyên qua cực vẫn liên tục và kéo chéo tạo cảm giác 3D tự nhiên.
        private fun applyOrbitDelta(yawDeg: Float, pitchDeg: Float) {
            if (yawDeg == 0f && pitchDeg == 0f) return
            if (yawDeg != 0f) Matrix.rotateM(userRotation, 0, yawDeg, 0f, 1f, 0f)
            if (pitchDeg != 0f) Matrix.rotateM(userRotation, 0, pitchDeg, 1f, 0f, 0f)
        }

        // Vuốt → xoay trực tiếp; thả → tiếp tục theo quán tính rồi hãm dần.
        // Tap ngắn vẫn giữ hành vi bắn sóng đổi màu.
        override fun onTouchEvent(event: MotionEvent) {
            velocityTracker?.addMovement(event)
            when (event.actionMasked) {
                MotionEvent.ACTION_DOWN -> {
                    velocityTracker?.recycle()
                    velocityTracker = VelocityTracker.obtain().also { it.addMovement(event) }
                    touching = true
                    downX = event.x
                    downY = event.y
                    lastTouchX = event.x
                    lastTouchY = event.y
                    dragDistance = 0f
                    yawVel = 0f
                    pitchVel = 0f
                    lastMotionAt = SystemClock.uptimeMillis()
                }
                MotionEvent.ACTION_MOVE -> {
                    val dx = event.x - lastTouchX
                    val dy = event.y - lastTouchY
                    dragDistance += sqrt(dx * dx + dy * dy)
                    val sx = max(1, w).toFloat()
                    val sy = max(1, h).toFloat()
                    applyOrbitDelta(
                        dx / sx * G_DRAG_DEG_PER_SCREEN,
                        dy / sy * G_DRAG_DEG_PER_SCREEN
                    )
                    lastTouchX = event.x
                    lastTouchY = event.y
                    lastMotionAt = SystemClock.uptimeMillis()
                }
                MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {
                    val wasTap = dragDistance < touchSlop &&
                        abs(event.x - downX) < touchSlop && abs(event.y - downY) < touchSlop
                    if (event.actionMasked == MotionEvent.ACTION_UP && wasTap) {
                        triggerWave(SystemClock.uptimeMillis())
                    } else {
                        velocityTracker?.computeCurrentVelocity(1000)
                        val sx = max(1, w).toFloat()
                        val sy = max(1, h).toFloat()
                        yawVel = ((velocityTracker?.xVelocity ?: 0f) / sx * G_DRAG_DEG_PER_SCREEN)
                            .coerceIn(-360f, 360f)
                        pitchVel = ((velocityTracker?.yVelocity ?: 0f) / sy * G_DRAG_DEG_PER_SCREEN)
                            .coerceIn(-240f, 240f)
                    }
                    touching = false
                    velocityTracker?.recycle()
                    velocityTracker = null
                    lastMotionAt = SystemClock.uptimeMillis()
                }
            }
            super.onTouchEvent(event)
        }

        // Xperia Home thường giữ gesture vuốt trang cho launcher. Offset là fallback để wallpaper
        // vẫn phản ứng khi người dùng lướt Home, kể cả lúc không nhận được ACTION_MOVE trực tiếp.
        override fun onOffsetsChanged(
            xOffset: Float, yOffset: Float, xOffsetStep: Float, yOffsetStep: Float,
            xPixelOffset: Int, yPixelOffset: Int
        ) {
            val now = SystemClock.uptimeMillis()
            if (!touching && lastOffsetX >= 0f) {
                val dx = xOffset - lastOffsetX
                if (abs(dx) < 0.5f) { // bỏ qua wrap 0 ↔ 1 ở launcher vòng
                    offsetYaw += dx * 75f
                    if (abs(dx) > 0.0005f) {
                        val dt = ((now - lastOffsetAt) / 1000f).coerceIn(0.008f, 0.12f)
                        val v = dx / dt * 75f
                        yawVel = (yawVel * 0.55f + v * 0.45f).coerceIn(-300f, 300f)
                        lastMotionAt = now
                    }
                }
            }
            lastOffsetX = xOffset
            lastOffsetAt = now
            super.onOffsetsChanged(xOffset, yOffset, xOffsetStep, yOffsetStep, xPixelOffset, yPixelOffset)
        }

        override fun onCommand(
            action: String?, x: Int, y: Int, z: Int, extras: Bundle?, resultRequested: Boolean
        ): Bundle? {
            if (action == WallpaperManager.COMMAND_TAP) triggerWave(SystemClock.uptimeMillis())
            return super.onCommand(action, x, y, z, extras, resultRequested)
        }

        private fun triggerWave(now: Long) {
            if (now - lastWaveAt < 300) return
            lastWaveAt = now
            stateIndex = (stateIndex + 1) % 4
            waves.add(GWave(0f, stateIndex))
            if (waves.size > 4) waves.removeAt(0)
        }

        // ── EGL / GL ──
        private fun initEGL(holder: SurfaceHolder): Boolean {
            dpy = EGL14.eglGetDisplay(EGL14.EGL_DEFAULT_DISPLAY)
            if (dpy == EGL14.EGL_NO_DISPLAY) return false
            val ver = IntArray(2)
            if (!EGL14.eglInitialize(dpy, ver, 0, ver, 1)) return false
            val attr = intArrayOf(
                EGL14.EGL_RENDERABLE_TYPE, EGL14.EGL_OPENGL_ES2_BIT,
                EGL14.EGL_RED_SIZE, 8, EGL14.EGL_GREEN_SIZE, 8,
                EGL14.EGL_BLUE_SIZE, 8, EGL14.EGL_ALPHA_SIZE, 8,
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
            val st = IntArray(1)
            GLES20.glGetProgramiv(prog, GLES20.GL_LINK_STATUS, st, 0)
            if (st[0] == 0) return false

            locP = GLES20.glGetAttribLocation(prog, "aP")
            locSym = GLES20.glGetAttribLocation(prog, "aSym")
            locMV = GLES20.glGetUniformLocation(prog, "uMV")
            locProj = GLES20.glGetUniformLocation(prog, "uProj")
            locShape = GLES20.glGetUniformLocation(prog, "uShape")
            locState = GLES20.glGetUniformLocation(prog, "uState")
            locPR = GLES20.glGetUniformLocation(prog, "uPR")
            locWave = GLES20.glGetUniformLocation(prog, "uWave")
            locCore = GLES20.glGetUniformLocation(prog, "uCore")
            locAccent = GLES20.glGetUniformLocation(prog, "uAccent")
            locTex = GLES20.glGetUniformLocation(prog, "uTex")
            locSymCount = GLES20.glGetUniformLocation(prog, "uSymCount")

            val symCount = buildAtlas()
            symbolCount = symCount

            // dữ liệu hạt: angle, rad, zOffset, speed, symbol (5 float / hạt)
            val buf = ByteBuffer.allocateDirect(G_PARTICLES * 5 * 4).order(ByteOrder.nativeOrder()).asFloatBuffer()
            for (i in 0 until G_PARTICLES) {
                val r1 = Random.nextFloat()
                val r5 = r1 * r1 * r1 * r1 * r1
                buf.put((Random.nextFloat() * 2f * PI).toFloat())
                buf.put(r5)
                buf.put(Random.nextFloat() + Random.nextFloat() + Random.nextFloat() - 1.5f)
                buf.put(0.8f + Random.nextFloat() * 1.2f)
                buf.put(Random.nextInt(symCount).toFloat())
            }
            buf.position(0)
            val ids = IntArray(1)
            GLES20.glGenBuffers(1, ids, 0)
            vbo = ids[0]
            GLES20.glBindBuffer(GLES20.GL_ARRAY_BUFFER, vbo)
            GLES20.glBufferData(GLES20.GL_ARRAY_BUFFER, G_PARTICLES * 5 * 4, buf, GLES20.GL_STATIC_DRAW)
            return true
        }

        // atlas ký tự: 16 ô 64px, chỉ dùng ký tự máy có font; thiếu thì dùng bộ dự phòng
        private fun buildAtlas(): Int {
            val p = Paint(Paint.ANTI_ALIAS_FLAG).apply {
                typeface = Typeface.create(Typeface.SERIF, Typeface.BOLD)
                textSize = 42f
                color = Color.WHITE
                textAlign = Paint.Align.CENTER
            }
            var syms = G_SYMBOLS.map { it.toString() }.filter { p.hasGlyph(it) }
            if (syms.isEmpty()) syms = G_SYMBOLS_FALLBACK.map { it.toString() }.filter { p.hasGlyph(it) }
            if (syms.isEmpty()) syms = listOf("+")
            syms = syms.take(16)

            val bmp = Bitmap.createBitmap(syms.size * 64, 64, Bitmap.Config.ARGB_8888)
            val cv = Canvas(bmp)
            val fm = p.fontMetrics
            val baseY = 32f - (fm.ascent + fm.descent) / 2f
            syms.forEachIndexed { i, s -> cv.drawText(s, i * 64f + 32f, baseY, p) }

            val ids = IntArray(1)
            GLES20.glGenTextures(1, ids, 0)
            tex = ids[0]
            GLES20.glBindTexture(GLES20.GL_TEXTURE_2D, tex)
            GLUtils.texImage2D(GLES20.GL_TEXTURE_2D, 0, bmp, 0)
            GLES20.glTexParameteri(GLES20.GL_TEXTURE_2D, GLES20.GL_TEXTURE_MIN_FILTER, GLES20.GL_LINEAR)
            GLES20.glTexParameteri(GLES20.GL_TEXTURE_2D, GLES20.GL_TEXTURE_MAG_FILTER, GLES20.GL_LINEAR)
            GLES20.glTexParameteri(GLES20.GL_TEXTURE_2D, GLES20.GL_TEXTURE_WRAP_S, GLES20.GL_CLAMP_TO_EDGE)
            GLES20.glTexParameteri(GLES20.GL_TEXTURE_2D, GLES20.GL_TEXTURE_WRAP_T, GLES20.GL_CLAMP_TO_EDGE)
            bmp.recycle()
            return syms.size
        }

        private fun releaseGL() {
            try {
                if (dpy != EGL14.EGL_NO_DISPLAY) {
                    if (glReady && ctx != EGL14.EGL_NO_CONTEXT && surf != EGL14.EGL_NO_SURFACE) {
                        EGL14.eglMakeCurrent(dpy, surf, surf, ctx)
                        GLES20.glDeleteBuffers(1, intArrayOf(vbo), 0)
                        GLES20.glDeleteTextures(1, intArrayOf(tex), 0)
                        GLES20.glDeleteProgram(prog)
                    }
                    EGL14.eglMakeCurrent(dpy, EGL14.EGL_NO_SURFACE, EGL14.EGL_NO_SURFACE, EGL14.EGL_NO_CONTEXT)
                    if (surf != EGL14.EGL_NO_SURFACE) EGL14.eglDestroySurface(dpy, surf)
                    if (ctx != EGL14.EGL_NO_CONTEXT) EGL14.eglDestroyContext(dpy, ctx)
                }
            } catch (e: Exception) {
                // bỏ qua
            }
            surf = EGL14.EGL_NO_SURFACE
            ctx = EGL14.EGL_NO_CONTEXT
            glReady = false
        }

        // ── khung hình ──
        private fun drawFrame(now: Long) {
            if (!glReady || w == 0) return
            try {
                val dt = ((now - lastT) / 1000f).coerceIn(0f, 0.1f)
                lastT = now
                animTime += dt
                morph += dt * 0.5f

                // Tilt low-pass ở nhịp render để không phụ thuộc tần số sensor.
                val tiltA = 1f - exp((-2f * PI.toFloat() * G_TILT_SMOOTH_HZ * dt))
                tiltPitch += (targetPitch - tiltPitch) * tiltA
                tiltRoll += (targetRoll - tiltRoll) * tiltA

                // Quán tính gesture: tiếp tục xoay trên chính orientation hiện tại rồi hãm dần.
                // Vì tích lũy bằng ma trận nên không có điểm gãy ±90° như Euler pitch/yaw.
                if (!touching) {
                    if (yawVel != 0f || pitchVel != 0f) {
                        applyOrbitDelta(yawVel * dt, pitchVel * dt)
                    }
                    val damp = exp(-G_INERTIA_FRICTION * dt)
                    yawVel *= damp
                    pitchVel *= damp
                    if (abs(yawVel) < G_INERTIA_STOP_DPS) yawVel = 0f
                    if (abs(pitchVel) < G_INERTIA_STOP_DPS) pitchVel = 0f
                }

                val inertial = abs(yawVel) + abs(pitchVel) > G_INERTIA_STOP_DPS * 1.5f

                if (G_AUTO_WAVE_MS > 0 && now - lastWaveAt > G_AUTO_WAVE_MS) triggerWave(now)

                val iter = waves.iterator()
                while (iter.hasNext()) {
                    val wv = iter.next()
                    wv.radius += dt * 650f
                    if (wv.radius >= 1200f) iter.remove()
                }

                // xuất hiện dần: trễ 0.5s rồi lerp 5%/16ms như bản gốc
                val te = (now - startAt) / 1000f - 0.5f
                val scale = if (te <= 0f) 0f else 1f - exp(-3.2f * te)

                if (!EGL14.eglMakeCurrent(dpy, surf, surf, ctx)) return
                GLES20.glViewport(0, 0, w, h)
                GLES20.glClearColor(0f, 0f, 0f, 1f)
                GLES20.glClear(GLES20.GL_COLOR_BUFFER_BIT)

                if (scale > 0.001f) {
                    // Hologram + free orbit:
                    // 1) tilt/launcher offset là lớp tham chiếu theo thiết bị / Home;
                    // 2) userRotation là orientation 3D tự do do vuốt + quán tính tích lũy.
                    Matrix.setIdentityM(mv, 0)
                    Matrix.translateM(mv, 0, 0f, 0f, -camZ)
                    Matrix.rotateM(mv, 0, tiltPitch, 1f, 0f, 0f)
                    Matrix.rotateM(mv, 0, tiltRoll + offsetYaw, 0f, 1f, 0f)
                    Matrix.rotateM(mv, 0, -tiltRoll * 0.20f, 0f, 0f, 1f)

                    // Chuyển động nền bám gem80k.html:
                    // r = animTime * 0.25
                    // rotX = sin(2r)^3 * 0.4 rad
                    // rotY = sin(r)^3 * 0.6 rad
                    // rotZ = sin(r)^3 * -0.3 rad
                    val r = animTime * 0.25f
                    val sr = kotlin.math.sin(r)
                    val s2r = kotlin.math.sin(r * 2f)
                    val baseRotX = s2r * s2r * s2r * 0.4f * (180f / PI.toFloat())
                    val baseRotY = sr * sr * sr * 0.6f * (180f / PI.toFloat())
                    val baseRotZ = sr * sr * sr * -0.3f * (180f / PI.toFloat())
                    Matrix.rotateM(mv, 0, baseRotX, 1f, 0f, 0f)
                    Matrix.rotateM(mv, 0, baseRotY, 0f, 1f, 0f)
                    Matrix.rotateM(mv, 0, baseRotZ, 0f, 0f, 1f)

                    Matrix.multiplyMM(rotTmp, 0, mv, 0, userRotation, 0)
                    System.arraycopy(rotTmp, 0, mv, 0, 16)
                    Matrix.scaleM(mv, 0, scale, scale, scale)

                    val shape = (3.5f + G_SPARK_N) / 2f +
                        ((3.5f - G_SPARK_N) / 2f) * kotlin.math.sin(morph)

                    java.util.Arrays.fill(waveArr, 0f)
                    for (i in 0 until waves.size) {
                        waveArr[i * 4] = waves[i].radius
                        waveArr[i * 4 + 1] = waves[i].state.toFloat()
                        waveArr[i * 4 + 2] = 80f
                        waveArr[i * 4 + 3] = 1f
                    }

                    GLES20.glUseProgram(prog)
                    GLES20.glUniformMatrix4fv(locMV, 1, false, mv, 0)
                    GLES20.glUniformMatrix4fv(locProj, 1, false, proj, 0)
                    GLES20.glUniform1f(locShape, shape)
                    GLES20.glUniform1f(locState, stateIndex.toFloat())
                    GLES20.glUniform1f(locPR, pixelRatio * G_SIZE_BOOST)
                    GLES20.glUniform4fv(locWave, 4, waveArr, 0)
                    GLES20.glUniform3fv(locCore, 4, coreArr, 0)
                    GLES20.glUniform3fv(locAccent, 4, accentArr, 0)

                    GLES20.glActiveTexture(GLES20.GL_TEXTURE0)
                    GLES20.glBindTexture(GLES20.GL_TEXTURE_2D, tex)
                    GLES20.glUniform1i(locTex, 0)
                    GLES20.glUniform1f(locSymCount, symbolCount.toFloat())

                    GLES20.glEnable(GLES20.GL_BLEND)
                    GLES20.glBlendFuncSeparate(
                        GLES20.GL_SRC_ALPHA, GLES20.GL_ONE, GLES20.GL_ZERO, GLES20.GL_ONE
                    )

                    GLES20.glBindBuffer(GLES20.GL_ARRAY_BUFFER, vbo)
                    GLES20.glEnableVertexAttribArray(locP)
                    GLES20.glVertexAttribPointer(locP, 4, GLES20.GL_FLOAT, false, 20, 0)
                    GLES20.glEnableVertexAttribArray(locSym)
                    GLES20.glVertexAttribPointer(locSym, 1, GLES20.GL_FLOAT, false, 20, 16)
                    GLES20.glDrawArrays(GLES20.GL_POINTS, 0, G_PARTICLES)
                    GLES20.glDisableVertexAttribArray(locP)
                    GLES20.glDisableVertexAttribArray(locSym)
                }

                EGL14.eglSwapBuffers(dpy, surf)
            } catch (e: Exception) {
                // bỏ qua khung lỗi
            }
        }
    }
}
