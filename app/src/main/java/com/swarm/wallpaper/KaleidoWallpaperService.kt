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
import kotlin.math.PI
import kotlin.math.cos
import kotlin.math.exp
import kotlin.math.max
import kotlin.math.sin
import kotlin.math.sqrt
import kotlin.random.Random

// ───────────────────────── CẤU HÌNH (chỉnh ở đây) ─────────────────────────
private const val G_STRUCTURE = 45000     // số hạt dựng hình mandala
private const val G_SPARKS = 9000         // số tàn lửa
private const val G_FPS = 60              // fps bình thường
private const val G_FPS_SAVER = 15        // fps khi bật Tiết kiệm pin
private const val G_AUTO_WAVE_MS = 8000L  // tự bắn sóng đổi màu mỗi N ms (0 = tắt, chỉ chạm mới đổi)
private const val G_SPARK_N = 0.7f        // (dự phòng, không dùng cho mandala)
private const val G_SIZE_BOOST = 1.0f     // (mặc định) nhân kích thước ký tự
private const val G_R = 120f              // bán kính mandala (world units)
private const val G_SYMBOLS = "ᚠᚢᚦᚨᚱᚲᚷᚹᚺᚾᛁᛃᛇᛈᛉᛋᛏ"
private const val G_SYMBOLS_FALLBACK = "✦✧◆◇○△□+×"

private class KWave(var radius: Float, val state: Int)

// ───────────────────────── SHADER ─────────────────────────
// Toàn bộ công thức hình học + màu + sóng từ file HTML gốc, chạy trên GPU.
private const val VERT = """
attribute vec3 aPos;      // vị trí gốc (x, y, z)
attribute vec4 aData;     // layer, size, alpha, colorMix
attribute float aSym;
uniform mat4 uMV;
uniform mat4 uProj;
uniform float uPR;
uniform vec4 uLayers;     // góc quay cho 4 lớp
uniform float uScale;
uniform vec3 uCore;       // màu chính (rìa)
uniform vec3 uAccent;     // màu lõi (trung tâm)
uniform vec4 uWave[4];    // radius, width, active, unused
uniform vec4 uHover;      // x, y, z, radius (radius < 0 = tắt)
varying vec3 vColor;
varying float vAlpha;
varying float vSym;

void main() {
    int li = int(aData.x + 0.5);
    float ang = 0.0;
    if (li == 0) ang = uLayers.x;
    else if (li == 1) ang = uLayers.y;
    else if (li == 2) ang = uLayers.z;
    else if (li == 3) ang = uLayers.w;

    float ca = cos(ang);
    float sa = sin(ang);
    vec2 rot = vec2(aPos.x * ca - aPos.y * sa, aPos.x * sa + aPos.y * ca);

    vec3 p;
    p.x = rot.x * uScale;
    p.y = rot.y * uScale;
    p.z = aPos.z * uScale;

    float rad = length(rot) * uScale;

    float boost = 1.0;
    for (int i = 0; i < 4; i++) {
        vec4 wv = uWave[i];
        if (wv.z > 0.5) {
            float d = abs(rad - wv.x);
            if (d < wv.y) boost = max(boost, 1.0 + (1.0 - d / wv.y) * 2.4);
        }
    }
    if (uHover.w > 0.0) {
        float dh = length(p - uHover.xyz);
        if (dh < uHover.w) boost = max(boost, 1.0 + (1.0 - dh / uHover.w) * 1.9);
    }

    vec3 col = mix(uCore, uAccent, aData.w);
    if (boost > 1.0) {
        float k = boost - 1.0;
        col = min(vec3(1.0), col * boost + k * 0.28);
    }
    vColor = col;
    vAlpha = aData.z * clamp(uScale * 1.2, 0.0, 1.0);
    vSym = aSym;

    vec4 mv = uMV * vec4(p, 1.0);
    float szMul = (boost > 1.0) ? (1.0 + (boost - 1.0) * 0.45) : 1.0;
    gl_PointSize = aData.y * uPR * (300.0 / -mv.z) * szMul;
    gl_Position = uProj * mv;
}
"""

private const val FRAG = """
precision mediump float;
varying vec3 vColor;
varying float vAlpha;
varying float vSym;
uniform sampler2D uTex;

void main() {
    vec2 uv = gl_PointCoord;
    uv.x = (uv.x + vSym) / 16.0;
    vec4 t = texture2D(uTex, uv);
    if (t.a < 0.12) discard;
    gl_FragColor = vec4(vColor, t.a * vAlpha);
}
"""

// ───────────────────────── WALLPAPER SERVICE ─────────────────────────
class KaleidoWallpaperService : WallpaperService() {

    override fun onCreateEngine(): Engine = GemEngine()

    private inner class GemEngine : Engine() {
        private val handler = Handler(Looper.getMainLooper())
        private val pm = getSystemService(Context.POWER_SERVICE) as PowerManager
        private val pixelRatio = resources.displayMetrics.density

        private var shown = false
        private var glReady = false

        private var dpy: EGLDisplay = EGL14.EGL_NO_DISPLAY
        private var ctx: EGLContext = EGL14.EGL_NO_CONTEXT
        private var surf: EGLSurface = EGL14.EGL_NO_SURFACE

        private var prog = 0
        private var structVbo = 0
        private var sparkVbo = 0
        private var tex = 0
        private var locPos = 0
        private var locData = 0
        private var locSym = 0
        private var locMV = 0
        private var locProj = 0
        private var locPR = 0
        private var locLayers = 0
        private var locScale = 0
        private var locCore = 0
        private var locAccent = 0
        private var locWave = 0
        private var locHover = 0
        private var locTex = 0

        private var glyphCount = 16

        // trạng thái hoạt ảnh mandala
        private val layerAngles = FloatArray(4)
        private val spinFactors = floatArrayOf(0.20f, -0.35f, 0.50f, -0.70f)
        private var reveal = 0f

        // tàn lửa
        private val spAngle = FloatArray(G_SPARKS)
        private val spRad = FloatArray(G_SPARKS)
        private val spSpeed = FloatArray(G_SPARKS)
        private val spSpin = FloatArray(G_SPARKS)
        private val spZ = FloatArray(G_SPARKS)
        private val spBase = FloatArray(G_SPARKS)
        private val spSym = FloatArray(G_SPARKS)
        private val sparkBuf = ByteBuffer.allocateDirect(G_SPARKS * 8 * 4)
            .order(ByteOrder.nativeOrder()).asFloatBuffer()

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

        // ── thông số chỉnh bằng gesture (mặc định lấy từ hằng số ở trên) ──
        private var sizeBoost = G_SIZE_BOOST
        private var sparkN = G_SPARK_N
        private var rotSpeed = 1f
        private var waveSpeed = 1f
        private var camZoom = 1f
        private var autoWaveMs = G_AUTO_WAVE_MS

        // ── gesture state machine: 0=rảnh, 1=1 ngón, 2=2 ngón, 3=3 ngón ──
        private var gestureMode = 0
        private var gLastX = 0f
        private var gLastY = 0f
        private var gLastDist = 0f
        private var gDownAt = 0L
        private var gMoved = 0f

        private val waves = ArrayList<KWave>()
        private val waveArr = FloatArray(16)
        private val coreArr = FloatArray(12)
        private val accentArr = FloatArray(12)

        private val loop = object : Runnable {
            override fun run() {
                val t0 = SystemClock.uptimeMillis()
                drawFrame(t0)
                if (shown) {
                    val fps = if (pm.isPowerSaveMode) G_FPS_SAVER else G_FPS
                    handler.postDelayed(this, max(1L, 1000L / fps - (SystemClock.uptimeMillis() - t0)))
                }
            }
        }

        init {
            // coreArr = màu chính (rìa), accentArr = màu lõi (trung tâm)
            fillColors(coreArr, listOf("#ff7b00", "#e52121", "#00cc99", "#1e70e5"))
            fillColors(accentArr, listOf("#ffa600", "#ff6b6b", "#66ffcc", "#6ba2ff"))
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
            // vừa khít chiều ngang màn hình dọc
            camZ = max(240f, 170f / (0.767f * aspect))
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
                reveal = 0f
                handler.post(loop)
            }
        }

        override fun onSurfaceDestroyed(holder: SurfaceHolder) {
            shown = false
            handler.removeCallbacks(loop)
            releaseGL()
            super.onSurfaceDestroyed(holder)
        }

        override fun onDestroy() {
            shown = false
            handler.removeCallbacks(loop)
            releaseGL()
            super.onDestroy()
        }

        // ── gesture state machine: vuốt 1/2/3 ngón để chỉnh thông số ──
        //  1 ngón dọc     → kích thước hạt (sizeBoost)
        //  1 ngón ngang   → độ nhọn sparkle (sparkN)
        //  2 ngón dọc     → tốc độ xoay tổng thể (rotSpeed)
        //  2 ngón ngang   → tốc độ lan sóng màu (waveSpeed)
        //  2 ngón chụm/mở → zoom camera (camZoom)
        //  3 ngón dọc     → chu kỳ tự bắn sóng đổi màu (autoWaveMs, 0 = tắt)
        //  tap 1 ngón     → bắn sóng đổi màu
        //  tap 3 ngón     → reset về giá trị mặc định
        override fun onTouchEvent(event: MotionEvent) {
            when (event.actionMasked) {
                MotionEvent.ACTION_DOWN -> {
                    gestureMode = 1
                    beginGesture(event)
                }
                MotionEvent.ACTION_POINTER_DOWN -> {
                    gestureMode = when {
                        event.pointerCount >= 3 -> 3
                        event.pointerCount == 2 -> 2
                        else -> 1
                    }
                    beginGesture(event)
                }
                MotionEvent.ACTION_POINTER_UP -> {
                    gestureMode = when {
                        event.pointerCount - 1 >= 3 -> 3
                        event.pointerCount - 1 == 2 -> 2
                        event.pointerCount - 1 == 1 -> 1
                        else -> 0
                    }
                    beginGesture(event)
                }
                MotionEvent.ACTION_MOVE -> handleMove(event)
                MotionEvent.ACTION_UP -> {
                    val quick = SystemClock.uptimeMillis() - gDownAt < 300L
                    val tap = gMoved < 20f
                    when {
                        gestureMode == 1 && quick && tap -> triggerWave(SystemClock.uptimeMillis())
                        gestureMode == 3 && quick && tap -> resetParams()
                    }
                    gestureMode = 0
                }
                MotionEvent.ACTION_CANCEL -> gestureMode = 0
            }
            super.onTouchEvent(event)
        }

        private fun beginGesture(event: MotionEvent) {
            gLastX = avgX(event)
            gLastY = avgY(event)
            gLastDist = spread(event)
            if (event.actionMasked == MotionEvent.ACTION_DOWN) {
                gDownAt = SystemClock.uptimeMillis()
                gMoved = 0f
            }
        }

        private fun handleMove(event: MotionEvent) {
            if (gestureMode == 0) return
            val x = avgX(event)
            val y = avgY(event)
            val dx = x - gLastX
            val dy = y - gLastY
            val dist = spread(event)
            val dDist = if (gLastDist > 0f && dist > 0f) dist - gLastDist else 0f

            when (gestureMode) {
                1 -> {
                    if (kotlin.math.abs(dx) > kotlin.math.abs(dy)) {
                        sparkN = (sparkN + dx * 0.004f).coerceIn(0f, 1.5f)
                    } else {
                        sizeBoost = (sizeBoost - dy * 0.006f).coerceIn(0.4f, 4.0f)
                    }
                    gMoved += kotlin.math.abs(dx) + kotlin.math.abs(dy)
                }
                2 -> {
                    val dragMag = kotlin.math.abs(dx) + kotlin.math.abs(dy)
                    if (kotlin.math.abs(dDist) > dragMag * 1.2f && gLastDist > 1f && dist > 1f) {
                        camZoom = (camZoom * (gLastDist / dist)).coerceIn(0.4f, 3.0f)
                    } else if (kotlin.math.abs(dx) > kotlin.math.abs(dy)) {
                        waveSpeed = (waveSpeed + dx * 0.004f).coerceIn(0.1f, 5.0f)
                    } else {
                        rotSpeed = (rotSpeed - dy * 0.005f).coerceIn(0f, 4.0f)
                    }
                    gMoved += dragMag
                }
                3 -> {
                    autoWaveMs = (autoWaveMs - (dy * 30f).toLong()).coerceIn(0L, 20000L)
                    gMoved += kotlin.math.abs(dy)
                }
            }

            gLastX = x
            gLastY = y
            gLastDist = dist
        }

        private fun resetParams() {
            sizeBoost = G_SIZE_BOOST
            sparkN = G_SPARK_N
            rotSpeed = 1f
            waveSpeed = 1f
            camZoom = 1f
            autoWaveMs = G_AUTO_WAVE_MS
        }

        private fun avgX(e: MotionEvent): Float {
            val skip = if (e.actionMasked == MotionEvent.ACTION_POINTER_UP) e.actionIndex else -1
            var s = 0f
            var n = 0
            for (i in 0 until e.pointerCount) {
                if (i == skip) continue
                s += e.getX(i); n++
            }
            return if (n == 0) 0f else s / n
        }

        private fun avgY(e: MotionEvent): Float {
            val skip = if (e.actionMasked == MotionEvent.ACTION_POINTER_UP) e.actionIndex else -1
            var s = 0f
            var n = 0
            for (i in 0 until e.pointerCount) {
                if (i == skip) continue
                s += e.getY(i); n++
            }
            return if (n == 0) 0f else s / n
        }

        private fun spread(e: MotionEvent): Float {
            val skip = if (e.actionMasked == MotionEvent.ACTION_POINTER_UP) e.actionIndex else -1
            var i0 = -1
            var i1 = -1
            for (i in 0 until e.pointerCount) {
                if (i == skip) continue
                if (i0 < 0) i0 = i else if (i1 < 0) { i1 = i; break }
            }
            if (i0 < 0 || i1 < 0) return 0f
            val dx = e.getX(i0) - e.getX(i1)
            val dy = e.getY(i0) - e.getY(i1)
            return kotlin.math.sqrt(dx * dx + dy * dy)
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
            waves.add(KWave(0f, stateIndex))
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

            locPos = GLES20.glGetAttribLocation(prog, "aPos")
            locData = GLES20.glGetAttribLocation(prog, "aData")
            locSym = GLES20.glGetAttribLocation(prog, "aSym")
            locMV = GLES20.glGetUniformLocation(prog, "uMV")
            locProj = GLES20.glGetUniformLocation(prog, "uProj")
            locPR = GLES20.glGetUniformLocation(prog, "uPR")
            locLayers = GLES20.glGetUniformLocation(prog, "uLayers")
            locScale = GLES20.glGetUniformLocation(prog, "uScale")
            locCore = GLES20.glGetUniformLocation(prog, "uCore")
            locAccent = GLES20.glGetUniformLocation(prog, "uAccent")
            locWave = GLES20.glGetUniformLocation(prog, "uWave")
            locHover = GLES20.glGetUniformLocation(prog, "uHover")
            locTex = GLES20.glGetUniformLocation(prog, "uTex")

            glyphCount = buildAtlas().coerceAtLeast(1)

            // ---- structure VBO: aPos(3) + aData(4) + aSym(1) = 8 float ----
            val structData = buildStructure()
            val ids = IntArray(1)
            GLES20.glGenBuffers(1, ids, 0)
            structVbo = ids[0]
            GLES20.glBindBuffer(GLES20.GL_ARRAY_BUFFER, structVbo)
            val sbuf = ByteBuffer.allocateDirect(G_STRUCTURE * 8 * 4)
                .order(ByteOrder.nativeOrder()).asFloatBuffer()
            sbuf.put(structData); sbuf.position(0)
            GLES20.glBufferData(GLES20.GL_ARRAY_BUFFER, G_STRUCTURE * 8 * 4, sbuf, GLES20.GL_STATIC_DRAW)

            // ---- spark VBO (dynamic) ----
            GLES20.glGenBuffers(1, ids, 0)
            sparkVbo = ids[0]
            GLES20.glBindBuffer(GLES20.GL_ARRAY_BUFFER, sparkVbo)
            GLES20.glBufferData(GLES20.GL_ARRAY_BUFFER, G_SPARKS * 8 * 4, null, GLES20.GL_DYNAMIC_DRAW)

            initSparks()
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

        // ── dựng hình mandala ──
        private class MPoly(val pts: FloatArray, val cum: FloatArray, val len: Float) {}

        private class MShape(
            val layer: Int, val weight: Float, val size: Float, val alpha: Float,
            val jitter: Float, val z: Float, val zj: Float, val disc: Float,
            val polys: List<MPoly>, val total: Float
        ) {}

        private fun circlePoly(radius: Float, segments: Int): FloatArray {
            val a = FloatArray(segments * 2)
            for (i in 0 until segments) {
                val t = i.toFloat() / segments * 2f * PI.toFloat()
                a[i * 2] = cos(t) * radius
                a[i * 2 + 1] = sin(t) * radius
            }
            return a
        }

        private fun starPoly(points: Int, outer: Float, inner: Float, phase: Float): FloatArray {
            val n = points * 2
            val a = FloatArray(n * 2)
            for (i in 0 until n) {
                val r = if (i % 2 == 0) outer else inner
                val t = i.toFloat() / n * 2f * PI.toFloat() + phase
                a[i * 2] = cos(t) * r
                a[i * 2 + 1] = sin(t) * r
            }
            return a
        }

        private fun squarePoly(half: Float, angle: Float): FloatArray {
            val c = cos(angle); val s = sin(angle)
            val cx = floatArrayOf(-half, -half, half, -half, half, half, -half, half)
            val out = FloatArray(8)
            for (i in 0 until 4) {
                val x = cx[i * 2]; val y = cx[i * 2 + 1]
                out[i * 2] = x * c - y * s
                out[i * 2 + 1] = x * s + y * c
            }
            return out
        }

        private fun preparePolys(polys: List<FloatArray>): Pair<List<MPoly>, Float> {
            val out = ArrayList<MPoly>()
            var total = 0f
            for (src in polys) {
                val n = src.size / 2
                val cum = FloatArray(n + 1)
                var len = 0f
                for (i in 0 until n) {
                    val ax = src[i * 2]; val ay = src[i * 2 + 1]
                    val j = (i + 1) % n
                    val bx = src[j * 2]; val by = src[j * 2 + 1]
                    val dx = bx - ax; val dy = by - ay
                    len += sqrt(dx * dx + dy * dy)
                    cum[i + 1] = len
                }
                out.add(MPoly(src, cum, len))
                total += len
            }
            return Pair(out, total)
        }

        private fun buildStructure(): FloatArray {
            val R = G_R
            val defs = ArrayList<MShape>()

            fun addPolys(
                layer: Int, weight: Float, size: Float, alpha: Float,
                jitter: Float, z: Float, zj: Float, polys: List<FloatArray>
            ) {
                val (ps, total) = preparePolys(polys)
                defs.add(MShape(layer, weight, size, alpha, jitter, z, zj, 0f, ps, total))
            }
            fun addDisc(
                layer: Int, weight: Float, size: Float, alpha: Float,
                jitter: Float, z: Float, zj: Float, disc: Float
            ) {
                defs.add(MShape(layer, weight, size, alpha, jitter, z, zj, disc, emptyList(), 0f))
            }

            addPolys(0, 0.130f, 2.2f, 0.13f, 0.055f, 0f, 6f, listOf(circlePoly(1.05f * R, 80)))
            addPolys(0, 0.050f, 2.6f, 0.30f, 0.004f, 0f, 3f, listOf(circlePoly(1.00f * R, 100)))
            addPolys(0, 0.045f, 2.6f, 0.28f, 0.004f, 0f, 3f, listOf(circlePoly(0.92f * R, 100)))
            addPolys(0, 0.075f, 7.0f, 0.55f, 0.002f, 0f, 2f, listOf(circlePoly(0.962f * R, 100)))
            addPolys(1, 0.170f, 2.9f, 0.32f, 0.005f, -5f, 3f,
                listOf(starPoly(8, 0.86f * R, 0.60f * R, PI.toFloat() / 2f)))
            addPolys(1, 0.050f, 2.6f, 0.28f, 0.004f, -5f, 3f, listOf(circlePoly(0.60f * R, 80)))
            addPolys(2, 0.190f, 2.9f, 0.32f, 0.005f, 5f, 3f,
                listOf(starPoly(12, 0.72f * R, 0.52f * R, 0f)))
            addPolys(2, 0.040f, 2.5f, 0.26f, 0.004f, 5f, 3f, listOf(circlePoly(0.48f * R, 80)))
            addPolys(3, 0.130f, 2.7f, 0.30f, 0.005f, 10f, 4f, listOf(
                squarePoly(0.30f * R, 0f),
                squarePoly(0.30f * R, PI.toFloat() / 6f),
                squarePoly(0.30f * R, 2f * PI.toFloat() / 6f),
                squarePoly(0.30f * R, 3f * PI.toFloat() / 6f)
            ))
            addDisc(3, 0.060f, 3.0f, 0.30f, 0f, 0f, 4f, 0.15f)

            var weightSum = 0f
            for (d in defs) weightSum += d.weight
            val slots = ArrayList<Int>()
            for (i in defs.indices) {
                val cnt = max(1, (defs[i].weight / weightSum * 2048f).toInt())
                repeat(cnt) { slots.add(i) }
            }
            val slotCount = slots.size

            val out = FloatArray(G_STRUCTURE * 8)
            for (i in 0 until G_STRUCTURE) {
                val P = defs[slots[Random.nextInt(slotCount)]]
                val bx: Float
                val by: Float

                if (P.disc > 0f) {
                    val a = Random.nextFloat() * 2f * PI.toFloat()
                    val rr = sqrt(Random.nextFloat()) * P.disc * R
                    bx = cos(a) * rr
                    by = sin(a) * rr
                } else {
                    var t = Random.nextFloat() * P.total
                    var poly = P.polys.last()
                    for (p in P.polys) {
                        if (t <= p.len) { poly = p; break }
                        t -= p.len
                    }
                    var lo = 0
                    var hi = poly.cum.size - 1
                    while (hi - lo > 1) {
                        val mid = (lo + hi) / 2
                        if (poly.cum[mid] <= t) lo = mid else hi = mid
                    }
                    val segLen = if (poly.cum[lo + 1] - poly.cum[lo] > 0f)
                        poly.cum[lo + 1] - poly.cum[lo] else 1f
                    val f = (t - poly.cum[lo]) / segLen
                    val n = poly.pts.size / 2
                    val i0 = lo
                    val i1 = (lo + 1) % n
                    val x0 = poly.pts[i0 * 2]; val y0 = poly.pts[i0 * 2 + 1]
                    val x1 = poly.pts[i1 * 2]; val y1 = poly.pts[i1 * 2 + 1]
                    var x = x0 + (x1 - x0) * f
                    var y = y0 + (y1 - y0) * f
                    val ja = Random.nextFloat() * 2f * PI.toFloat()
                    val jr = (Random.nextFloat() * 0.5f + Random.nextFloat() * 0.5f) * P.jitter * R
                    x += cos(ja) * jr
                    y += sin(ja) * jr
                    bx = x; by = y
                }

                val bz = P.z + (Random.nextFloat() - 0.5f) * P.zj
                val rad = sqrt(bx * bx + by * by)
                val cMix = Math.pow(max(0f, 1f - rad / R).toDouble(), 1.5).toFloat()
                val sz = P.size * (0.70f + Random.nextFloat() * 0.60f)
                val al = P.alpha * (0.65f + Random.nextFloat() * 0.70f)
                val sym = Random.nextInt(glyphCount).toFloat()

                val o = i * 8
                out[o] = bx; out[o + 1] = by; out[o + 2] = bz
                out[o + 3] = P.layer.toFloat()
                out[o + 4] = sz
                out[o + 5] = al
                out[o + 6] = cMix
                out[o + 7] = sym
            }
            return out
        }

        // ── tàn lửa ──
        private fun initSparks() {
            for (i in 0 until G_SPARKS) {
                spSym[i] = Random.nextInt(glyphCount).toFloat()
                spBase[i] = 2.0f + Random.nextFloat() * 4.5f
                spZ[i] = (Random.nextFloat() - 0.5f) * 40f
                respawnSpark(i, true)
            }
        }

        private fun respawnSpark(i: Int, warm: Boolean) {
            spAngle[i] = Random.nextFloat() * 2f * PI.toFloat()
            spRad[i] = if (warm) (0.05f + Random.nextFloat() * 1.15f)
            else (0.04f + Random.nextFloat() * 0.10f)
            spSpeed[i] = 0.14f + Random.nextFloat() * 0.38f
            spSpin[i] = (Random.nextFloat() - 0.5f) * 2.6f
        }

        private fun updateSparks(dt: Float, ease: Float, scaleR: Float) {
            val R = G_R
            sparkBuf.clear()
            for (i in 0 until G_SPARKS) {
                spRad[i] += spSpeed[i] * dt
                spAngle[i] += spSpin[i] * dt
                if (spRad[i] > 1.28f) respawnSpark(i, false)

                val r = spRad[i]
                val a = spAngle[i]
                val rr = r * R * scaleR
                val x = cos(a) * rr
                val y = sin(a) * rr
                val z = spZ[i] * scaleR

                var t = (r - 0.04f) / 1.24f
                if (t < 0f) t = 0f else if (t > 1f) t = 1f
                val fade = sin(PI.toFloat() * t)
                val cMix = 1f - t * 0.65f

                sparkBuf.put(x)
                sparkBuf.put(y)
                sparkBuf.put(z)
                sparkBuf.put(4f)   // layer = 4 → không xoay
                sparkBuf.put(spBase[i] * fade * (0.4f + 0.6f * ease))
                sparkBuf.put(0.85f * fade * ease)
                sparkBuf.put(cMix)
                sparkBuf.put(spSym[i])
            }
            sparkBuf.position(0)
            GLES20.glBindBuffer(GLES20.GL_ARRAY_BUFFER, sparkVbo)
            GLES20.glBufferSubData(GLES20.GL_ARRAY_BUFFER, 0, G_SPARKS * 8 * 4, sparkBuf)
        }

        private fun releaseGL() {
            try {
                if (dpy != EGL14.EGL_NO_DISPLAY) {
                    if (glReady && ctx != EGL14.EGL_NO_CONTEXT && surf != EGL14.EGL_NO_SURFACE) {
                        EGL14.eglMakeCurrent(dpy, surf, surf, ctx)
                        GLES20.glDeleteBuffers(1, intArrayOf(structVbo), 0)
                        GLES20.glDeleteBuffers(1, intArrayOf(sparkVbo), 0)
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

                // hoạt ảnh xuất hiện (ease smoothstep)
                reveal = (reveal + dt * 0.85f).coerceAtMost(1f)
                val ease = reveal * reveal * (3f - 2f * reveal)
                val breathe = 1f + 0.015f * sin(animTime * 1.6f)
                val scaleR = ease * breathe

                for (l in 0 until 4) layerAngles[l] += rotSpeed * spinFactors[l] * dt

                if (autoWaveMs > 0 && now - lastWaveAt > autoWaveMs) triggerWave(now)

                val iter = waves.iterator()
                while (iter.hasNext()) {
                    val wv = iter.next()
                    wv.radius += dt * 620f * waveSpeed
                    if (wv.radius >= G_R * 1.8f) iter.remove()
                }

                if (!EGL14.eglMakeCurrent(dpy, surf, surf, ctx)) return
                GLES20.glViewport(0, 0, w, h)
                GLES20.glClearColor(0f, 0f, 0f, 1f)
                GLES20.glClear(GLES20.GL_COLOR_BUFFER_BIT)

                Matrix.setIdentityM(mv, 0)
                Matrix.translateM(mv, 0, 0f, 0f, -camZ * camZoom)

                GLES20.glUseProgram(prog)
                GLES20.glUniformMatrix4fv(locMV, 1, false, mv, 0)
                GLES20.glUniformMatrix4fv(locProj, 1, false, proj, 0)
                GLES20.glUniform1f(locPR, pixelRatio * sizeBoost)
                GLES20.glUniform1f(locScale, scaleR)
                GLES20.glUniform4f(locLayers,
                    layerAngles[0], layerAngles[1], layerAngles[2], layerAngles[3])
                GLES20.glUniform3f(locCore,
                    coreArr[stateIndex * 3], coreArr[stateIndex * 3 + 1], coreArr[stateIndex * 3 + 2])
                GLES20.glUniform3f(locAccent,
                    accentArr[stateIndex * 3], accentArr[stateIndex * 3 + 1], accentArr[stateIndex * 3 + 2])

                java.util.Arrays.fill(waveArr, 0f)
                for (i in 0 until waves.size) {
                    waveArr[i * 4] = waves[i].radius
                    waveArr[i * 4 + 1] = 68f
                    waveArr[i * 4 + 2] = 1f
                    waveArr[i * 4 + 3] = 0f
                }
                GLES20.glUniform4fv(locWave, 4, waveArr, 0)

                // hover tắt trên wallpaper
                GLES20.glUniform4f(locHover, 0f, 0f, 0f, -1f)

                GLES20.glActiveTexture(GLES20.GL_TEXTURE0)
                GLES20.glBindTexture(GLES20.GL_TEXTURE_2D, tex)
                GLES20.glUniform1i(locTex, 0)

                GLES20.glEnable(GLES20.GL_BLEND)
                GLES20.glBlendFuncSeparate(
                    GLES20.GL_SRC_ALPHA, GLES20.GL_ONE, GLES20.GL_ZERO, GLES20.GL_ONE
                )

                // ---- structure ----
                GLES20.glBindBuffer(GLES20.GL_ARRAY_BUFFER, structVbo)
                GLES20.glEnableVertexAttribArray(locPos)
                GLES20.glVertexAttribPointer(locPos, 3, GLES20.GL_FLOAT, false, 32, 0)
                GLES20.glEnableVertexAttribArray(locData)
                GLES20.glVertexAttribPointer(locData, 4, GLES20.GL_FLOAT, false, 32, 12)
                GLES20.glEnableVertexAttribArray(locSym)
                GLES20.glVertexAttribPointer(locSym, 1, GLES20.GL_FLOAT, false, 32, 28)
                GLES20.glDrawArrays(GLES20.GL_POINTS, 0, G_STRUCTURE)

                // ---- sparks ----
                updateSparks(dt, ease, scaleR)

                GLES20.glBindBuffer(GLES20.GL_ARRAY_BUFFER, sparkVbo)
                GLES20.glEnableVertexAttribArray(locPos)
                GLES20.glVertexAttribPointer(locPos, 3, GLES20.GL_FLOAT, false, 32, 0)
                GLES20.glEnableVertexAttribArray(locData)
                GLES20.glVertexAttribPointer(locData, 4, GLES20.GL_FLOAT, false, 32, 12)
                GLES20.glEnableVertexAttribArray(locSym)
                GLES20.glVertexAttribPointer(locSym, 1, GLES20.GL_FLOAT, false, 32, 28)
                GLES20.glDrawArrays(GLES20.GL_POINTS, 0, G_SPARKS)

                GLES20.glDisableVertexAttribArray(locPos)
                GLES20.glDisableVertexAttribArray(locData)
                GLES20.glDisableVertexAttribArray(locSym)

                EGL14.eglSwapBuffers(dpy, surf)
            } catch (e: Exception) {
                // bỏ qua khung lỗi
            }
        }
    }
}
