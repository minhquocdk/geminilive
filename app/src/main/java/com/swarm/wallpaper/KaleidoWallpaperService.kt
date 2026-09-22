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
import kotlin.math.exp
import kotlin.math.max
import kotlin.random.Random

// ───────────────────────── CẤU HÌNH (chỉnh ở đây) ─────────────────────────
private const val G_PARTICLES = 20000     // số hạt
private const val G_FPS = 60              // fps bình thường
private const val G_FPS_SAVER = 15        // fps khi bật Tiết kiệm pin
private const val G_AUTO_WAVE_MS = 8000L  // tự bắn sóng đổi màu mỗi N ms (0 = tắt, chỉ chạm mới đổi)
private const val G_SPARK_N = 0.7f        // độ "nhọn" của hình sparkle
private const val G_SIZE_BOOST = 1.6f     // nhân kích thước ký tự cho dễ nhìn trên màn hình nhỏ
private const val G_PET_PARTICLES = 500   // số hạt tạo nên con pet
private const val G_SYMBOLS = "⌖⎋⍕⌬⧉⧇⧻⧼⧽"
private const val G_SYMBOLS_FALLBACK = "✦✧◆◇○△□+×"

private class KWave(var radius: Float, val state: Int)

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

void main() {
    vec2 uv = gl_PointCoord;
    uv.x = (uv.x + vSym) / 16.0;
    vec4 t = texture2D(uTex, uv);
    if (t.a < 0.1) discard;
    gl_FragColor = vec4(vColor, t.a);
}
"""

// ───────────────────────── PET SHADER ─────────────────────────
// Con pet (port từ aqua.html) cũng được tạo nên từ các hạt point.
private const val PET_VERT = """
attribute vec4 aP;        // xyz = offset quanh tâm pet
uniform mat4 uMV;
uniform mat4 uProj;
uniform vec2 uPetPos;
uniform float uPR;
uniform float uTime;
uniform vec3 uColor;
varying vec3 vColor;

void main() {
    vec3 p = aP.xyz;
    // bơi lượn nhẹ
    p.x += sin(uTime * 2.3 + aP.y * 0.3) * 0.6;
    p.y += cos(uTime * 1.9 + aP.x * 0.3) * 0.5;
    vec4 mv = uMV * vec4(p + vec3(uPetPos, 0.0), 1.0);
    gl_PointSize = 2.4 * uPR * (300.0 / -mv.z);
    gl_Position = uProj * mv;
    vColor = uColor;
}
"""

private const val PET_FRAG = """
precision mediump float;
varying vec3 vColor;
void main() {
    vec2 c = gl_PointCoord - vec2(0.5);
    float d2 = dot(c, c);
    if (d2 > 0.25) discard;
    gl_FragColor = vec4(vColor, 1.0 - d2 * 3.0);
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

        // pet (port từ aqua.html)
        private var petProg = 0
        private var petVbo = 0
        private var petLocP = 0
        private var petLocMV = 0
        private var petLocProj = 0
        private var petLocPos = 0
        private var petLocPR = 0
        private var petLocTime = 0
        private var petLocColor = 0

        private var petX = 40f
        private var petY = 0f
        private var petTX = 40f
        private var petTY = 0f
        private var petEnergy = 88f
        private var petMood = 72f
        private var petHunger = 25f
        private var petNeedsAcc = 0f
        private var petNextDecisionAt = 0L
        private var petSleeping = false
        private var petWobble = 0f

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

        // chạm màn hình → sóng đổi màu
        override fun onTouchEvent(event: MotionEvent) {
            if (event.actionMasked == MotionEvent.ACTION_DOWN) {
                triggerWave(SystemClock.uptimeMillis())
                petMood = minOf(100f, petMood + 5f)
                petEnergy = maxOf(0f, petEnergy - 1.5f)
            }
            super.onTouchEvent(event)
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

            val symCount = buildAtlas()

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
            if (!createPet()) return false
            return true
        }

        // ── Pet: program riêng + buffer hạt tạo nên con pet (port từ aqua.html) ──
        private fun createPet(): Boolean {
            val vs = compile(GLES20.GL_VERTEX_SHADER, PET_VERT)
            val fs = compile(GLES20.GL_FRAGMENT_SHADER, PET_FRAG)
            if (vs == 0 || fs == 0) return false
            petProg = GLES20.glCreateProgram()
            GLES20.glAttachShader(petProg, vs)
            GLES20.glAttachShader(petProg, fs)
            GLES20.glLinkProgram(petProg)
            val st = IntArray(1)
            GLES20.glGetProgramiv(petProg, GLES20.GL_LINK_STATUS, st, 0)
            if (st[0] == 0) return false

            petLocP = GLES20.glGetAttribLocation(petProg, "aP")
            petLocMV = GLES20.glGetUniformLocation(petProg, "uMV")
            petLocProj = GLES20.glGetUniformLocation(petProg, "uProj")
            petLocPos = GLES20.glGetUniformLocation(petProg, "uPetPos")
            petLocPR = GLES20.glGetUniformLocation(petProg, "uPR")
            petLocTime = GLES20.glGetUniformLocation(petProg, "uTime")
            petLocColor = GLES20.glGetUniformLocation(petProg, "uColor")

            val buf = ByteBuffer.allocateDirect(G_PET_PARTICLES * 4 * 4).order(ByteOrder.nativeOrder()).asFloatBuffer()
            // thân: ellipse blob
            for (i in 0 until 220) {
                val a = (Random.nextFloat() * 2f * PI).toFloat()
                val rad = kotlin.math.sqrt(Random.nextFloat())
                buf.put(kotlin.math.cos(a) * rad * 14f)
                buf.put(kotlin.math.sin(a) * rad * 9f)
                buf.put(Random.nextFloat() * 3f - 1.5f)
                buf.put(0f)
            }
            // mane: các sợi vung ra phía sau
            for (i in 0 until 120) {
                val t = i / 15f
                val baseX = -2f - t * 0.4f
                val baseY = -5f + t * 0.3f
                val u = Random.nextFloat()
                val len = 16f + Random.nextFloat() * 5f
                buf.put(baseX - u * len)
                buf.put(baseY - u * 8f + kotlin.math.sin(u * 3f) * 5f)
                buf.put(Random.nextFloat() * 2f - 1f)
                buf.put(0f)
            }
            // chân
            for (i in 0 until 60) {
                val l = Random.nextInt(4)
                val sx = -7f + l * 4.6f
                val t = Random.nextFloat()
                val sw = kotlin.math.sin(t * 4f) * 1.8f
                buf.put(sx + sw)
                buf.put(7f + t * 7f)
                buf.put(0f)
                buf.put(0f)
            }
            // mắt + chấm nhỏ
            for (i in 0 until (G_PET_PARTICLES - 400)) {
                buf.put(5f + Random.nextFloat() * 3f)
                buf.put(-2f + Random.nextFloat() * 3f)
                buf.put(1f)
                buf.put(0f)
            }
            buf.position(0)
            val ids = IntArray(1)
            GLES20.glGenBuffers(1, ids, 0)
            petVbo = ids[0]
            GLES20.glBindBuffer(GLES20.GL_ARRAY_BUFFER, petVbo)
            GLES20.glBufferData(GLES20.GL_ARRAY_BUFFER, G_PET_PARTICLES * 4 * 4, buf, GLES20.GL_STATIC_DRAW)
            return true
        }

        // Logic pet đơn giản port từ aqua.html: nhu cầu + bơi lượn
        private fun updatePet(dt: Float, now: Long) {
            petNeedsAcc += dt
            if (petNeedsAcc >= 1f) {
                val s = petNeedsAcc.toInt()
                petNeedsAcc -= s.toFloat()
                if (petSleeping) {
                    petEnergy = minOf(100f, petEnergy + 3f * s)
                    if (petEnergy >= 70f) petSleeping = false
                } else {
                    petHunger = minOf(100f, petHunger + 0.72f * s)
                    petEnergy = maxOf(0f, petEnergy - 0.24f * s)
                    petMood = maxOf(0f, petMood - 0.04f * s)
                    if (petEnergy < 18f) petSleeping = true
                }
            }
            if (now >= petNextDecisionAt) {
                petNextDecisionAt = now + 2500L + Random.nextLong(3000L)
                if (petSleeping) {
                    petTX = 0f
                    petTY = 0f
                } else {
                    val ang = (Random.nextFloat() * 2f * PI).toFloat()
                    val r = 30f + Random.nextFloat() * 55f
                    petTX = kotlin.math.cos(ang) * r
                    petTY = kotlin.math.sin(ang) * r * 0.55f
                }
            }
            val dx = petTX - petX
            val dy = petTY - petY
            val d = kotlin.math.sqrt(dx * dx + dy * dy)
            if (d > 0.5f) {
                val speed = if (petSleeping) 3f else (12f * (0.5f + petEnergy / 200f))
                val step = minOf(d, speed * dt)
                petX += dx / d * step
                petY += dy / d * step
            }
            petWobble += dt * (if (petSleeping) 1.2f else 2.4f)
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

        private fun releaseGL() {
            try {
                if (dpy != EGL14.EGL_NO_DISPLAY) {
                    if (glReady && ctx != EGL14.EGL_NO_CONTEXT && surf != EGL14.EGL_NO_SURFACE) {
                        EGL14.eglMakeCurrent(dpy, surf, surf, ctx)
                        GLES20.glDeleteBuffers(1, intArrayOf(vbo), 0)
                        GLES20.glDeleteTextures(1, intArrayOf(tex), 0)
                        GLES20.glDeleteProgram(prog)
                        if (petVbo != 0) GLES20.glDeleteBuffers(1, intArrayOf(petVbo), 0)
                        if (petProg != 0) GLES20.glDeleteProgram(petProg)
                    }
                    petVbo = 0
                    petProg = 0
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
                updatePet(dt, now)

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
                    // xoay tổng thể như bản gốc
                    val r = animTime * 0.25f
                    val s2 = kotlin.math.sin(r * 2f)
                    val s1 = kotlin.math.sin(r)
                    val rx = Math.toDegrees((s2 * s2 * s2 * 0.4f).toDouble()).toFloat()
                    val ry = Math.toDegrees((s1 * s1 * s1 * 0.6f).toDouble()).toFloat()
                    val rz = Math.toDegrees((s1 * s1 * s1 * -0.3f).toDouble()).toFloat()
                    Matrix.setIdentityM(mv, 0)
                    Matrix.translateM(mv, 0, 0f, 0f, -camZ)
                    Matrix.rotateM(mv, 0, rx, 1f, 0f, 0f)
                    Matrix.rotateM(mv, 0, ry, 0f, 1f, 0f)
                    Matrix.rotateM(mv, 0, rz, 0f, 0f, 1f)
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

                    // ── Vẽ pet (particle) ──
                    if (petProg != 0 && petVbo != 0) {
                        GLES20.glUseProgram(petProg)
                        GLES20.glUniformMatrix4fv(petLocMV, 1, false, mv, 0)
                        GLES20.glUniformMatrix4fv(petLocProj, 1, false, proj, 0)
                        val ox = petX + kotlin.math.sin(petWobble) * 1.5f
                        val oy = petY + kotlin.math.cos(petWobble * 0.8f) * 1.2f
                        GLES20.glUniform2f(petLocPos, ox, oy)
                        GLES20.glUniform1f(petLocPR, pixelRatio * G_SIZE_BOOST)
                        GLES20.glUniform1f(petLocTime, animTime)
                        val petHue = if (petSleeping) 210f else (140f + petMood * 0.7f).coerceAtMost(190f)
                        val pc = Color.HSVToColor(floatArrayOf(petHue, 0.85f, 1f))
                        GLES20.glUniform3f(
                            petLocColor,
                            Color.red(pc) / 255f,
                            Color.green(pc) / 255f,
                            Color.blue(pc) / 255f
                        )
                        GLES20.glEnable(GLES20.GL_BLEND)
                        GLES20.glBlendFunc(GLES20.GL_SRC_ALPHA, GLES20.GL_ONE_MINUS_SRC_ALPHA)
                        GLES20.glBindBuffer(GLES20.GL_ARRAY_BUFFER, petVbo)
                        GLES20.glEnableVertexAttribArray(petLocP)
                        GLES20.glVertexAttribPointer(petLocP, 4, GLES20.GL_FLOAT, false, 16, 0)
                        GLES20.glDrawArrays(GLES20.GL_POINTS, 0, G_PET_PARTICLES)
                        GLES20.glDisableVertexAttribArray(petLocP)
                    }
                }

                EGL14.eglSwapBuffers(dpy, surf)
            } catch (e: Exception) {
                // bỏ qua khung lỗi
            }
        }
    }
}
