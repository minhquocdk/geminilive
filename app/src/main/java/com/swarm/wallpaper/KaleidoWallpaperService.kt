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
import android.hardware.Sensor
import android.hardware.SensorEvent
import android.hardware.SensorEventListener
import android.hardware.SensorManager
import android.os.SystemClock
import android.service.wallpaper.WallpaperService
import android.view.MotionEvent
import android.view.SurfaceHolder
import java.nio.ByteBuffer
import java.nio.ByteOrder
import kotlin.math.PI
import kotlin.math.abs
import kotlin.math.cos
import kotlin.math.max
import kotlin.math.sin
import kotlin.math.sqrt
import kotlin.random.Random

// ───────────────────────── CẤU HÌNH (chỉnh ở đây) ─────────────────────────
private const val G_PARTICLES = 18000     // số hạt dựng hình
private const val G_SPARKS = 3000         // pool tàn lửa
private const val G_FPS = 60              // fps bình thường
private const val G_FPS_SAVER = 20        // fps khi bật Tiết kiệm pin
private const val G_R = 120f              // bán kính gốc (world units)
private const val G_HOVER_R = 95f         // bán kính hover parallax
private const val G_SYMBOLS = "ᚠᚢᚦᚨᚱᚲᚷᚹᚺᚾᛁᛃᛇᛈᛉᛋᛏᛒᛖᛗᛚᛝᛟᛞᛥᛦᛧᛨᛩᛪ"
private const val G_SYMBOLS_FALLBACK = "✦✧◆◇○△□+×·"

private class Preset(val name: String, val hex: Int, val core: Int)

private val PRESETS = arrayOf(
    Preset("Cam Mystic",    0xffff7b00.toInt(), 0xffffa600.toInt()),
    Preset("Đỏ Crimson",    0xffe52121.toInt(), 0xffff6b6b.toInt()),
    Preset("Xanh Eldritch", 0xff00cc99.toInt(), 0xff66ffcc.toInt()),
    Preset("Xanh Sorcerer", 0xff1e70e5.toInt(), 0xff6ba2ff.toInt())
)

private class KWave(var radius: Float, val width: Float, val speed: Float)

private class ShapeDef(
    val layer: Int,
    val weight: Float,
    val size: Float,
    val alpha: Float,
    val jitter: Float,
    val z: Float,
    val zj: Float,
    val disc: Float = 0f,
    val open: Boolean = false,
    val polys: List<FloatArray> = emptyList()
)

private class SpellDef(
    val name: String,
    val preset: Int,
    val spin: FloatArray,        // tốc độ xoay 4 layer
    val sparkOrbit: Boolean,     // true = xoáy vành, false = toả từ lõi
    val sparkRateLo: Float, val sparkRateHi: Float,
    val sparkSpin: Float,
    val sparkSize: Float,
    val sparkZ: Float,
    val shapes: List<ShapeDef>
)

// ───────────────────────── POLYLINE HELPERS ─────────────────────────
private fun circlePoly(r: Float, seg: Int, phase: Float = 0f): FloatArray {
    val out = FloatArray(seg * 2)
    val tau = (2.0 * PI).toFloat()
    for (i in 0 until seg) {
        val a = i.toFloat() / seg * tau + phase
        out[i * 2] = cos(a) * r; out[i * 2 + 1] = sin(a) * r
    }
    return out
}

private fun starPoly(points: Int, outer: Float, inner: Float, phase: Float = 0f): FloatArray {
    val out = FloatArray(points * 4)
    val tau = (2.0 * PI).toFloat()
    for (i in 0 until points * 2) {
        val rad = if (i % 2 == 0) outer else inner
        val a = i.toFloat() / (points * 2) * tau + phase
        out[i * 2] = cos(a) * rad; out[i * 2 + 1] = sin(a) * rad
    }
    return out
}

private fun polygonPoly(sides: Int, r: Float, phase: Float = 0f): FloatArray {
    val out = FloatArray(sides * 2)
    val tau = (2.0 * PI).toFloat()
    for (i in 0 until sides) {
        val a = i.toFloat() / sides * tau + phase
        out[i * 2] = cos(a) * r; out[i * 2 + 1] = sin(a) * r
    }
    return out
}

private fun squarePoly(half: Float, angle: Float): FloatArray {
    val c = cos(angle); val s = sin(angle)
    val px = floatArrayOf(-half, half, half, -half)
    val py = floatArrayOf(-half, -half, half, half)
    val out = FloatArray(8)
    for (i in 0 until 4) {
        out[i * 2] = px[i] * c - py[i] * s
        out[i * 2 + 1] = px[i] * s + py[i] * c
    }
    return out
}

private fun arcPoly(r: Float, a0: Float, a1: Float, seg: Int): FloatArray {
    val out = FloatArray((seg + 1) * 2)
    for (i in 0..seg) {
        val a = a0 + (a1 - a0) * i / seg
        out[i * 2] = cos(a) * r; out[i * 2 + 1] = sin(a) * r
    }
    return out
}

private fun spiralPoly(r0: Float, r1: Float, a0: Float, a1: Float, seg: Int): FloatArray {
    val out = FloatArray((seg + 1) * 2)
    for (i in 0..seg) {
        val t = i.toFloat() / seg
        val r = r0 + (r1 - r0) * t
        val a = a0 + (a1 - a0) * t
        out[i * 2] = cos(a) * r; out[i * 2 + 1] = sin(a) * r
    }
    return out
}

private fun lensPoly(w: Float, h: Float, seg: Int): FloatArray {
    val out = FloatArray((seg * 2 + 2) * 2)
    var k = 0
    for (i in 0..seg) {
        val t = i.toFloat() / seg
        out[k++] = -w + 2 * w * t
        out[k++] = h * sin(PI.toFloat() * t)
    }
    for (i in seg downTo 0) {
        val t = i.toFloat() / seg
        out[k++] = -w + 2 * w * t
        out[k++] = -h * sin(PI.toFloat() * t)
    }
    return out
}

private fun makeCoils(count: Int, rBase: Float, rAmp: Float, seed: Float): List<FloatArray> {
    val tau = (2.0 * PI).toFloat()
    return (0 until count).map { k ->
        val r = rBase + rAmp * abs(sin(k * 1.7f + seed))
        val a0 = k / count.toFloat() * tau + seed
        arcPoly(r, a0, a0 + tau * 0.62f, 56)
    }
}

// ───────────────────────── ĐỊNH NGHĨA 5 PHÉP THUẬT ─────────────────────────
private val MANDALA: List<ShapeDef> = listOf(
    ShapeDef(0, 0.130f, 2.2f, 0.13f, 0.055f,   0f,  6f, polys = listOf(circlePoly(1.05f, 80))),
    ShapeDef(0, 0.050f, 2.6f, 0.30f, 0.004f,   0f,  3f, polys = listOf(circlePoly(1.00f,100))),
    ShapeDef(0, 0.045f, 2.6f, 0.28f, 0.004f,   0f,  3f, polys = listOf(circlePoly(0.92f,100))),
    ShapeDef(0, 0.075f, 7.0f, 0.55f, 0.002f,   0f,  2f, polys = listOf(circlePoly(0.962f,100))),
    ShapeDef(1, 0.170f, 2.9f, 0.32f, 0.005f,  -5f,  3f, polys = listOf(starPoly(8, 0.86f, 0.60f, (PI/2).toFloat()))),
    ShapeDef(1, 0.050f, 2.6f, 0.28f, 0.004f,  -5f,  3f, polys = listOf(circlePoly(0.60f, 80))),
    ShapeDef(2, 0.190f, 2.9f, 0.32f, 0.005f,   5f,  3f, polys = listOf(starPoly(12, 0.72f, 0.52f, 0f))),
    ShapeDef(2, 0.040f, 2.5f, 0.26f, 0.004f,   5f,  3f, polys = listOf(circlePoly(0.48f, 80))),
    ShapeDef(3, 0.130f, 2.7f, 0.30f, 0.005f,  10f,  4f, polys = listOf(
        squarePoly(0.30f, 0f), squarePoly(0.30f, (PI/6).toFloat()),
        squarePoly(0.30f, (PI/3).toFloat()), squarePoly(0.30f, (PI/2).toFloat())
    )),
    ShapeDef(3, 0.060f, 3.0f, 0.30f, 0.000f,   0f,  4f, disc = 0.15f)
)

private val PORTAL_SWIRL: List<FloatArray> = run {
    val tau = (2.0 * PI).toFloat()
    (0 until 8).map { k ->
        val a0 = k / 8f * tau
        spiralPoly(0.22f, 0.88f, a0, a0 + 0.85f, 40)
    }
}
private val PORTAL: List<ShapeDef> = listOf(
    ShapeDef(0, 0.22f, 2.8f, 0.55f, 0.008f, 0f,  3f, polys = listOf(circlePoly(1.00f,160))),
    ShapeDef(0, 0.14f, 2.4f, 0.40f, 0.010f, 0f,  3f, polys = listOf(circlePoly(0.93f,140))),
    ShapeDef(0, 0.12f, 2.4f, 0.35f, 0.020f, 0f,  5f, polys = listOf(circlePoly(1.08f,140))),
    ShapeDef(1, 0.10f, 3.6f, 0.14f, 0.100f, 0f, 10f, polys = listOf(circlePoly(0.80f,120))),
    ShapeDef(1, 0.07f, 4.0f, 0.45f, 0.030f, 0f, 12f, polys = listOf(circlePoly(1.15f,120))),
    ShapeDef(2, 0.25f, 2.6f, 0.30f, 0.010f, 0f,  6f, open = true, polys = PORTAL_SWIRL),
    ShapeDef(3, 0.10f, 2.6f, 0.10f, 0.000f, 0f,  6f, disc = 0.55f)
)

private val BANDS: List<ShapeDef> = listOf(
    ShapeDef(0, 0.30f, 3.0f, 0.45f, 0.012f,  0f, 8f, open = true, polys = makeCoils(7, 0.60f, 0.16f, 0f)),
    ShapeDef(1, 0.28f, 3.0f, 0.42f, 0.012f, -4f, 8f, open = true, polys = makeCoils(7, 0.68f, 0.14f, 0.45f)),
    ShapeDef(2, 0.22f, 2.8f, 0.38f, 0.010f,  4f, 8f, open = true, polys = makeCoils(7, 0.52f, 0.12f, 0.90f)),
    ShapeDef(0, 0.06f, 3.6f, 0.10f, 0.060f,  0f, 8f, polys = listOf(circlePoly(0.92f, 90))),
    ShapeDef(3, 0.08f, 2.8f, 0.35f, 0.010f,  0f, 4f, polys = listOf(circlePoly(0.28f, 80))),
    ShapeDef(3, 0.06f, 3.0f, 0.40f, 0.000f,  0f, 3f, disc = 0.10f)
)

private val MIRROR_SHARDS: List<FloatArray> = run {
    val rnd = Random(20240617)
    val tau = (2.0 * PI).toFloat()
    (0 until 34).map {
        val a = rnd.nextFloat() * tau
        val rad = 0.28f + rnd.nextFloat() * 0.78f
        val cx = cos(a) * rad
        val cy = sin(a) * rad
        val s = 0.05f + rnd.nextFloat() * 0.13f
        val rot = rnd.nextFloat() * tau
        val sides = 3 + rnd.nextInt(2)
        val poly = FloatArray(sides * 2)
        for (j in 0 until sides) {
            val ang = rot + j / sides.toFloat() * tau
            val rr = s * (0.55f + rnd.nextFloat() * 0.75f)
            poly[j * 2] = cx + cos(ang) * rr
            poly[j * 2 + 1] = cy + sin(ang) * rr
        }
        poly
    }
}
private val MIRROR: List<ShapeDef> = listOf(
    ShapeDef(0, 0.42f, 2.6f, 0.34f, 0.004f, 0f, 10f, polys = MIRROR_SHARDS),
    ShapeDef(1, 0.14f, 2.6f, 0.35f, 0.006f, 0f,  4f, polys = listOf(polygonPoly(6, 1.02f, 0f))),
    ShapeDef(1, 0.10f, 2.4f, 0.28f, 0.006f, 0f,  4f, polys = listOf(polygonPoly(6, 0.86f, (PI/6).toFloat()))),
    ShapeDef(0, 0.08f, 2.6f, 0.22f, 0.010f, 0f,  6f, polys = listOf(circlePoly(1.12f, 120))),
    ShapeDef(2, 0.12f, 2.6f, 0.30f, 0.006f, 0f,  6f, polys = listOf(
        polygonPoly(3, 0.50f, 0f), polygonPoly(3, 0.50f, PI.toFloat())
    )),
    ShapeDef(3, 0.06f, 3.0f, 0.28f, 0.000f, 0f,  4f, disc = 0.12f)
)

private val AGAMOTTO_RAYS: List<FloatArray> = run {
    val tau = (2.0 * PI).toFloat()
    (0 until 24).map { k ->
        val a = k / 24f * tau
        floatArrayOf(cos(a) * 0.60f, sin(a) * 0.60f, cos(a) * 0.82f, sin(a) * 0.82f)
    }
}
private val AGAMOTTO: List<ShapeDef> = listOf(
    ShapeDef(0, 0.10f, 2.6f, 0.35f, 0.005f,  0f, 3f, polys = listOf(circlePoly(1.02f,120))),
    ShapeDef(0, 0.08f, 2.6f, 0.30f, 0.005f,  0f, 3f, polys = listOf(circlePoly(0.94f,120))),
    ShapeDef(0, 0.09f, 6.5f, 0.50f, 0.002f,  0f, 2f, polys = listOf(circlePoly(0.98f,120))),
    ShapeDef(1, 0.20f, 2.6f, 0.32f, 0.004f,  0f, 4f, open = true, polys = AGAMOTTO_RAYS),
    ShapeDef(1, 0.12f, 2.8f, 0.28f, 0.005f, -4f, 4f, polys = listOf(starPoly(6, 0.72f, 0.50f, (PI/2).toFloat()))),
    ShapeDef(2, 0.10f, 2.6f, 0.32f, 0.005f,  0f, 3f, polys = listOf(circlePoly(0.62f,100))),
    ShapeDef(3, 0.22f, 3.0f, 0.45f, 0.006f,  6f, 5f, polys = listOf(lensPoly(0.46f, 0.24f, 40))),
    ShapeDef(3, 0.05f, 3.2f, 0.50f, 0.004f,  6f, 3f, polys = listOf(circlePoly(0.12f, 60))),
    ShapeDef(3, 0.04f, 3.0f, 0.35f, 0.000f,  6f, 3f, disc = 0.06f)
)

private val SPELLS: List<SpellDef> = listOf(
    SpellDef("Khiên Mandala", 0,
        floatArrayOf(0.20f, -0.35f, 0.50f, -0.70f),
        false, 0.16f, 0.42f, 2.6f, 1.00f, 40f, MANDALA),
    SpellDef("Cổng Không Gian", 0,
        floatArrayOf(0.55f, -0.20f, 0.35f, -0.10f),
        true,  0.45f, 0.95f, 6.0f, 1.15f, 26f, PORTAL),
    SpellDef("Dây Trói Cyttorak", 1,
        floatArrayOf(0.42f, -0.55f, 0.70f, -0.30f),
        false, 0.22f, 0.55f, 3.4f, 1.00f, 46f, BANDS),
    SpellDef("Chiều Gương", 3,
        floatArrayOf(0.14f, -0.22f, 0.30f, -0.44f),
        false, 0.10f, 0.28f, 1.6f, 0.90f, 70f, MIRROR),
    SpellDef("Mắt Agamotto", 2,
        floatArrayOf(0.16f, -0.28f, 0.38f, -0.52f),
        true,  0.25f, 0.60f, 3.0f, 1.00f, 34f, AGAMOTTO)
)

// ───────────────────────── SHADER ─────────────────────────
// VERT cho hạt dựng hình: xoay 4 layer, hover boost, mix màu core/base
private const val VERT = """
attribute vec4 aP;        // x, y, z, layer (0..3)
attribute vec4 aX;        // radius, colorMix, sizeBase, alphaBase
attribute float aSym;

uniform mat4 uMV;
uniform mat4 uProj;
uniform float uPixelRatio;
uniform vec2 uCosSin[4];  // (cos, sin) cho từng layer
uniform vec3 uBaseColor;
uniform vec3 uCoreColor;
uniform float uScale;
uniform vec3 uHover;      // xyz, .z > 0.5 = active
uniform float uHoverR2;
uniform float uHoverR;
uniform float uSizeIn;
uniform float uReveal;

varying vec3 vColor;
varying float vSym;
varying float vAlpha;

void main() {
    int L = int(aP.w + 0.5);
    vec2 cs = uCosSin[L];
    float c = cs.x;
    float s = cs.y;
    float bx = aP.x * c - aP.y * s;
    float by = aP.x * s + aP.y * c;
    vec3 p;
    p.x = bx * uScale;
    p.y = by * uScale;
    p.z = aP.z * uScale;

    float boost = 1.0;
    if (uHover.z > 0.5) {
        vec3 d = p - uHover;
        float d2 = dot(d, d);
        if (d2 < uHoverR2) {
            float f = 1.0 - sqrt(d2) / uHoverR;
            boost = 1.0 + f * 1.9;
        }
    }

    vec3 col = mix(uBaseColor, uCoreColor, aX.y);
    if (boost > 1.0) {
        float k = boost - 1.0;
        col = col * boost + vec3(k * 0.28);
        col = min(col, vec3(1.0));
    }
    vColor = col;

    float sz = aX.z * uSizeIn;
    if (boost > 1.0) sz *= 1.0 + (boost - 1.0) * 0.45;
    vAlpha = aX.w * uReveal;

    vec4 mv = uMV * vec4(p, 1.0);
    gl_PointSize = sz * uPixelRatio * (300.0 / -mv.z);
    gl_Position = uProj * mv;
    vSym = aSym;
}
"""

// VERT cho tàn lửa: vị trí + màu đã tính sẵn trên CPU
private const val SPARK_VERT = """
attribute vec4 aP;        // x, y, z, _
attribute vec3 aCol;
attribute vec2 aSA;       // size, alpha
attribute float aSym;

uniform mat4 uMV;
uniform mat4 uProj;
uniform float uPixelRatio;

varying vec3 vColor;
varying float vSym;
varying float vAlpha;

void main() {
    vec4 mv = uMV * vec4(aP.xyz, 1.0);
    gl_PointSize = aSA.x * uPixelRatio * (300.0 / -mv.z);
    gl_Position = uProj * mv;
    vColor = aCol;
    vSym = aSym;
    vAlpha = aSA.y;
}
"""

private const val FRAG = """
precision mediump float;
varying vec3 vColor;
varying float vSym;
varying float vAlpha;
uniform sampler2D uTex;
uniform float uSymCount;

void main() {
    vec2 uv = gl_PointCoord;
    uv.x = (uv.x + vSym) / uSymCount;
    vec4 t = texture2D(uTex, uv);
    if (t.a < 0.12) discard;
    gl_FragColor = vec4(vColor, t.a * vAlpha);
}
"""

// ───────────────────────── WALLPAPER SERVICE ─────────────────────────
class KaleidoWallpaperService : WallpaperService() {

    override fun onCreateEngine(): Engine = GemEngine()

    private inner class GemEngine : Engine(), SensorEventListener {
        private val handler = Handler(Looper.getMainLooper())
        private val pm = getSystemService(Context.POWER_SERVICE) as PowerManager
        private val pixelRatio = resources.displayMetrics.density
        private val sensorMgr = getSystemService(Context.SENSOR_SERVICE) as SensorManager
        private val accel by lazy { sensorMgr.getDefaultSensor(Sensor.TYPE_ACCELEROMETER) }

        private var shown = false
        private var glReady = false

        private var dpy: EGLDisplay = EGL14.EGL_NO_DISPLAY
        private var ctx: EGLContext = EGL14.EGL_NO_CONTEXT
        private var surf: EGLSurface = EGL14.EGL_NO_SURFACE

        private var progStruct = 0
        private var progSpark = 0
        private var vboStruct = 0
        private var vboSpark = 0
        private var tex = 0

        // uniforms chung
        private var uMV = 0
        private var uProj = 0
        private var uTex = 0
        // uniforms progStruct
        private var uPRs = 0
        private var uCosSin = 0
        private var uBaseColor = 0
        private var uCoreColor = 0
        private var uScale = 0
        private var uHover = 0
        private var uHoverR2 = 0
        private var uHoverR = 0
        private var uSizeIn = 0
        private var uReveal = 0
        private var uSymCountS = 0
        private var aPs = 0
        private var aXs = 0
        private var aSyms = 0
        // uniforms progSpark
        private var uPRk = 0
        private var uSymCountK = 0
        private var aPk = 0
        private var aColk = 0
        private var aSAk = 0
        private var aSymk = 0

        private var glyphCount = 16

        private var w = 0
        private var h = 0
        private var camZ = 300f
        private val proj = FloatArray(16)
        private val mv = FloatArray(16)

        private var startAt = 0L
        private var lastT = 0L
        private var animTime = 0f
        private var reveal = 0f

        // trạng thái phép thuật / màu
        private var spellIndex = 0
        private var presetIndex = 0
        private var speed = 1.2f
        private val angles = FloatArray(4)
        private val cosSin = FloatArray(8)

        // lắc đổi phép
        private var lastShakeAt = 0L
        private val grav = FloatArray(3)
        private var hasGrav = false

        // hover (parallax point)
        private var hoverActive = false
        private var hoverX = 0f; private var hoverY = 0f
        private var lastDownAt = 0L
        private var downX = 0f; private var downY = 0f

        private val waves = ArrayList<KWave>()

        // hạt dựng hình
        private val baseP = FloatArray(G_PARTICLES * 9)   // x,y,z,layer, radius,mix,size,alpha, sym
        private val dynP = FloatArray(G_PARTICLES * 4)    // cos-sin applied rotation result + reveal (unused CPU now)
        // tàn lửa
        private val sparkBase = FloatArray(G_SPARKS * 9)  // x,y,z,_,r,g,b,size,alpha, sym (packed differently)
        private val spAngle = FloatArray(G_SPARKS)
        private val spLife = FloatArray(G_SPARKS)
        private val spRate = FloatArray(G_SPARKS)
        private val spSpin = FloatArray(G_SPARKS)
        private val spZ = FloatArray(G_SPARKS)
        private val spBaseSize = FloatArray(G_SPARKS)
        private var activeSparks = 2000
        // Layout 10 float / spark: x,y,z,pad, r,g,b, size,alpha,sym
        private val sparkCPU = FloatArray(G_SPARKS * 10)

        private val baseColorArr = FloatArray(3)
        private val coreColorArr = FloatArray(3)

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

        private fun hexToRgb(hex: Int, out: FloatArray) {
            out[0] = ((hex shr 16) and 0xff) / 255f
            out[1] = ((hex shr 8) and 0xff) / 255f
            out[2] = (hex and 0xff) / 255f
        }

        private fun applyPreset(i: Int) {
            presetIndex = i
            hexToRgb(PRESETS[i].hex, baseColorArr)
            hexToRgb(PRESETS[i].core, coreColorArr)
        }

        override fun onCreate(surfaceHolder: SurfaceHolder) {
            super.onCreate(surfaceHolder)
            setTouchEventsEnabled(true)
            applyPreset(0)
            accel?.let { sensorMgr.registerListener(this, it, SensorManager.SENSOR_DELAY_GAME) }
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
            // vừa khít chiều ngang màn hình (kể cả dọc)
            val halfNeeded = G_R * 1.30f
            val tanHalf = Math.tan(Math.toRadians(75.0 / 2.0)).toFloat()
            val distV = halfNeeded / tanHalf
            val distH = halfNeeded / (tanHalf * aspect)
            camZ = max(distV, distH)
            Matrix.perspectiveM(proj, 0, 75f, aspect, 0.1f, 3000f)
        }

        override fun onVisibilityChanged(visible: Boolean) {
            shown = visible
            handler.removeCallbacks(loop)
            if (visible) {
                val now = SystemClock.uptimeMillis()
                startAt = now
                lastT = now
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
            sensorMgr.unregisterListener(this)
            releaseGL()
            super.onDestroy()
        }

        // ── Cảm biến: parallax + lắc đổi phép ──
        override fun onSensorChanged(event: SensorEvent) {
            if (event.sensor.type != Sensor.TYPE_ACCELEROMETER) return
            val x = event.values[0]
            val y = event.values[1]
            val z = event.values[2]
            if (!hasGrav) {
                grav[0] = x; grav[1] = y; grav[2] = z
                hasGrav = true
            } else {
                val a = 0.85f
                grav[0] = grav[0] * a + x * (1 - a)
                grav[1] = grav[1] * a + y * (1 - a)
                grav[2] = grav[2] * a + z * (1 - a)
            }
            // lắc = bỏ trọng lực ra, tính magnitude phần động
            val dx = x - grav[0]
            val dy = y - grav[1]
            val dz = z - grav[2]
            val m = sqrt(dx * dx + dy * dy + dz * dz)
            val now = SystemClock.uptimeMillis()
            if (m > 12f && now - lastShakeAt > 900L) {
                lastShakeAt = now
                spellIndex = (spellIndex + 1) % SPELLS.size
                rebuildStructure(SPELLS[spellIndex].shapes)
                applyPreset(SPELLS[spellIndex].preset)
                reveal = 0f
                angles[0] = 0f; angles[1] = 0f; angles[2] = 0f; angles[3] = 0f
                waves.clear()
                respawnAllSparks(true)
            }
        }

        override fun onAccuracyChanged(sensor: Sensor?, accuracy: Int) {}
        // orbit
        private var orbitYaw = 0f
        private var orbitPitch = 0f
        private var orbitYaw0 = 0f
        private var orbitPitch0 = 0f
        private var dragging = false
        private var velYaw = 0f
        private var velPitch = 0f
        // ── Touch: tap đổi màu + bắn sóng, kéo để di chuyển hover ──
        override fun onTouchEvent(event: MotionEvent) {
            when (event.actionMasked) {
                MotionEvent.ACTION_DOWN -> {
                    downX = event.x; downY = event.y
                    lastDownAt = SystemClock.uptimeMillis()
                    orbitYaw0 = orbitYaw
                    orbitPitch0 = orbitPitch
                    dragging = false
                    velYaw = 0f
                    velPitch = 0f
                    // bật hover ngay khi chạm để ngón tay sáng lên
                    updateHover(event.x, event.y)
                }
                MotionEvent.ACTION_MOVE -> {
                    val dx = event.x - downX
                    val dy = event.y - downY
                    if (!dragging && dx * dx + dy * dy > 100f) dragging = true
                    if (dragging) {
                        val prevYaw = orbitYaw
                        val prevPitch = orbitPitch
                        orbitYaw = orbitYaw0 + dx * 0.35f
                        orbitPitch = (orbitPitch0 + dy * 0.35f).coerceIn(-75f, 75f)
                        velYaw = orbitYaw - prevYaw
                        velPitch = orbitPitch - prevPitch
                    }
                    // hover bám theo ngón tay kể cả khi đang xoay
                    updateHover(event.x, event.y)
                }
                MotionEvent.ACTION_UP -> {
                    if (!dragging) {
                        val dt = SystemClock.uptimeMillis() - lastDownAt
                        val dx = event.x - downX; val dy = event.y - downY
                        if (dt < 300L && sqrt(dx * dx + dy * dy) < 24f) {
                            triggerTap()
                        }
                    }
                    hoverActive = false
                    dragging = false
                }
                MotionEvent.ACTION_CANCEL -> {
                    hoverActive = false
                    dragging = false
                }
            }
            super.onTouchEvent(event)
        }

        private fun updateHover(x: Float, y: Float) {
            if (w == 0 || h == 0) return
            // map screen px -> world xấp xỉ, dùng tỉ lệ màn hình
            val halfW = G_R * 1.30f * (w.toFloat() / h.toFloat()).coerceAtLeast(1f)
            val halfH = G_R * 1.30f
            hoverX = (x / w.toFloat() * 2f - 1f) * halfW
            hoverY = -(y / h.toFloat() * 2f - 1f) * halfH
            hoverActive = true
        }

        private fun triggerTap() {
            presetIndex = (presetIndex + 1) % PRESETS.size
            applyPreset(presetIndex)
            waves.add(KWave(0f, 68f, 620f * speed))
            if (waves.size > 6) waves.removeAt(0)
        }

        override fun onCommand(
            action: String?, x: Int, y: Int, z: Int, extras: Bundle?, resultRequested: Boolean
        ): Bundle? {
            if (action == WallpaperManager.COMMAND_TAP) triggerTap()
            return super.onCommand(action, x, y, z, extras, resultRequested)
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
            // ── program cho hạt dựng hình ──
            val vs1 = compile(GLES20.GL_VERTEX_SHADER, VERT)
            val fs1 = compile(GLES20.GL_FRAGMENT_SHADER, FRAG)
            if (vs1 == 0 || fs1 == 0) return false
            progStruct = GLES20.glCreateProgram()
            GLES20.glAttachShader(progStruct, vs1)
            GLES20.glAttachShader(progStruct, fs1)
            GLES20.glLinkProgram(progStruct)
            val st = IntArray(1)
            GLES20.glGetProgramiv(progStruct, GLES20.GL_LINK_STATUS, st, 0)
            if (st[0] == 0) return false

            uMV = GLES20.glGetUniformLocation(progStruct, "uMV")
            uProj = GLES20.glGetUniformLocation(progStruct, "uProj")
            uTex = GLES20.glGetUniformLocation(progStruct, "uTex")
            uPRs = GLES20.glGetUniformLocation(progStruct, "uPixelRatio")
            uCosSin = GLES20.glGetUniformLocation(progStruct, "uCosSin")
            uBaseColor = GLES20.glGetUniformLocation(progStruct, "uBaseColor")
            uCoreColor = GLES20.glGetUniformLocation(progStruct, "uCoreColor")
            uScale = GLES20.glGetUniformLocation(progStruct, "uScale")
            uHover = GLES20.glGetUniformLocation(progStruct, "uHover")
            uHoverR2 = GLES20.glGetUniformLocation(progStruct, "uHoverR2")
            uHoverR = GLES20.glGetUniformLocation(progStruct, "uHoverR")
            uSizeIn = GLES20.glGetUniformLocation(progStruct, "uSizeIn")
            uReveal = GLES20.glGetUniformLocation(progStruct, "uReveal")
            uSymCountS = GLES20.glGetUniformLocation(progStruct, "uSymCount")
            aPs = GLES20.glGetAttribLocation(progStruct, "aP")
            aXs = GLES20.glGetAttribLocation(progStruct, "aX")
            aSyms = GLES20.glGetAttribLocation(progStruct, "aSym")

            // ── program cho tàn lửa ──
            val vs2 = compile(GLES20.GL_VERTEX_SHADER, SPARK_VERT)
            val fs2 = compile(GLES20.GL_FRAGMENT_SHADER, FRAG)
            if (vs2 == 0 || fs2 == 0) return false
            progSpark = GLES20.glCreateProgram()
            GLES20.glAttachShader(progSpark, vs2)
            GLES20.glAttachShader(progSpark, fs2)
            GLES20.glLinkProgram(progSpark)
            GLES20.glGetProgramiv(progSpark, GLES20.GL_LINK_STATUS, st, 0)
            if (st[0] == 0) return false

            uPRk = GLES20.glGetUniformLocation(progSpark, "uPixelRatio")
            uSymCountK = GLES20.glGetUniformLocation(progSpark, "uSymCount")
            aPk = GLES20.glGetAttribLocation(progSpark, "aP")
            aColk = GLES20.glGetAttribLocation(progSpark, "aCol")
            aSAk = GLES20.glGetAttribLocation(progSpark, "aSA")
            aSymk = GLES20.glGetAttribLocation(progSpark, "aSym")

            glyphCount = buildAtlas().coerceAtLeast(1)
            rebuildStructure(SPELLS[0].shapes)
            respawnAllSparks(true)
            return true
        }

        private fun rebuildStructure(shapes: List<ShapeDef>) {
            val symCount = glyphCount
            // tổng trọng số
            var weightSum = 0f
            for (s in shapes) weightSum += s.weight
            // bảng chọn hình theo trọng số
            val slots = ArrayList<Int>(2048)
            for ((idx, s) in shapes.withIndex()) {
                val cnt = max(1, Math.round(s.weight / weightSum * 2048f))
                repeat(cnt) { slots.add(idx) }
            }
            val slotCount = slots.size

            for (i in 0 until G_PARTICLES) {
                val P = shapes[slots[Random.nextInt(slotCount)]]
                val o = i * 9
                var x: Float; var y: Float
                if (P.disc > 0f) {
                    val a = Random.nextFloat() * (2f * PI).toFloat()
                    val rr = sqrt(Random.nextFloat()) * P.disc * G_R
                    x = cos(a) * rr; y = sin(a) * rr
                } else {
                    // chọn polyline theo độ dài
                    var total = 0f
                    for (poly in P.polys) {
                        val n = poly.size / 2
                        val seg = if (P.open) n - 1 else n
                        var len = 0f
                        for (k in 0 until seg) {
                            val ax = poly[k*2]; val ay = poly[k*2+1]
                            val bx = poly[((k+1) % n)*2]; val by = poly[((k+1) % n)*2+1]
                            val dx = bx - ax; val dy = by - ay
                            len += sqrt(dx*dx + dy*dy)
                        }
                        total += len
                    }
                    var t = Random.nextFloat() * total
                    var chosen: FloatArray = P.polys[0]
                    var chosenLen = 0f
                    for (poly in P.polys) {
                        val n = poly.size / 2
                        val seg = if (P.open) n - 1 else n
                        var len = 0f
                        for (k in 0 until seg) {
                            val ax = poly[k*2]; val ay = poly[k*2+1]
                            val bx = poly[((k+1) % n)*2]; val by = poly[((k+1) % n)*2+1]
                            val dx = bx - ax; val dy = by - ay
                            len += sqrt(dx*dx + dy*dy)
                        }
                        if (t <= len) { chosen = poly; chosenLen = len; break }
                        t -= len
                    }
                    // tìm đoạn
                    val n = chosen.size / 2
                    val seg = if (P.open) n - 1 else n
                    var cum = 0f
                    var lo = 0
                    var acc = 0f
                    for (k in 0 until seg) {
                        val ax = chosen[k*2]; val ay = chosen[k*2+1]
                        val bx = chosen[((k+1) % n)*2]; val by = chosen[((k+1) % n)*2+1]
                        val dx = bx - ax; val dy = by - ay
                        val segLen = sqrt(dx*dx + dy*dy)
                        if (t <= acc + segLen || k == seg - 1) { lo = k; cum = acc; break }
                        acc += segLen
                    }
                    val ax = chosen[lo*2]; val ay = chosen[lo*2+1]
                    val bxi = ((lo + 1) % n) * 2
                    val bx = chosen[bxi]; val by = chosen[bxi+1]
                    val dx = bx - ax; val dy = by - ay
                    val segLen = sqrt(dx*dx + dy*dy).coerceAtLeast(1e-4f)
                    val f = ((t - cum) / segLen).coerceIn(0f, 1f)
                    x = (ax + dx * f) * G_R
                    y = (ay + dy * f) * G_R

                    // jitter
                    val ja = Random.nextFloat() * (2f * PI).toFloat()
                    val jr = (Random.nextFloat() * 0.5f + Random.nextFloat() * 0.5f) * P.jitter * G_R
                    x += cos(ja) * jr; y += sin(ja) * jr
                }

                val z = P.z + (Random.nextFloat() - 0.5f) * P.zj
                val rad = sqrt(x * x + y * y)
                val mix = Math.pow((1f - rad / G_R).coerceAtLeast(0f).toDouble(), 1.5).toFloat()

                baseP[o]     = x
                baseP[o + 1] = y
                baseP[o + 2] = z
                baseP[o + 3] = P.layer.toFloat()
                baseP[o + 4] = rad
                baseP[o + 5] = mix
                baseP[o + 6] = P.size * (0.70f + Random.nextFloat() * 0.60f)
                baseP[o + 7] = P.alpha * (0.65f + Random.nextFloat() * 0.70f)
                baseP[o + 8] = Random.nextInt(symCount).toFloat()
            }

            // nạp lên VBO
            val buf = ByteBuffer.allocateDirect(G_PARTICLES * 9 * 4)
                .order(ByteOrder.nativeOrder()).asFloatBuffer()
            buf.put(baseP); buf.position(0)
            if (vboStruct == 0) {
                val ids = IntArray(1); GLES20.glGenBuffers(1, ids, 0); vboStruct = ids[0]
            }
            GLES20.glBindBuffer(GLES20.GL_ARRAY_BUFFER, vboStruct)
            GLES20.glBufferData(GLES20.GL_ARRAY_BUFFER, G_PARTICLES * 9 * 4, buf, GLES20.GL_STATIC_DRAW)
        }

        private fun respawnAllSparks(warm: Boolean) {
            val sp = SPELLS[spellIndex]
            for (i in 0 until G_SPARKS) {
                spAngle[i] = Random.nextFloat() * (2f * PI).toFloat()
                spLife[i]  = if (warm) Random.nextFloat() else 0f
                spRate[i]  = sp.sparkRateLo + Random.nextFloat() * (sp.sparkRateHi - sp.sparkRateLo)
                spSpin[i]  = (Random.nextFloat() - 0.5f) * sp.sparkSpin
                spZ[i]     = (Random.nextFloat() - 0.5f) * sp.sparkZ
                spBaseSize[i] = 2.0f + Random.nextFloat() * 4.5f
                sparkCPU[i * 10 + 9] = Random.nextInt(glyphCount.coerceAtLeast(1)).toFloat()
            }
        }

        // atlas ký tự: N ô 64px, chỉ dùng ký tự máy có font; thiếu thì dùng bộ dự phòng
        private fun buildAtlas(): Int {
            val p = Paint(Paint.ANTI_ALIAS_FLAG).apply {
                typeface = Typeface.create("serif", Typeface.BOLD)
                textSize = 42f
                color = Color.WHITE
                textAlign = Paint.Align.CENTER
            }
            var syms = G_SYMBOLS.map { it.toString() }.filter { p.hasGlyph(it) }
            if (syms.isEmpty()) syms = G_SYMBOLS_FALLBACK.map { it.toString() }.filter { p.hasGlyph(it) }
            if (syms.isEmpty()) syms = listOf("+")
            syms = syms.take(32)
            val count = syms.size
            val cellW = 64
            // Atlas width must match the number of glyphs actually drawn, otherwise the
            // fragment shader (which divides by uSymCount = count) samples beyond the
            // glyph's real region and the point sprite renders at a fraction of its
            // intended size (glyphs appear tiny).
            val bmpW = count * cellW
            val bmp = Bitmap.createBitmap(bmpW, 64, Bitmap.Config.ARGB_8888)
            val cv = Canvas(bmp)
            val fm = p.fontMetrics
            val baseY = 32f - (fm.ascent + fm.descent) / 2f
            syms.forEachIndexed { i, s -> cv.drawText(s, i * cellW + 32f, baseY, p) }

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
            return count
        }

        private fun releaseGL() {
            try {
                if (dpy != EGL14.EGL_NO_DISPLAY) {
                    if (glReady && ctx != EGL14.EGL_NO_CONTEXT && surf != EGL14.EGL_NO_SURFACE) {
                        EGL14.eglMakeCurrent(dpy, surf, surf, ctx)
                        if (vboStruct != 0) GLES20.glDeleteBuffers(1, intArrayOf(vboStruct), 0)
                        if (vboSpark != 0) GLES20.glDeleteBuffers(1, intArrayOf(vboSpark), 0)
                        GLES20.glDeleteTextures(1, intArrayOf(tex), 0)
                        if (progStruct != 0) GLES20.glDeleteProgram(progStruct)
                        if (progSpark != 0) GLES20.glDeleteProgram(progSpark)
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
                val dt = ((now - lastT) / 1000f).coerceIn(0f, 0.05f)
                lastT = now
                animTime += dt

                // cập nhật góc xoay 4 layer
                val spin = SPELLS[spellIndex].spin
                for (l in 0 until 4) {
                    angles[l] += speed * spin[l] * dt
                    cosSin[l * 2] = cos(angles[l])
                    cosSin[l * 2 + 1] = sin(angles[l])
                }

                // reveal
                if (reveal < 1f) reveal = (reveal + dt * 0.85f).coerceAtMost(1f)
                val ease = reveal * reveal * (3f - 2f * reveal)
                val breathe = 1f + 0.015f * sin(animTime * 1.6f)
                val scaleR = ease * breathe

                // waves
                val iter = waves.iterator()
                while (iter.hasNext()) {
                    val wv = iter.next()
                    wv.radius += dt * wv.speed
                    if (wv.radius > G_R * 1.8f) iter.remove()
                }

                if (!EGL14.eglMakeCurrent(dpy, surf, surf, ctx)) return
                GLES20.glViewport(0, 0, w, h)
                GLES20.glClearColor(0f, 0f, 0f, 1f)
                GLES20.glClear(GLES20.GL_COLOR_BUFFER_BIT)

                if (scaleR > 0.001f) {
                    // hover parallax chỉ áp khi KHÔNG kéo — tránh làm trôi tâm khi orbit,
                    // nhưng điểm sáng (uHover) vẫn bật để ngón tay rực lên khi chạm
                    val hvx = if (hoverActive && !dragging) hoverX * 0.18f else 0f
                    val hvy = if (hoverActive && !dragging) hoverY * 0.18f else 0f

                    // quán tính orbit khi thả tay
                    if (!dragging) {
                        // 1) tiếp tục xoay theo vận tốc đã có, giảm dần
                        orbitYaw += velYaw
                        orbitPitch = (orbitPitch + velPitch).coerceIn(-75f, 75f)
                        velYaw *= 0.92f
                        velPitch *= 0.92f
                        if (abs(velYaw) < 0.05f) velYaw = 0f
                        if (abs(velPitch) < 0.05f) velPitch = 0f

                        // 2) sau khi quán tính tắt, tự động về 0
                        if (velYaw == 0f && velPitch == 0f) {
                            orbitYaw *= 0.94f
                            orbitPitch *= 0.94f
                            if (abs(orbitYaw) < 0.05f) orbitYaw = 0f
                            if (abs(orbitPitch) < 0.05f) orbitPitch = 0f
                        }
                    }

                    Matrix.setIdentityM(mv, 0)
                    Matrix.translateM(mv, 0, -hvx, -hvy, -camZ)
                    Matrix.rotateM(mv, 0, orbitYaw, 0f, 1f, 0f)
                    Matrix.rotateM(mv, 0, orbitPitch, 1f, 0f, 0f)
                    Matrix.scaleM(mv, 0, scaleR, scaleR, scaleR)

                    val sizeIn = 0.55f + 0.45f * ease
                    val hoverFlag = if (hoverActive) 1f else 0f

                    GLES20.glEnable(GLES20.GL_BLEND)
                    GLES20.glBlendFuncSeparate(
                        GLES20.GL_SRC_ALPHA, GLES20.GL_ONE, GLES20.GL_ZERO, GLES20.GL_ONE
                    )
                    GLES20.glDepthMask(false)

                    GLES20.glActiveTexture(GLES20.GL_TEXTURE0)
                    GLES20.glBindTexture(GLES20.GL_TEXTURE_2D, tex)

                    // ── HẠT DỰNG HÌNH ──
                    GLES20.glUseProgram(progStruct)
                    GLES20.glUniformMatrix4fv(uMV, 1, false, mv, 0)
                    GLES20.glUniformMatrix4fv(uProj, 1, false, proj, 0)
                    GLES20.glUniform1f(uPRs, pixelRatio)
                    GLES20.glUniform2fv(uCosSin, 4, cosSin, 0)
                    GLES20.glUniform3fv(uBaseColor, 1, baseColorArr, 0)
                    GLES20.glUniform3fv(uCoreColor, 1, coreColorArr, 0)
                    GLES20.glUniform1f(uScale, 1f)
                    GLES20.glUniform3f(uHover, hoverX, hoverY, hoverFlag)
                    GLES20.glUniform1f(uHoverR2, G_HOVER_R * G_HOVER_R)
                    GLES20.glUniform1f(uHoverR, G_HOVER_R)
                    GLES20.glUniform1f(uSizeIn, sizeIn)
                    GLES20.glUniform1f(uReveal, ease)
                    GLES20.glUniform1f(uSymCountS, glyphCount.toFloat())
                    GLES20.glUniform1i(uTex, 0)

                    GLES20.glBindBuffer(GLES20.GL_ARRAY_BUFFER, vboStruct)
                    val stride = 9 * 4
                    GLES20.glEnableVertexAttribArray(aPs)
                    GLES20.glVertexAttribPointer(aPs, 4, GLES20.GL_FLOAT, false, stride, 0)
                    GLES20.glEnableVertexAttribArray(aXs)
                    GLES20.glVertexAttribPointer(aXs, 4, GLES20.GL_FLOAT, false, stride, 16)
                    GLES20.glEnableVertexAttribArray(aSyms)
                    GLES20.glVertexAttribPointer(aSyms, 1, GLES20.GL_FLOAT, false, stride, 32)
                    GLES20.glDrawArrays(GLES20.GL_POINTS, 0, G_PARTICLES)
                    GLES20.glDisableVertexAttribArray(aPs)
                    GLES20.glDisableVertexAttribArray(aXs)
                    GLES20.glDisableVertexAttribArray(aSyms)

                    // ── TÀN LỬA ──
                    updateSparks(dt, ease, scaleR)
                    if (activeSparks > 0) {
                        GLES20.glUseProgram(progSpark)
                        GLES20.glUniformMatrix4fv(uMV, 1, false, mv, 0)
                        GLES20.glUniformMatrix4fv(uProj, 1, false, proj, 0)
                        GLES20.glUniform1f(uPRk, pixelRatio)
                        GLES20.glUniform1f(uSymCountK, glyphCount.toFloat())

                        if (vboSpark == 0) {
                            val ids = IntArray(1); GLES20.glGenBuffers(1, ids, 0); vboSpark = ids[0]
                        }
                        val sBuf = ByteBuffer.allocateDirect(G_SPARKS * 10 * 4)
                            .order(ByteOrder.nativeOrder()).asFloatBuffer()
                        sBuf.put(sparkCPU); sBuf.position(0)
                        GLES20.glBindBuffer(GLES20.GL_ARRAY_BUFFER, vboSpark)
                        GLES20.glBufferData(GLES20.GL_ARRAY_BUFFER, G_SPARKS * 10 * 4, sBuf, GLES20.GL_DYNAMIC_DRAW)

                        val sStride = 10 * 4
                        GLES20.glEnableVertexAttribArray(aPk)
                        GLES20.glVertexAttribPointer(aPk, 4, GLES20.GL_FLOAT, false, sStride, 0)
                        GLES20.glEnableVertexAttribArray(aColk)
                        GLES20.glVertexAttribPointer(aColk, 3, GLES20.GL_FLOAT, false, sStride, 16)
                        GLES20.glEnableVertexAttribArray(aSAk)
                        GLES20.glVertexAttribPointer(aSAk, 2, GLES20.GL_FLOAT, false, sStride, 28)
                        GLES20.glEnableVertexAttribArray(aSymk)
                        GLES20.glVertexAttribPointer(aSymk, 1, GLES20.GL_FLOAT, false, sStride, 36)
                        GLES20.glDrawArrays(GLES20.GL_POINTS, 0, activeSparks)
                        GLES20.glDisableVertexAttribArray(aPk)
                        GLES20.glDisableVertexAttribArray(aColk)
                        GLES20.glDisableVertexAttribArray(aSAk)
                        GLES20.glDisableVertexAttribArray(aSymk)
                    }

                    GLES20.glDepthMask(true)
                }

                EGL14.eglSwapBuffers(dpy, surf)
            } catch (e: Exception) {
                // bỏ qua khung lỗi
            }
        }

        // Tính toán tàn lửa trên CPU: vị trí, màu, size, alpha, sym
        // Layout 10 float / spark: [0..2]=pos, [3]=pad, [4..6]=rgb, [7]=size, [8]=alpha, [9]=sym
        private fun updateSparks(dt: Float, ease: Float, scaleR: Float) {
            val sp = SPELLS[spellIndex]
            val orbit = sp.sparkOrbit
            val sizeMul = sp.sparkSize
            val pr = baseColorArr[0]; val pg = baseColorArr[1]; val pb = baseColorArr[2]
            val cr = coreColorArr[0]; val cg = coreColorArr[1]; val cb = coreColorArr[2]
            val coreR = cr * 0.55f + 0.45f
            val coreG = cg * 0.55f + 0.45f
            val coreB = cb * 0.55f + 0.45f

            for (i in 0 until activeSparks) {
                spLife[i] += spRate[i] * dt
                if (spLife[i] >= 1f) {
                    spAngle[i] = Random.nextFloat() * (2f * PI).toFloat()
                    spLife[i] = 0f
                    spRate[i] = sp.sparkRateLo + Random.nextFloat() * (sp.sparkRateHi - sp.sparkRateLo)
                    spSpin[i] = (Random.nextFloat() - 0.5f) * sp.sparkSpin
                    spZ[i] = (Random.nextFloat() - 0.5f) * sp.sparkZ
                }
                spAngle[i] += spSpin[i] * dt

                val life = spLife[i]
                val r = if (orbit) (0.80f + life * 0.45f) else (0.04f + life * 1.24f)
                val rr = r * G_R * scaleR
                val x = cos(spAngle[i]) * rr
                val y = sin(spAngle[i]) * rr
                val z = spZ[i] * scaleR
                val fade = sin(PI.toFloat() * life)
                val mixS = life * 0.65f
                val o = i * 10
                sparkCPU[o]     = x
                sparkCPU[o + 1] = y
                sparkCPU[o + 2] = z
                sparkCPU[o + 3] = 0f
                sparkCPU[o + 4] = coreR + (pr - coreR) * mixS
                sparkCPU[o + 5] = coreG + (pg - coreG) * mixS
                sparkCPU[o + 6] = coreB + (pb - coreB) * mixS
                sparkCPU[o + 7] = spBaseSize[i] * sizeMul * fade * (0.4f + 0.6f * ease)
                sparkCPU[o + 8] = 0.85f * fade * ease
                // [o + 9] = sym, đã set trong respawnAllSparks, giữ nguyên
            }
        }
    }
}
