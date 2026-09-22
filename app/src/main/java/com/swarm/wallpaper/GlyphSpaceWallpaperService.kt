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
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.os.PowerManager
import android.os.SystemClock
import android.service.wallpaper.WallpaperService
import android.view.MotionEvent
import android.view.SurfaceHolder
import android.view.ViewConfiguration
import java.nio.ByteBuffer
import java.nio.ByteOrder
import kotlin.math.PI
import kotlin.math.abs
import kotlin.math.atan2
import kotlin.math.exp
import kotlin.math.max
import kotlin.math.min
import kotlin.math.sqrt
import kotlin.random.Random

// ───────────────────────── KASCP3 / AI GLYPH SPACE ─────────────────────────
// 4 mode ORBIT / DRIFT / MATRIX / PULSE.
// Tối ưu theo kiến trúc: EGL + GLES2, VBO tĩnh, glyph texture atlas,
// adaptive FPS, power saver, sensor low-pass, lifecycle dừng render khi ẩn.

// ───────────────────────── CẤU HÌNH (chỉnh ở đây) ─────────────────────────
private const val K_FPS = 30
private const val K_FPS_ACTIVE = 60
private const val K_FPS_SAVER = 15
private const val K_TRANSITION_MS = 850L
private const val K_FOCAL = 520f
private const val K_MAX_DPR = 1.75f
private const val K_SYMBOLS = "⌖⎋⍕⌬⧉⧇⧻⧼⧽"
private const val K_SYMBOLS_FALLBACK = "✦✧◆◇○△□+×"
private const val K_SYMBOLS_MATRIX = "ﾊﾐﾋｰｳｼﾅﾓﾆｻﾜﾂｵﾘｱﾎﾃﾏｹﾒｴｶｷﾑﾕﾗ012789"
private const val K_SYMBOLS_MATRIX_FALLBACK = "01アイウエオカキクケコサシスセソ"
private const val K_TILT_SMOOTH_HZ = 4.5f
private const val K_TILT_X_PER_DEG = 1.35f
private const val K_TILT_Y_PER_DEG = 1.00f
private const val K_TILT_LIMIT_DEG = 35f
private const val K_SENSOR_STILL_EPS_DEG = 0.20f
private const val K_MODE_COUNT = 8

// Bảng màu palette 4 lớp (kỹ thuật từ Gemini): mỗi lớp có core + accent,
// shader nội suy giữa hai màu theo bán kính giống uCore/uAccent bên Gemini.
private val K_PALETTE_CORE = listOf("#00B95C", "#FFCC00", "#FF4641", "#3186FF")
private val K_PALETTE_ACCENT = listOf("#00A5B7", "#FF6B2B", "#D8627E", "#A975AA")

// ───────────────────────── SHADER ─────────────────────────
// aA = id, seed, phase, speed
// aB = size, life, ageOffset, symbolIndex
// Toàn bộ công thức hình học + màu + vòng đời chạy trên GPU.
private const val K_VERT = """
precision highp float;

attribute vec4 aA;
attribute vec4 aB;

uniform float uTime;
uniform float uMode;
uniform float uNextMode;
uniform float uTransitionT;
uniform float uTransitioning;
uniform float uTransitionSerial;
uniform float uTransitionStartTime;
uniform vec2 uSize;      // logical CSS-like pixels
uniform vec2 uCamera;    // logical pixels
uniform float uDpr;
uniform float uFocal;
uniform vec3 uCore[4];    // màu lõi 4 lớp (kỹ thuật Gemini)
uniform vec3 uAccent[4];  // màu viền 4 lớp
uniform float uHour;
uniform float uMinute;
uniform float uSecond;

varying vec4 vColor;
varying float vSym;
varying float vTexSel;

float hash11(float p) {
    return fract(sin(p * 127.1 + 311.7) * 43758.5453123);
}

float sat(float x) { return clamp(x, 0.0, 1.0); }
float ease3(float t) { return t * t * (3.0 - 2.0 * t); }

vec3 hsl2rgb(float h, float s, float l) {
    h = fract(h);
    vec3 rgb = clamp(abs(mod(h * 6.0 + vec3(0.0, 4.0, 2.0), 6.0) - 3.0) - 1.0, 0.0, 1.0);
    rgb = rgb * rgb * (3.0 - 2.0 * rgb);
    float c = (1.0 - abs(2.0 * l - 1.0)) * s;
    return (rgb - 0.5) * c + l;
}

vec3 posOrbit(float t, float id, float seed, float phase, float speed, float minDim, float aspectX) {
    float lane12 = mod(id, 12.0);
    float ring = 0.13 + (lane12 / 11.0) * 0.42;
    float radius = minDim * ring;
    float a = phase + t * speed * 0.34 + lane12 * 3.14159265359 / 6.0;
    float wobble = sin(t * 0.7 + seed) * minDim * 0.035;
    return vec3(
        cos(a) * (radius + wobble) * aspectX,
        sin(a) * radius * 0.58,
        130.0 + sin(a * 1.7 + seed) * 310.0
    );
}

vec3 posDrift(float t, float id, float seed, float phase, float speed) {
    float spanX = uSize.x * 0.72;
    float spanY = uSize.y * 0.62;
    float x = sin(t * 0.13 * speed + seed * 0.7) * spanX
            + cos(t * 0.05 + seed) * spanX * 0.25;
    float y = cos(t * 0.11 * speed + seed * 1.2) * spanY
            + sin(t * 0.07 + seed * 0.3) * spanY * 0.22;
    float z = 80.0 + ((sin(t * 0.19 + seed * 2.2) + 1.0) * 0.5) * 520.0;
    return vec3(x, y, z);
}

vec3 posMatrix(float t, float id, float seed, float speed, float colCount, float speedMul) {
    float lane = mod(id, colCount) - colCount * 0.5;
    float col = lane * (uSize.x / (colCount + 1.0));
    float travel = mod(t * (90.0 + speed * 130.0) * speedMul + seed * 800.0, uSize.y * 1.7)
                 - uSize.y * 0.85;
    float pulse = sin(t * 0.8 + seed) * 18.0;
    float depthCycle = mod(t * (70.0 + speed * 55.0) + seed * 500.0, 720.0);
    return vec3(col + pulse, travel, 40.0 + depthCycle);
}

vec3 posPulse(float t, float id, float seed, float minDim, float aspectX) {
    float branch = mod(id, 12.0);
    float layer = floor(id / 12.0);
    float baseR = minDim * (0.10 + mod(layer, 10.0) * 0.035);
    float pulse = 1.0 + sin(t * 1.35 + layer * 0.45 + seed) * 0.16;
    float angle = branch * 3.14159265359 / 6.0 + sin(t * 0.35 + layer * 0.2) * 0.22;
    return vec3(
        cos(angle) * baseR * pulse * aspectX,
        sin(angle) * baseR * pulse,
        120.0 + sin(t * 1.15 + branch * 0.5 + layer) * 260.0
    );
}

// Mặt đồng hồ hiện đại: vành 12 mốc giờ + kim giờ/phút/giây bằng glyph theo giờ thật,
// phần glyph còn lại orbit nhẹ quanh mặt số với z lệch tạo cảm giác 3D.
vec3 posClock(float t, float id, float seed, float phase, float speed, float minDim, float aspectX) {
    float faceR = minDim * 0.40;
    float role = mod(id, 40.0);

    if (role < 12.0) {
        float a = role / 12.0 * 6.28318530718 - 1.57079632679;
        return vec3(cos(a) * faceR * aspectX, sin(a) * faceR, 60.0 + sin(t * 0.5 + seed) * 20.0);
    }
    if (role < 20.0) {
        float hourAngle = (mod(uHour, 12.0) / 12.0 + uMinute / 720.0) * 6.28318530718 - 1.57079632679;
        float rr = ((role - 12.0) / 7.0) * faceR * 0.5;
        return vec3(cos(hourAngle) * rr * aspectX, sin(hourAngle) * rr, 40.0);
    }
    if (role < 30.0) {
        float minAngle = (uMinute / 60.0 + uSecond / 3600.0) * 6.28318530718 - 1.57079632679;
        float rr = ((role - 20.0) / 9.0) * faceR * 0.78;
        return vec3(cos(minAngle) * rr * aspectX, sin(minAngle) * rr, 45.0);
    }
    if (role < 36.0) {
        float secAngle = (uSecond / 60.0) * 6.28318530718 - 1.57079632679;
        float rr = ((role - 30.0) / 5.0) * faceR * 0.9;
        return vec3(cos(secAngle) * rr * aspectX, sin(secAngle) * rr, 50.0);
    }
    float lane = role - 36.0;
    float ring = faceR * (1.15 + lane * 0.12);
    float a = phase + t * speed * 0.22 + lane * 2.09;
    return vec3(cos(a) * ring * aspectX, sin(a) * ring * 0.9, 200.0 + sin(a * 1.4 + seed) * 260.0);
}

vec3 positionForMode(float mode, float t, float id, float seed, float phase, float speed) {
    float minDim = min(uSize.x, uSize.y);
    float aspectX = max(1.0, uSize.x / max(1.0, uSize.y));

    if (mode < 0.5) return posOrbit(t, id, seed, phase, speed, minDim, aspectX);
    if (mode < 1.5) return posDrift(t, id, seed, phase, speed);
    if (mode < 2.5) return posMatrix(t, id, seed, speed, 13.0, 1.0);
    if (mode < 3.5) return posPulse(t, id, seed, minDim, aspectX);
    if (mode < 4.5) { // ORBIT + PULSE lai
        float bl = 0.5 + 0.5 * sin(t * 0.18 + seed * 0.5);
        return mix(posOrbit(t, id, seed, phase, speed, minDim, aspectX),
                   posPulse(t, id, seed, minDim, aspectX), bl);
    }
    if (mode < 5.5) { // DRIFT + MATRIX lai
        float bl = 0.5 + 0.5 * sin(t * 0.15 + seed * 0.6);
        return mix(posDrift(t, id, seed, phase, speed),
                   posMatrix(t, id, seed, speed, 13.0, 1.0), bl);
    }
    if (mode < 6.5) return posClock(t, id, seed, phase, speed, minDim, aspectX);
    return posMatrix(t, id, seed, speed, 22.0, 1.6); // MATRIX REAL
}

void main() {
    float id = aA.x;
    float seed = aA.y;
    float phase = aA.z;
    float speed = aA.w;
    float baseSize = aB.x;
    float life = aB.y;
    float ageOffset = aB.z;
    float baseSym = aB.w;

    vec3 p = positionForMode(uMode, uTime, id, seed, phase, speed);
    if (uTransitioning > 0.5) {
        // Khớp HTML: from bị đóng băng tại lúc transition bắt đầu; to được lấy ở tStart + 850ms.
        // Vẫn không cần upload dynamic vertex data mỗi frame.
        vec3 p0 = positionForMode(uMode, uTransitionStartTime, id, seed, phase, speed);
        vec3 p1 = positionForMode(uNextMode, uTransitionStartTime + 0.85, id, seed, phase, speed);
        p = mix(p0, p1, ease3(uTransitionT));
    }

    float z = clamp(p.z, 0.0, 900.0);
    float scale = uFocal / (uFocal + z);
    float depthParallax = 0.35 + (1.0 - scale) * 1.4;

    float sx = uSize.x * 0.5 + (p.x - uCamera.x * depthParallax) * scale;
    float sy = uSize.y * 0.5 + (p.y - uCamera.y * depthParallax) * scale;

    // Vòng đời glyph: giữ fade/glitch spawn của HTML nhưng thực hiện ở shader.
    float age = mod(uTime + ageOffset, life);
    float glitchMs = mix(140.0, 420.0, hash11(seed + 17.0));
    float spawning = 1.0 - step(glitchMs, age * 1000.0);

    float transRand = hash11(id * 19.13 + uTransitionSerial * 71.7 + seed);
    float transGlitchDur = mix(0.08, 0.20, hash11(seed + uTransitionSerial * 3.1));
    float transitionGlitch = uTransitioning * (1.0 - step(0.28, transRand))
                           * (1.0 - step(transGlitchDur, uTransitionT * 0.85));
    float glitching = max(spawning, transitionGlitch);

    // Jitter + đổi ký tự theo frame khi glitch.
    float frameKey = floor(uTime * 30.0);
    float jr = hash11(seed * 3.1 + frameKey * 1.7 + id);
    float jy = hash11(seed * 5.7 + frameKey * 2.3 + id * 0.7);
    sx += glitching * (jr * 8.0 - 4.0);
    sy += glitching * (jy * 6.0 - 3.0);

    float edgeFade = sat(min(min(sx, uSize.x - sx), min(sy, uSize.y - sy)) / 80.0);
    float lifeFadeIn = sat(age / 0.5);
    float lifeFadeOut = sat((life - age) / 0.8);
    float alpha = edgeFade * lifeFadeIn * lifeFadeOut * sat(0.25 + scale * 0.95);
    if (glitching > 0.5) alpha *= mix(0.35, 1.0, hash11(frameKey + seed * 11.0));

    // Palette 4 lớp (kỹ thuật Gemini): chọn lớp theo thời gian, nội suy
    // core -> accent theo chiều sâu để giữ sắc độ ổn định thay vì HSL quay vòng.
    float layerF = mod(uTime * 0.08 + seed * 0.37, 4.0);
    int li = int(layerF);
    int ni = int(mod(layerF + 1.0, 4.0));
    float lt = fract(layerF);
    vec3 pc = mix(uCore[li], uCore[ni], lt);
    vec3 pa = mix(uAccent[li], uAccent[ni], lt);
    float coreMix = clamp((1.0 - scale) * 1.25, 0.0, 1.0);
    vec3 rgb = mix(pc, pa, coreMix);
    if (glitching > 0.5) rgb = min(vec3(1.0), rgb * 1.25);
    vColor = vec4(rgb, alpha);

    float glitchSym = floor(hash11(frameKey * 13.0 + seed * 31.0 + id) * 9.0);
    float swapGate = step(hash11(frameKey + seed * 7.0), 0.72);
    vSym = mix(baseSym, glitchSym, glitching * swapGate);

    float modeSel = mix(uMode, uNextMode, uTransitioning * step(0.5, uTransitionT));
    vTexSel = step(6.5, modeSel);
    float sizeMul = 1.0;
    if (modeSel > 0.5 && modeSel < 2.5) sizeMul = 2.0;      // DRIFT / MATRIX: baseSize x2
    else if (modeSel > 4.5 && modeSel < 5.5) sizeMul = 2.0; // DRIFT+MATRIX lai
    else if (modeSel > 6.5) sizeMul = 2.0;                  // MATRIX REAL

    // logical pixels -> clip space. Android viewport tự scale lên physical pixels.
    float cx = sx / uSize.x * 2.0 - 1.0;
    float cy = 1.0 - sy / uSize.y * 2.0;
    gl_Position = vec4(cx, cy, 0.0, 1.0);
    gl_PointSize = max(8.0, baseSize * sizeMul * scale) * uDpr;
}
"""

private const val K_FRAG = """
precision mediump float;
varying vec4 vColor;
varying float vSym;
varying float vTexSel;
uniform sampler2D uTex;
uniform sampler2D uTex2;

void main() {
    vec2 uv = gl_PointCoord;
    uv.x = (uv.x + vSym) / 16.0;
    vec4 t = vTexSel > 0.5 ? texture2D(uTex2, uv) : texture2D(uTex, uv);
    float a = t.a * vColor.a;
    if (a < 0.01) discard;
    vec3 brightRgb = min(vec3(1.0), vColor.rgb * 1.1);
    gl_FragColor = vec4(brightRgb, a);
}
"""

// ───────────────────────── WALLPAPER SERVICE ─────────────────────────
class GlyphSpaceWallpaperService : WallpaperService() {
    override fun onCreateEngine(): Engine = KEngine()

    private inner class KEngine : Engine() {
        private val handler = Handler(Looper.getMainLooper())
        private val pm = getSystemService(Context.POWER_SERVICE) as PowerManager
        private val sensorManager = getSystemService(Context.SENSOR_SERVICE) as SensorManager
        private val gravitySensor = sensorManager.getDefaultSensor(Sensor.TYPE_GRAVITY)
            ?: sensorManager.getDefaultSensor(Sensor.TYPE_ACCELEROMETER)
        private val touchSlop = ViewConfiguration.get(this@GlyphSpaceWallpaperService).scaledTouchSlop.toFloat()
        private val dpr: Float
            get() = min(resources.displayMetrics.density, K_MAX_DPR)

        private var shown = false
        private var glReady = false

        private var dpy: EGLDisplay = EGL14.EGL_NO_DISPLAY
        private var ctx: EGLContext = EGL14.EGL_NO_CONTEXT
        private var surf: EGLSurface = EGL14.EGL_NO_SURFACE
        private var prog = 0
        private var vbo = 0
        private var tex = 0
        private var tex2 = 0

        private var locA = -1
        private var locB = -1
        private var locTime = -1
        private var locMode = -1
        private var locNextMode = -1
        private var locTransitionT = -1
        private var locTransitioning = -1
        private var locTransitionSerial = -1
        private var locTransitionStartTime = -1
        private var locSize = -1
        private var locCamera = -1
        private var locDpr = -1
        private var locFocal = -1
        private var locCore = -1
        private var locAccent = -1
        private var locTex = -1
        private var locTex2 = -1
        private var locHour = -1
        private var locMinute = -1
        private var locSecond = -1

        private var w = 0
        private var h = 0
        private var glyphCount = 0

        // Palette 4 lớp (kỹ thuật Gemini): nạp hex -> float[3] trong init.
        private val coreArr = FloatArray(12)
        private val accentArr = FloatArray(12)

        private var lastFrameAt = 0L
        private var timeSec = 0f
        private var modeIndex = 0
        private var transitioning = false
        private var transitionStartAt = 0L
        private var transitionStartTimeSec = 0f
        private var transitionSerial = 0f
        private var lastModeSwitchAt = 0L

        // Camera parallax: cùng semantics với HTML (camera.x/y tính bằng logical px).
        private var cameraX = 0f
        private var cameraY = 0f
        private var targetCameraX = 0f
        private var targetCameraY = 0f
        private var launcherCameraX = 0f
        private var tiltCameraX = 0f

        // Sensor: baseline-relative để không phụ thuộc tư thế máy lúc wallpaper vừa hiện.
        private var sensorRegistered = false
        private val gravity = FloatArray(3)
        private var haveGravity = false
        private var lastSensorNs = 0L
        private var baseRoll = 0f
        private var basePitch = 0f
        private var haveBaseline = false
        private var lastRoll = 0f
        private var lastPitch = 0f
        private var lastSensorMotionAt = 0L

        private var downX = 0f
        private var downY = 0f
        private var dragging = false

        init {
            fillColors(coreArr, K_PALETTE_CORE)
            fillColors(accentArr, K_PALETTE_ACCENT)
        }

        private fun fillColors(dst: FloatArray, hex: List<String>) {
            hex.forEachIndexed { i, s ->
                val c = Color.parseColor(s)
                dst[i * 3] = Color.red(c) / 255f
                dst[i * 3 + 1] = Color.green(c) / 255f
                dst[i * 3 + 2] = Color.blue(c) / 255f
            }
        }

        private val loop = object : Runnable {
            override fun run() {
                val started = SystemClock.uptimeMillis()
                drawFrame(started)
                if (!shown) return

                val active = transitioning || dragging || started - lastSensorMotionAt < 220L
                val fps = when {
                    active -> K_FPS_ACTIVE
                    pm.isPowerSaveMode -> K_FPS_SAVER
                    else -> K_FPS
                }
                val spent = SystemClock.uptimeMillis() - started
                handler.postDelayed(this, max(1L, 1000L / fps - spent))
            }
        }

        private val sensorListener = object : SensorEventListener {
            override fun onSensorChanged(event: SensorEvent) {
                if (!shown || event.values.size < 3) return
                val nowNs = event.timestamp
                val dt = if (lastSensorNs == 0L) 0.02f
                else ((nowNs - lastSensorNs) * 1e-9f).coerceIn(0.001f, 0.1f)
                lastSensorNs = nowNs

                // TYPE_GRAVITY đã lọc; accelerometer fallback cần low-pass mạnh hơn.
                val hz = if (event.sensor.type == Sensor.TYPE_GRAVITY) 7f else 3.5f
                val a = 1f - exp(-2f * PI.toFloat() * hz * dt)
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
                val roll = Math.toDegrees(
                    atan2(gx.toDouble(), sqrt((gy * gy + gz * gz).toDouble()))
                ).toFloat()
                val pitch = Math.toDegrees(
                    atan2((-gy).toDouble(), sqrt((gx * gx + gz * gz).toDouble()))
                ).toFloat()

                if (!haveBaseline) {
                    baseRoll = roll
                    basePitch = pitch
                    lastRoll = roll
                    lastPitch = pitch
                    haveBaseline = true
                }

                val dr = (roll - baseRoll).coerceIn(-K_TILT_LIMIT_DEG, K_TILT_LIMIT_DEG)
                val dp = (pitch - basePitch).coerceIn(-K_TILT_LIMIT_DEG, K_TILT_LIMIT_DEG)
                tiltCameraX = -dr * K_TILT_X_PER_DEG
                targetCameraX = tiltCameraX + launcherCameraX
                targetCameraY = -dp * K_TILT_Y_PER_DEG

                if (abs(roll - lastRoll) + abs(pitch - lastPitch) > K_SENSOR_STILL_EPS_DEG) {
                    lastSensorMotionAt = SystemClock.uptimeMillis()
                }
                lastRoll = roll
                lastPitch = pitch
            }

            override fun onAccuracyChanged(sensor: Sensor?, accuracy: Int) = Unit
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
            rebuildGlyphVbo()
        }

        override fun onVisibilityChanged(visible: Boolean) {
            shown = visible
            handler.removeCallbacks(loop)
            if (visible) {
                val now = SystemClock.uptimeMillis()
                lastFrameAt = now
                lastSensorMotionAt = now
                haveBaseline = false
                registerSensors()
                handler.post(loop)
            } else {
                unregisterSensors()
                dragging = false
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

        // Tap đổi mode giống pointerdown của HTML, nhưng dùng touchSlop để tránh đổi mode khi launcher kéo trang.
        override fun onTouchEvent(event: MotionEvent) {
            when (event.actionMasked) {
                MotionEvent.ACTION_DOWN -> {
                    downX = event.x
                    downY = event.y
                    dragging = false
                }
                MotionEvent.ACTION_MOVE -> {
                    if (!dragging) {
                        val dx = event.x - downX
                        val dy = event.y - downY
                        dragging = sqrt(dx * dx + dy * dy) > touchSlop
                    }
                }
                MotionEvent.ACTION_UP -> {
                    if (!dragging) switchMode(SystemClock.uptimeMillis())
                    dragging = false
                }
                MotionEvent.ACTION_CANCEL -> dragging = false
            }
            super.onTouchEvent(event)
        }

        override fun onCommand(
            action: String?, x: Int, y: Int, z: Int, extras: Bundle?, resultRequested: Boolean
        ): Bundle? {
            if (action == WallpaperManager.COMMAND_TAP) switchMode(SystemClock.uptimeMillis())
            return super.onCommand(action, x, y, z, extras, resultRequested)
        }

        // Launcher offset chỉ thêm parallax rất nhỏ; không thay đổi mode.
        override fun onOffsetsChanged(
            xOffset: Float, yOffset: Float, xOffsetStep: Float, yOffsetStep: Float,
            xPixelOffset: Int, yPixelOffset: Int
        ) {
            launcherCameraX = (xOffset - 0.5f) * 26f
            targetCameraX = tiltCameraX + launcherCameraX
            super.onOffsetsChanged(xOffset, yOffset, xOffsetStep, yOffsetStep, xPixelOffset, yPixelOffset)
        }

        private fun switchMode(now: Long) {
            if (transitioning || now - lastModeSwitchAt < 250L) return
            lastModeSwitchAt = now
            transitionStartAt = now
            transitionStartTimeSec = timeSec
            transitionSerial += 1f
            transitioning = true
        }

        private fun registerSensors() {
            if (!sensorRegistered && gravitySensor != null) {
                sensorRegistered = sensorManager.registerListener(
                    sensorListener, gravitySensor, SensorManager.SENSOR_DELAY_GAME
                )
                lastSensorNs = 0L
                haveGravity = false
                haveBaseline = false
            }
        }

        private fun unregisterSensors() {
            if (sensorRegistered) sensorManager.unregisterListener(sensorListener)
            sensorRegistered = false
            lastSensorNs = 0L
            haveGravity = false
            haveBaseline = false
        }

        // ── EGL / GL ──
        private fun initEGL(holder: SurfaceHolder): Boolean {
            dpy = EGL14.eglGetDisplay(EGL14.EGL_DEFAULT_DISPLAY)
            if (dpy == EGL14.EGL_NO_DISPLAY) return false

            val ver = IntArray(2)
            if (!EGL14.eglInitialize(dpy, ver, 0, ver, 1)) return false

            val attrs = intArrayOf(
                EGL14.EGL_RENDERABLE_TYPE, EGL14.EGL_OPENGL_ES2_BIT,
                EGL14.EGL_RED_SIZE, 8,
                EGL14.EGL_GREEN_SIZE, 8,
                EGL14.EGL_BLUE_SIZE, 8,
                EGL14.EGL_ALPHA_SIZE, 8,
                EGL14.EGL_NONE
            )
            val cfgs = arrayOfNulls<EGLConfig>(1)
            val n = IntArray(1)
            if (!EGL14.eglChooseConfig(dpy, attrs, 0, cfgs, 0, 1, n, 0) || n[0] == 0) return false
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
            val shader = GLES20.glCreateShader(type)
            GLES20.glShaderSource(shader, src)
            GLES20.glCompileShader(shader)
            val ok = IntArray(1)
            GLES20.glGetShaderiv(shader, GLES20.GL_COMPILE_STATUS, ok, 0)
            if (ok[0] == 0) {
                GLES20.glDeleteShader(shader)
                return 0
            }
            return shader
        }

        private fun initGL(): Boolean {
            val vs = compile(GLES20.GL_VERTEX_SHADER, K_VERT)
            val fs = compile(GLES20.GL_FRAGMENT_SHADER, K_FRAG)
            if (vs == 0 || fs == 0) return false

            prog = GLES20.glCreateProgram()
            GLES20.glAttachShader(prog, vs)
            GLES20.glAttachShader(prog, fs)
            GLES20.glLinkProgram(prog)
            GLES20.glDeleteShader(vs)
            GLES20.glDeleteShader(fs)

            val ok = IntArray(1)
            GLES20.glGetProgramiv(prog, GLES20.GL_LINK_STATUS, ok, 0)
            if (ok[0] == 0) return false

            locA = GLES20.glGetAttribLocation(prog, "aA")
            locB = GLES20.glGetAttribLocation(prog, "aB")
            locTime = GLES20.glGetUniformLocation(prog, "uTime")
            locMode = GLES20.glGetUniformLocation(prog, "uMode")
            locNextMode = GLES20.glGetUniformLocation(prog, "uNextMode")
            locTransitionT = GLES20.glGetUniformLocation(prog, "uTransitionT")
            locTransitioning = GLES20.glGetUniformLocation(prog, "uTransitioning")
            locTransitionSerial = GLES20.glGetUniformLocation(prog, "uTransitionSerial")
            locTransitionStartTime = GLES20.glGetUniformLocation(prog, "uTransitionStartTime")
            locSize = GLES20.glGetUniformLocation(prog, "uSize")
            locCamera = GLES20.glGetUniformLocation(prog, "uCamera")
            locDpr = GLES20.glGetUniformLocation(prog, "uDpr")
            locFocal = GLES20.glGetUniformLocation(prog, "uFocal")
            locCore = GLES20.glGetUniformLocation(prog, "uCore")
            locAccent = GLES20.glGetUniformLocation(prog, "uAccent")
            locTex = GLES20.glGetUniformLocation(prog, "uTex")
            locTex2 = GLES20.glGetUniformLocation(prog, "uTex2")
            locHour = GLES20.glGetUniformLocation(prog, "uHour")
            locMinute = GLES20.glGetUniformLocation(prog, "uMinute")
            locSecond = GLES20.glGetUniformLocation(prog, "uSecond")

            buildAtlas()
            buildAtlas2()
            val ids = IntArray(1)
            GLES20.glGenBuffers(1, ids, 0)
            vbo = ids[0]
            if (w > 0 && h > 0) rebuildGlyphVbo()
            return true
        }

        // 16 cells × 64 px như gemlive.kt; shader chọn cell bằng vSym.
        private fun buildAtlas() {
            val p = Paint(Paint.ANTI_ALIAS_FLAG).apply {
                typeface = Typeface.create(Typeface.MONOSPACE, Typeface.NORMAL)
                textSize = 46f
                color = Color.WHITE
                textAlign = Paint.Align.CENTER
            }
            var syms = K_SYMBOLS.map { it.toString() }.filter { p.hasGlyph(it) }
            if (syms.isEmpty()) syms = K_SYMBOLS_FALLBACK.map { it.toString() }.filter { p.hasGlyph(it) }
            if (syms.isEmpty()) syms = listOf("+")
            syms = syms.take(16)

            val bmp = Bitmap.createBitmap(1024, 64, Bitmap.Config.ARGB_8888)
            val canvas = Canvas(bmp)
            val fm = p.fontMetrics
            val baseline = 32f - (fm.ascent + fm.descent) / 2f
            // Lấp đủ 16 cell bằng cách lặp symbol khả dụng để fallback font không tạo ô rỗng.
            for (i in 0 until 16) {
                canvas.drawText(syms[i % syms.size], i * 64f + 32f, baseline, p)
            }

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
        }

        // Atlas riêng cho MODE MATRIX REAL: bộ ký tự kiểu Matrix (katakana/số).
        private fun buildAtlas2() {
            val p = Paint(Paint.ANTI_ALIAS_FLAG).apply {
                typeface = Typeface.create(Typeface.MONOSPACE, Typeface.NORMAL)
                textSize = 46f
                color = Color.WHITE
                textAlign = Paint.Align.CENTER
            }
            var syms = K_SYMBOLS_MATRIX.map { it.toString() }.filter { p.hasGlyph(it) }
            if (syms.isEmpty()) syms = K_SYMBOLS_MATRIX_FALLBACK.map { it.toString() }.filter { p.hasGlyph(it) }
            if (syms.isEmpty()) syms = listOf("1")
            syms = syms.take(16)

            val bmp = Bitmap.createBitmap(1024, 64, Bitmap.Config.ARGB_8888)
            val canvas = Canvas(bmp)
            val fm = p.fontMetrics
            val baseline = 32f - (fm.ascent + fm.descent) / 2f
            for (i in 0 until 16) {
                canvas.drawText(syms[i % syms.size], i * 64f + 32f, baseline, p)
            }

            val ids = IntArray(1)
            GLES20.glGenTextures(1, ids, 0)
            tex2 = ids[0]
            GLES20.glBindTexture(GLES20.GL_TEXTURE_2D, tex2)
            GLUtils.texImage2D(GLES20.GL_TEXTURE_2D, 0, bmp, 0)
            GLES20.glGenerateMipmap(GLES20.GL_TEXTURE_2D)
            GLES20.glTexParameteri(GLES20.GL_TEXTURE_2D, GLES20.GL_TEXTURE_MIN_FILTER, GLES20.GL_LINEAR_MIPMAP_LINEAR)
            GLES20.glTexParameteri(GLES20.GL_TEXTURE_2D, GLES20.GL_TEXTURE_MAG_FILTER, GLES20.GL_LINEAR)
            GLES20.glTexParameteri(GLES20.GL_TEXTURE_2D, GLES20.GL_TEXTURE_WRAP_S, GLES20.GL_CLAMP_TO_EDGE)
            GLES20.glTexParameteri(GLES20.GL_TEXTURE_2D, GLES20.GL_TEXTURE_WRAP_T, GLES20.GL_CLAMP_TO_EDGE)
            bmp.recycle()
        }

        private fun rebuildGlyphVbo() {
            if (!glReady && prog == 0) return
            if (w <= 0 || h <= 0 || vbo == 0) return

            val logicalW = w / dpr
            val logicalH = h / dpr
            glyphCount = min(180, max(64, ((logicalW * logicalH) / 6200f).toInt()))

            // 8 float / glyph = 32 bytes. Buffer tĩnh: shader tự animate hoàn toàn.
            val buf = ByteBuffer.allocateDirect(glyphCount * 8 * 4)
                .order(ByteOrder.nativeOrder()).asFloatBuffer()
            val symCount = min(9, K_SYMBOLS.length)

            for (i in 0 until glyphCount) {
                val seed = Random.nextFloat() * 1000f
                val phase = Random.nextFloat() * (2f * PI.toFloat())
                val speed = 0.30f + Random.nextFloat() * 0.60f
                val size = 12f + Random.nextFloat() * 14f
                val life = 5f + Random.nextFloat() * 5f
                val ageOffset = Random.nextFloat() * life
                val sym = Random.nextInt(max(1, symCount)).toFloat()

                buf.put(i.toFloat())
                buf.put(seed)
                buf.put(phase)
                buf.put(speed)
                buf.put(size)
                buf.put(life)
                buf.put(ageOffset)
                buf.put(sym)
            }
            buf.position(0)

            if (dpy != EGL14.EGL_NO_DISPLAY && surf != EGL14.EGL_NO_SURFACE && ctx != EGL14.EGL_NO_CONTEXT) {
                if (!EGL14.eglMakeCurrent(dpy, surf, surf, ctx)) return
            }
            GLES20.glBindBuffer(GLES20.GL_ARRAY_BUFFER, vbo)
            GLES20.glBufferData(GLES20.GL_ARRAY_BUFFER, glyphCount * 8 * 4, buf, GLES20.GL_STATIC_DRAW)
        }

        // ── khung hình ──
        private fun drawFrame(now: Long) {
            if (!glReady || w <= 0 || h <= 0 || glyphCount <= 0) return
            try {
                val dt = ((now - lastFrameAt) / 1000f).coerceIn(0.001f, 0.05f)
                lastFrameAt = now
                timeSec += dt

                var transitionT = 0f
                if (transitioning) {
                    transitionT = ((now - transitionStartAt).toFloat() / K_TRANSITION_MS).coerceIn(0f, 1f)
                    if (transitionT >= 1f) {
                        modeIndex = (modeIndex + 1) % K_MODE_COUNT
                        transitioning = false
                        transitionT = 0f
                    }
                }

                val camA = 1f - exp(-2f * PI.toFloat() * K_TILT_SMOOTH_HZ * dt)
                cameraX += (targetCameraX - cameraX) * camA
                cameraY += (targetCameraY - cameraY) * camA

                if (!EGL14.eglMakeCurrent(dpy, surf, surf, ctx)) return
                GLES20.glViewport(0, 0, w, h)
                GLES20.glClearColor(0f, 0f, 0f, 1f)
                GLES20.glClear(GLES20.GL_COLOR_BUFFER_BIT)

                GLES20.glUseProgram(prog)
                GLES20.glUniform1f(locTime, timeSec)
                GLES20.glUniform1f(locMode, modeIndex.toFloat())
                GLES20.glUniform1f(locNextMode, ((modeIndex + 1) % K_MODE_COUNT).toFloat())
                GLES20.glUniform1f(locTransitionT, transitionT)
                GLES20.glUniform1f(locTransitioning, if (transitioning) 1f else 0f)
                GLES20.glUniform1f(locTransitionSerial, transitionSerial)
                GLES20.glUniform1f(locTransitionStartTime, transitionStartTimeSec)
                GLES20.glUniform2f(locSize, w / dpr, h / dpr)
                GLES20.glUniform2f(locCamera, cameraX, cameraY)
                GLES20.glUniform1f(locDpr, dpr)
                GLES20.glUniform1f(locFocal, K_FOCAL)
                GLES20.glUniform3fv(locCore, 4, coreArr, 0)
                GLES20.glUniform3fv(locAccent, 4, accentArr, 0)

                val cal = java.util.Calendar.getInstance()
                GLES20.glUniform1f(locHour, cal.get(java.util.Calendar.HOUR_OF_DAY).toFloat())
                GLES20.glUniform1f(locMinute, cal.get(java.util.Calendar.MINUTE).toFloat())
                GLES20.glUniform1f(
                    locSecond,
                    cal.get(java.util.Calendar.SECOND).toFloat() + cal.get(java.util.Calendar.MILLISECOND) / 1000f
                )

                GLES20.glActiveTexture(GLES20.GL_TEXTURE0)
                GLES20.glBindTexture(GLES20.GL_TEXTURE_2D, tex)
                GLES20.glUniform1i(locTex, 0)
                GLES20.glActiveTexture(GLES20.GL_TEXTURE1)
                GLES20.glBindTexture(GLES20.GL_TEXTURE_2D, tex2)
                GLES20.glUniform1i(locTex2, 1)

                GLES20.glEnable(GLES20.GL_BLEND)
                GLES20.glBlendFunc(GLES20.GL_SRC_ALPHA, GLES20.GL_ONE_MINUS_SRC_ALPHA)

                GLES20.glBindBuffer(GLES20.GL_ARRAY_BUFFER, vbo)
                GLES20.glEnableVertexAttribArray(locA)
                GLES20.glVertexAttribPointer(locA, 4, GLES20.GL_FLOAT, false, 32, 0)
                GLES20.glEnableVertexAttribArray(locB)
                GLES20.glVertexAttribPointer(locB, 4, GLES20.GL_FLOAT, false, 32, 16)
                GLES20.glDrawArrays(GLES20.GL_POINTS, 0, glyphCount)
                GLES20.glDisableVertexAttribArray(locA)
                GLES20.glDisableVertexAttribArray(locB)

                EGL14.eglSwapBuffers(dpy, surf)
            } catch (_: Exception) {
                // Wallpaper không được crash launcher vì một frame lỗi/EGL race.
            }
        }

        private fun releaseGL() {
            try {
                if (dpy != EGL14.EGL_NO_DISPLAY) {
                    if (ctx != EGL14.EGL_NO_CONTEXT && surf != EGL14.EGL_NO_SURFACE) {
                        EGL14.eglMakeCurrent(dpy, surf, surf, ctx)
                        if (vbo != 0) GLES20.glDeleteBuffers(1, intArrayOf(vbo), 0)
                        if (tex != 0) GLES20.glDeleteTextures(1, intArrayOf(tex), 0)
                        if (tex2 != 0) GLES20.glDeleteTextures(1, intArrayOf(tex2), 0)
                        if (prog != 0) GLES20.glDeleteProgram(prog)
                    }
                    EGL14.eglMakeCurrent(
                        dpy, EGL14.EGL_NO_SURFACE, EGL14.EGL_NO_SURFACE, EGL14.EGL_NO_CONTEXT
                    )
                    if (surf != EGL14.EGL_NO_SURFACE) EGL14.eglDestroySurface(dpy, surf)
                    if (ctx != EGL14.EGL_NO_CONTEXT) EGL14.eglDestroyContext(dpy, ctx)
                    EGL14.eglTerminate(dpy)
                }
            } catch (_: Exception) {
            }
            surf = EGL14.EGL_NO_SURFACE
            ctx = EGL14.EGL_NO_CONTEXT
            dpy = EGL14.EGL_NO_DISPLAY
            prog = 0
            vbo = 0
            tex = 0
            tex2 = 0
            glReady = false
        }
    }
}
