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
import java.nio.ByteBuffer
import java.nio.ByteOrder
import kotlin.math.PI
import kotlin.math.abs
import kotlin.math.atan2
import kotlin.math.exp
import kotlin.math.max
import kotlin.math.min
import kotlin.math.pow
import kotlin.math.sqrt
import kotlin.random.Random

// Port trực tiếp các tham số chính từ gemini.js.
private const val PARTICLE_COUNT = 80_000
private const val COLOR_SATURATION = 0.75f
private const val SCATTER_TOP = 1.0f
private const val SCATTER_BOTTOM = 0.15f // Web dùng khi scroll; wallpaper không có DOM scroll.
private const val ENTRANCE_DELAY_MS = 2_000L
private const val ENTRANCE_GROW_SPEED = 0.8f
private const val ENTRANCE_LINGER_SECONDS = 3.0f
private const val SPARK_CURVE_N = 0.7f
private const val ROUNDING_FACTOR = 0.18f
private const val PARTICLE_RADIUS = 120f
private const val WAVE_WIDTH = 75f
private const val WAVE_SPEED = 750f
private const val WAVE_END_RADIUS = 1500f
private const val AUTO_RETURN_FORCE = 0.15f
private const val AUTO_RETURN_FORCE_DECAY = 0.02f

// Android-specific scheduling / interaction adaptation.
private const val FPS_NORMAL = 30
private const val FPS_INTERACTION = 60
private const val FPS_SAVER = 15
private const val DRAG_DEG_PER_SCREEN = 150f
private const val INERTIA_FRICTION = 3.6f
private const val INERTIA_STOP_DPS = 2f
private const val TILT_MAX_DEG = 12f
private const val TILT_GAIN = 0.45f
private const val TILT_SMOOTH_HZ = 5f
private const val MAX_GPU_WAVES = 8

private data class Wave(var radius: Float, val stateIndex: Int)

/*
 * aP = angle, radialRandom^5, zRandom, sizeRandom.
 * Toàn bộ geometry/color/size loop của gemini.js được chuyển sang vertex shader để 80k hạt
 * không phải cập nhật FloatArray trên CPU mỗi frame.
 */
private const val VERTEX_SHADER = """
attribute vec4 aP;
uniform mat4 uMV;
uniform mat4 uProj;
uniform float uShape;
uniform float uScatter;
uniform float uBaseState;
uniform float uPixelRatio;
uniform vec4 uWave[8];
uniform vec3 uCore[4];
uniform vec3 uAccent[4];
varying vec3 vColor;

float smooth01(float x) {
    x = clamp(x, 0.0, 1.0);
    return x * x * (3.0 - 2.0 * x);
}

void main() {
    float angle = aP.x;
    float radial = aP.y;
    float ca = cos(angle);
    float sa = sin(angle);

    float e = 2.0 / uShape;
    float superX = pow(max(abs(ca), 0.0001), e) * sign(ca);
    float superY = pow(max(abs(sa), 0.0001), e) * sign(sa);

    float c2 = cos(2.0 * angle);
    float rounding = ${ROUNDING_FACTOR} * c2 * c2;
    float dx = superX * (1.0 - rounding) + ca * rounding;
    float dy = superY * (1.0 - rounding) + sa * rounding;

    float m = 1.0 + radial * uScatter - 0.04;
    float x = dx * ${PARTICLE_RADIUS} * m;
    float y = dy * ${PARTICLE_RADIUS} * m;
    float z = aP.z * ${PARTICLE_RADIUS} * (0.1 + 1.2 * uScatter);

    float dist3 = max(length(vec3(x, y, z)), 0.001);
    float state = uBaseState;
    float boost = 1.0;

    for (int i = 0; i < 8; ++i) {
        vec4 wave = uWave[i];
        if (wave.w > 0.5) {
            if (dist3 < wave.x) state = wave.y;
            float d = abs(dist3 - wave.x);
            if (d < wave.z) {
                float q = 1.0 - d / wave.z;
                boost = max(boost, 1.0 + q * 1.5);
            }
        }
    }

    // gemini.js: N = smoothstep(0,1, smoothstep(.08,.55, radial))
    float inner = smooth01((radial - 0.08) / (0.55 - 0.08));
    float mixT = smooth01(inner);
    vec3 core;
    vec3 accent;
    if (state < 0.5) {
        core = uCore[0]; accent = uAccent[0];
    } else if (state < 1.5) {
        core = uCore[1]; accent = uAccent[1];
    } else if (state < 2.5) {
        core = uCore[2]; accent = uAccent[2];
    } else {
        core = uCore[3]; accent = uAccent[3];
    }
    vec3 col = mix(core, accent, mixT);
    if (boost > 1.0) col = min(vec3(1.0), col * boost);
    vColor = col;

    float fade = 1.0 - clamp((dist3 - 40.0) / 220.0, 0.0, 1.0);
    float customSize = aP.w * (0.01 + fade * 1.8);

    vec4 mv = uMV * vec4(x, y, z, 1.0);
    gl_PointSize = customSize * uPixelRatio * (250.0 / max(1.0, -mv.z));
    gl_Position = uProj * mv;
}
"""

private const val FRAGMENT_SHADER = """
precision mediump float;
varying vec3 vColor;

void main() {
    float dist = length(gl_PointCoord - vec2(0.5));
    if (dist > 0.5) discard;
    float t = clamp((dist - 0.4) / 0.1, 0.0, 1.0);
    float smoothEdge = t * t * (3.0 - 2.0 * t);
    float alpha = 1.0 - smoothEdge;
    gl_FragColor = vec4(vColor, alpha);
}
"""

class GeminiWallpaperService : WallpaperService() {
    override fun onCreateEngine(): Engine = GeminiEngine()

    private inner class GeminiEngine : Engine() {
        private val handler = Handler(Looper.getMainLooper())
        private val powerManager = getSystemService(Context.POWER_SERVICE) as PowerManager
        private val sensorManager = getSystemService(Context.SENSOR_SERVICE) as SensorManager
        private val gravitySensor = sensorManager.getDefaultSensor(Sensor.TYPE_GRAVITY)
            ?: sensorManager.getDefaultSensor(Sensor.TYPE_ACCELEROMETER)
        private val pixelRatio = resources.displayMetrics.density

        private var visible = false
        private var glReady = false
        private var sensorRegistered = false

        private var display: EGLDisplay = EGL14.EGL_NO_DISPLAY
        private var context: EGLContext = EGL14.EGL_NO_CONTEXT
        private var surface: EGLSurface = EGL14.EGL_NO_SURFACE

        private var program = 0
        private var vbo = 0
        private var locP = -1
        private var locMV = -1
        private var locProj = -1
        private var locShape = -1
        private var locScatter = -1
        private var locBaseState = -1
        private var locPixelRatio = -1
        private var locWave = -1
        private var locCore = -1
        private var locAccent = -1

        private var widthPx = 0
        private var heightPx = 0
        private var cameraZ = 240f
        private val projection = FloatArray(16)
        private val modelView = FloatArray(16)

        // gemini.js timing state.
        private var shownAtMs = 0L
        private var lastFrameMs = 0L
        private var visibleAnimSeconds = 0f
        private var entranceScale = 0f
        private var morphPhase = (-PI / 2.0).toFloat()
        private var idleTime = 0f
        private var scatter = SCATTER_TOP
        private var targetScatter = SCATTER_TOP

        // gemini.js: C = state đã phủ toàn bộ; w = state mới nhất đã chọn.
        private var baseState = 3
        private var selectedState = 3
        private val waves = ArrayList<Wave>()
        private val waveUniforms = FloatArray(MAX_GPU_WAVES * 4)
        private val coreColors = FloatArray(12)
        private val accentColors = FloatArray(12)

        // Touch/mobile replacement for OrbitControls.
        private var touching = false
        private var interactionMode = false
        private var lastTouchX = 0f
        private var lastTouchY = 0f
        private var userYaw = 0f
        private var userPitch = 0f
        private var yawVelocity = 0f
        private var pitchVelocity = 0f
        private var returnForce = AUTO_RETURN_FORCE
        private var lastWaveAtMs = 0L
        private var velocityTracker: VelocityTracker? = null

        // Device tilt is Android-only parallax layered on top of the JS model.
        private val gravity = FloatArray(3)
        private var haveGravity = false
        private var lastSensorNs = 0L
        private var targetTiltPitch = 0f
        private var targetTiltRoll = 0f
        private var tiltPitch = 0f
        private var tiltRoll = 0f

        private var lastOffsetX = -1f
        private var lastOffsetAt = 0L
        private var launcherYaw = 0f

        init {
            fillSaturatedColors(coreColors, arrayOf("#00B95C", "#FFCC00", "#FF4641", "#3186FF"))
            fillSaturatedColors(accentColors, arrayOf("#00A5B7", "#FF6B2B", "#D8627E", "#A975AA"))
        }

        private val sensorListener = object : SensorEventListener {
            override fun onSensorChanged(event: SensorEvent) {
                if (!visible || event.values.size < 3) return
                val nowNs = event.timestamp
                val dt = if (lastSensorNs == 0L) 0.02f
                else ((nowNs - lastSensorNs) * 1e-9f).coerceIn(0.001f, 0.1f)
                lastSensorNs = nowNs

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
                val rawRoll = Math.toDegrees(
                    atan2(gx.toDouble(), sqrt((gy * gy + gz * gz).toDouble()))
                ).toFloat()
                val rawPitch = Math.toDegrees(
                    atan2((-gy).toDouble(), sqrt((gx * gx + gz * gz).toDouble()))
                ).toFloat()

                targetTiltRoll = (-rawRoll * TILT_GAIN).coerceIn(-TILT_MAX_DEG, TILT_MAX_DEG)
                targetTiltPitch = (-rawPitch * TILT_GAIN).coerceIn(-TILT_MAX_DEG, TILT_MAX_DEG)
            }

            override fun onAccuracyChanged(sensor: Sensor?, accuracy: Int) = Unit
        }

        private val frameLoop = object : Runnable {
            override fun run() {
                val frameStart = SystemClock.uptimeMillis()
                drawFrame(frameStart)
                if (!visible) return

                val interactionActive = touching ||
                    abs(yawVelocity) >= INERTIA_STOP_DPS ||
                    abs(pitchVelocity) >= INERTIA_STOP_DPS ||
                    (frameStart - lastOffsetAt in 0..180L)
                val fps = when {
                    interactionActive -> FPS_INTERACTION
                    powerManager.isPowerSaveMode -> FPS_SAVER
                    else -> FPS_NORMAL
                }
                val spent = SystemClock.uptimeMillis() - frameStart
                handler.postDelayed(this, max(1L, 1000L / fps - spent))
            }
        }

        override fun onCreate(surfaceHolder: SurfaceHolder) {
            super.onCreate(surfaceHolder)
            setTouchEventsEnabled(true)
        }

        override fun onSurfaceCreated(holder: SurfaceHolder) {
            super.onSurfaceCreated(holder)
            if (initEgl(holder)) glReady = initGl()
        }

        override fun onSurfaceChanged(holder: SurfaceHolder, format: Int, width: Int, height: Int) {
            super.onSurfaceChanged(holder, format, width, height)
            widthPx = width
            heightPx = height
            if (height <= 0) return
            val aspect = width.toFloat() / height.toFloat()
            cameraZ = max(240f, 170f / (0.767f * aspect))
            Matrix.perspectiveM(projection, 0, 75f, aspect, 0.1f, 2000f)
        }

        override fun onVisibilityChanged(visible: Boolean) {
            this.visible = visible
            handler.removeCallbacks(frameLoop)
            if (visible) {
                val now = SystemClock.uptimeMillis()
                shownAtMs = now
                lastFrameMs = now
                visibleAnimSeconds = 0f
                entranceScale = 0f
                morphPhase = (-PI / 2.0).toFloat()
                idleTime = 0f
                registerSensor()
                handler.post(frameLoop)
            } else {
                unregisterSensor()
                recycleVelocityTracker()
                touching = false
            }
        }

        override fun onSurfaceDestroyed(holder: SurfaceHolder) {
            visible = false
            handler.removeCallbacks(frameLoop)
            unregisterSensor()
            recycleVelocityTracker()
            releaseGl()
            super.onSurfaceDestroyed(holder)
        }

        override fun onDestroy() {
            visible = false
            handler.removeCallbacks(frameLoop)
            unregisterSensor()
            recycleVelocityTracker()
            releaseGl()
            super.onDestroy()
        }

        override fun onTouchEvent(event: MotionEvent) {
            when (event.actionMasked) {
                MotionEvent.ACTION_DOWN -> {
                    recycleVelocityTracker()
                    velocityTracker = VelocityTracker.obtain().also { it.addMovement(event) }
                    touching = true
                    interactionMode = true
                    returnForce = AUTO_RETURN_FORCE
                    lastTouchX = event.x
                    lastTouchY = event.y
                    yawVelocity = 0f
                    pitchVelocity = 0f

                    // JS dùng pointerdown: đổi state và bắn wave ngay cả khi sau đó là drag.
                    triggerWave(force = true)
                }

                MotionEvent.ACTION_MOVE -> {
                    velocityTracker?.addMovement(event)
                    val dx = event.x - lastTouchX
                    val dy = event.y - lastTouchY
                    userYaw += dx / max(1, widthPx).toFloat() * DRAG_DEG_PER_SCREEN
                    userPitch += dy / max(1, heightPx).toFloat() * DRAG_DEG_PER_SCREEN
                    userPitch = userPitch.coerceIn(-89f, 89f)
                    lastTouchX = event.x
                    lastTouchY = event.y
                }

                MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {
                    velocityTracker?.addMovement(event)
                    velocityTracker?.computeCurrentVelocity(1000)
                    val sx = max(1, widthPx).toFloat()
                    val sy = max(1, heightPx).toFloat()
                    yawVelocity = ((velocityTracker?.xVelocity ?: 0f) / sx * DRAG_DEG_PER_SCREEN)
                        .coerceIn(-360f, 360f)
                    pitchVelocity = ((velocityTracker?.yVelocity ?: 0f) / sy * DRAG_DEG_PER_SCREEN)
                        .coerceIn(-240f, 240f)
                    touching = false
                    recycleVelocityTracker()
                }
            }
            super.onTouchEvent(event)
        }

        override fun onOffsetsChanged(
            xOffset: Float,
            yOffset: Float,
            xOffsetStep: Float,
            yOffsetStep: Float,
            xPixelOffset: Int,
            yPixelOffset: Int
        ) {
            val now = SystemClock.uptimeMillis()
            if (!touching && lastOffsetX >= 0f) {
                val dx = xOffset - lastOffsetX
                if (abs(dx) < 0.5f) launcherYaw += dx * 45f
            }
            lastOffsetX = xOffset
            lastOffsetAt = now
            super.onOffsetsChanged(xOffset, yOffset, xOffsetStep, yOffsetStep, xPixelOffset, yPixelOffset)
        }

        override fun onCommand(
            action: String?,
            x: Int,
            y: Int,
            z: Int,
            extras: Bundle?,
            resultRequested: Boolean
        ): Bundle? {
            // Một số launcher gửi COMMAND_TAP thay vì MotionEvent. Tránh double-wave nếu vừa ACTION_DOWN.
            if (action == WallpaperManager.COMMAND_TAP && !touching) triggerWave(force = false)
            return super.onCommand(action, x, y, z, extras, resultRequested)
        }

        private fun triggerWave(force: Boolean = false) {
            val now = SystemClock.uptimeMillis()
            if (!force && now - lastWaveAtMs < 200L) return
            lastWaveAtMs = now
            selectedState = (selectedState + 1) % 4
            waves.add(Wave(0f, selectedState))
        }

        private fun updateWaves(dt: Float) {
            for (wave in waves) wave.radius += dt * WAVE_SPEED

            // JS chỉ commit C theo thứ tự queue khi wave đầu tiên đã phủ hết object.
            while (waves.isNotEmpty() && waves[0].radius >= WAVE_END_RADIUS) {
                baseState = waves[0].stateIndex
                waves.removeAt(0)
            }
        }

        private fun updateInteraction(dt: Float) {
            if (!touching) {
                if (abs(yawVelocity) > 0f || abs(pitchVelocity) > 0f) {
                    userYaw += yawVelocity * dt
                    userPitch = (userPitch + pitchVelocity * dt).coerceIn(-89f, 89f)
                    val damp = exp(-INERTIA_FRICTION * dt)
                    yawVelocity *= damp
                    pitchVelocity *= damp
                    if (abs(yawVelocity) < INERTIA_STOP_DPS) yawVelocity = 0f
                    if (abs(pitchVelocity) < INERTIA_STOP_DPS) pitchVelocity = 0f
                }

                // Tương đương ý đồ autoReturnToFront của JS: sau OrbitControls, camera trở lại mặt trước.
                if (interactionMode && yawVelocity == 0f && pitchVelocity == 0f) {
                    val yawError = returnYawError(userYaw)
                    val k = 1f - exp(-returnForce * 5f * dt)
                    userYaw += yawError * k
                    userPitch += (0f - userPitch) * k

                    if (abs(yawError) < 5f && abs(userPitch) < 5f) {
                        returnForce = max(0f, returnForce - dt * AUTO_RETURN_FORCE_DECAY)
                    }
                    if (returnForce <= 0.001f) {
                        val n = normalizeDegrees(userYaw)
                        userYaw = if (abs(n) <= 90f) 0f else if (n >= 0f) 180f else -180f
                        userPitch = 0f
                        interactionMode = false
                    }
                }
            }
        }

        private fun drawFrame(nowMs: Long) {
            if (!glReady || widthPx <= 0 || heightPx <= 0) return
            try {
                val dt = ((nowMs - lastFrameMs) / 1000f).coerceIn(0f, 0.1f)
                lastFrameMs = nowMs

                val delayPassed = nowMs - shownAtMs >= ENTRANCE_DELAY_MS
                if (delayPassed) {
                    visibleAnimSeconds += dt
                    entranceScale += (1f - entranceScale) * (dt * ENTRANCE_GROW_SPEED).coerceIn(0f, 1f)
                }

                // gemini.js chỉ bắt đầu morph + idle rotation sau entranceLingerSeconds.
                if (delayPassed && visibleAnimSeconds > ENTRANCE_LINGER_SECONDS) {
                    if (!interactionMode) idleTime += dt
                    val speed = (0.15f + (
                        (3.5f + SPARK_CURVE_N) / 2f +
                            (3.5f - SPARK_CURVE_N) / 2f * kotlin.math.sin(morphPhase) -
                            (SPARK_CURVE_N - 0.1f)
                        ).pow(2) * 0.15f) * 1.2f
                    morphPhase += dt * speed
                }

                scatter += (targetScatter - scatter) * 0.1f
                updateWaves(dt)
                updateInteraction(dt)

                val tiltA = 1f - exp(-2f * PI.toFloat() * TILT_SMOOTH_HZ * dt)
                tiltPitch += (targetTiltPitch - tiltPitch) * tiltA
                tiltRoll += (targetTiltRoll - tiltRoll) * tiltA

                if (!EGL14.eglMakeCurrent(display, surface, surface, context)) return
                GLES20.glViewport(0, 0, widthPx, heightPx)
                GLES20.glClearColor(0f, 0f, 0f, 1f)
                GLES20.glClear(GLES20.GL_COLOR_BUFFER_BIT)

                if (delayPassed && entranceScale > 0.0001f) {
                    buildModelView()
                    val shape = (3.5f + SPARK_CURVE_N) / 2f +
                        (3.5f - SPARK_CURVE_N) / 2f * kotlin.math.sin(morphPhase)
                    fillWaveUniforms()

                    GLES20.glUseProgram(program)
                    GLES20.glUniformMatrix4fv(locMV, 1, false, modelView, 0)
                    GLES20.glUniformMatrix4fv(locProj, 1, false, projection, 0)
                    GLES20.glUniform1f(locShape, shape)
                    GLES20.glUniform1f(locScatter, scatter)
                    GLES20.glUniform1f(locBaseState, baseState.toFloat())
                    GLES20.glUniform1f(locPixelRatio, pixelRatio)
                    GLES20.glUniform4fv(locWave, MAX_GPU_WAVES, waveUniforms, 0)
                    GLES20.glUniform3fv(locCore, 4, coreColors, 0)
                    GLES20.glUniform3fv(locAccent, 4, accentColors, 0)

                    GLES20.glEnable(GLES20.GL_BLEND)
                    GLES20.glBlendFunc(GLES20.GL_SRC_ALPHA, GLES20.GL_ONE)
                    GLES20.glDisable(GLES20.GL_DEPTH_TEST)

                    GLES20.glBindBuffer(GLES20.GL_ARRAY_BUFFER, vbo)
                    GLES20.glEnableVertexAttribArray(locP)
                    GLES20.glVertexAttribPointer(locP, 4, GLES20.GL_FLOAT, false, 16, 0)
                    GLES20.glDrawArrays(GLES20.GL_POINTS, 0, PARTICLE_COUNT)
                    GLES20.glDisableVertexAttribArray(locP)
                }

                EGL14.eglSwapBuffers(display, surface)
            } catch (_: Exception) {
                // Wallpaper service không được crash chỉ vì một frame/EGL transient lỗi.
            }
        }

        private fun buildModelView() {
            Matrix.setIdentityM(modelView, 0)
            Matrix.translateM(modelView, 0, 0f, 0f, -cameraZ)

            // Android parallax/background-page layer.
            Matrix.rotateM(modelView, 0, tiltPitch, 1f, 0f, 0f)
            Matrix.rotateM(modelView, 0, tiltRoll + launcherYaw, 0f, 1f, 0f)

            // OrbitControls-equivalent user control.
            Matrix.rotateM(modelView, 0, userPitch, 1f, 0f, 0f)
            Matrix.rotateM(modelView, 0, userYaw, 0f, 1f, 0f)

            // gemini.js idle object rotation:
            // r = I*.22; x=sin(2r)^3*.85, y=sin(r)^3*1.15, z=sin(r)^3*-.65 (radians).
            if (!interactionMode) {
                val r = idleTime * 0.22f
                val sx = kotlin.math.sin(r * 2f).pow(3) * 0.85f
                val sy = kotlin.math.sin(r).pow(3) * 1.15f
                val sz = kotlin.math.sin(r).pow(3) * -0.65f
                val radToDeg = (180f / PI.toFloat())
                Matrix.rotateM(modelView, 0, sx * radToDeg, 1f, 0f, 0f)
                Matrix.rotateM(modelView, 0, sy * radToDeg, 0f, 1f, 0f)
                Matrix.rotateM(modelView, 0, sz * radToDeg, 0f, 0f, 1f)
            }

            Matrix.scaleM(modelView, 0, entranceScale, entranceScale, entranceScale)
        }

        private fun fillWaveUniforms() {
            java.util.Arrays.fill(waveUniforms, 0f)
            // Nếu queue > GPU slots, giữ các wave mới nhất; baseState vẫn commit theo queue CPU.
            val start = max(0, waves.size - MAX_GPU_WAVES)
            var slot = 0
            for (i in start until waves.size) {
                val wave = waves[i]
                val o = slot * 4
                waveUniforms[o] = wave.radius
                waveUniforms[o + 1] = wave.stateIndex.toFloat()
                waveUniforms[o + 2] = WAVE_WIDTH
                waveUniforms[o + 3] = 1f
                slot++
            }
        }

        private fun initEgl(holder: SurfaceHolder): Boolean {
            display = EGL14.eglGetDisplay(EGL14.EGL_DEFAULT_DISPLAY)
            if (display == EGL14.EGL_NO_DISPLAY) return false
            val version = IntArray(2)
            if (!EGL14.eglInitialize(display, version, 0, version, 1)) return false

            val attrs = intArrayOf(
                EGL14.EGL_RENDERABLE_TYPE, EGL14.EGL_OPENGL_ES2_BIT,
                EGL14.EGL_RED_SIZE, 8,
                EGL14.EGL_GREEN_SIZE, 8,
                EGL14.EGL_BLUE_SIZE, 8,
                EGL14.EGL_ALPHA_SIZE, 8,
                EGL14.EGL_NONE
            )
            val configs = arrayOfNulls<EGLConfig>(1)
            val count = IntArray(1)
            if (!EGL14.eglChooseConfig(display, attrs, 0, configs, 0, 1, count, 0) || count[0] == 0) return false
            val config = configs[0] ?: return false

            context = EGL14.eglCreateContext(
                display,
                config,
                EGL14.EGL_NO_CONTEXT,
                intArrayOf(EGL14.EGL_CONTEXT_CLIENT_VERSION, 2, EGL14.EGL_NONE),
                0
            )
            surface = EGL14.eglCreateWindowSurface(
                display,
                config,
                holder.surface,
                intArrayOf(EGL14.EGL_NONE),
                0
            )
            if (context == EGL14.EGL_NO_CONTEXT || surface == EGL14.EGL_NO_SURFACE) return false
            return EGL14.eglMakeCurrent(display, surface, surface, context)
        }

        private fun initGl(): Boolean {
            val vs = compileShader(GLES20.GL_VERTEX_SHADER, VERTEX_SHADER)
            val fs = compileShader(GLES20.GL_FRAGMENT_SHADER, FRAGMENT_SHADER)
            if (vs == 0 || fs == 0) return false

            program = GLES20.glCreateProgram()
            GLES20.glAttachShader(program, vs)
            GLES20.glAttachShader(program, fs)
            GLES20.glLinkProgram(program)
            GLES20.glDeleteShader(vs)
            GLES20.glDeleteShader(fs)

            val linked = IntArray(1)
            GLES20.glGetProgramiv(program, GLES20.GL_LINK_STATUS, linked, 0)
            if (linked[0] == 0) return false

            locP = GLES20.glGetAttribLocation(program, "aP")
            locMV = GLES20.glGetUniformLocation(program, "uMV")
            locProj = GLES20.glGetUniformLocation(program, "uProj")
            locShape = GLES20.glGetUniformLocation(program, "uShape")
            locScatter = GLES20.glGetUniformLocation(program, "uScatter")
            locBaseState = GLES20.glGetUniformLocation(program, "uBaseState")
            locPixelRatio = GLES20.glGetUniformLocation(program, "uPixelRatio")
            locWave = GLES20.glGetUniformLocation(program, "uWave[0]")
            locCore = GLES20.glGetUniformLocation(program, "uCore[0]")
            locAccent = GLES20.glGetUniformLocation(program, "uAccent[0]")

            val data = ByteBuffer.allocateDirect(PARTICLE_COUNT * 4 * 4)
                .order(ByteOrder.nativeOrder())
                .asFloatBuffer()
            repeat(PARTICLE_COUNT) {
                val r = Random.nextFloat()
                data.put(Random.nextFloat() * 2f * PI.toFloat())
                data.put(r * r * r * r * r)
                data.put(Random.nextFloat() + Random.nextFloat() + Random.nextFloat() - 1.5f)
                data.put(0.8f + Random.nextFloat() * 1.2f)
            }
            data.position(0)

            val ids = IntArray(1)
            GLES20.glGenBuffers(1, ids, 0)
            vbo = ids[0]
            GLES20.glBindBuffer(GLES20.GL_ARRAY_BUFFER, vbo)
            GLES20.glBufferData(
                GLES20.GL_ARRAY_BUFFER,
                PARTICLE_COUNT * 4 * 4,
                data,
                GLES20.GL_STATIC_DRAW
            )
            return vbo != 0
        }

        private fun compileShader(type: Int, source: String): Int {
            val shader = GLES20.glCreateShader(type)
            GLES20.glShaderSource(shader, source)
            GLES20.glCompileShader(shader)
            val ok = IntArray(1)
            GLES20.glGetShaderiv(shader, GLES20.GL_COMPILE_STATUS, ok, 0)
            if (ok[0] == 0) {
                GLES20.glDeleteShader(shader)
                return 0
            }
            return shader
        }

        private fun releaseGl() {
            try {
                if (display != EGL14.EGL_NO_DISPLAY) {
                    if (context != EGL14.EGL_NO_CONTEXT && surface != EGL14.EGL_NO_SURFACE) {
                        EGL14.eglMakeCurrent(display, surface, surface, context)
                        if (vbo != 0) GLES20.glDeleteBuffers(1, intArrayOf(vbo), 0)
                        if (program != 0) GLES20.glDeleteProgram(program)
                    }
                    EGL14.eglMakeCurrent(
                        display,
                        EGL14.EGL_NO_SURFACE,
                        EGL14.EGL_NO_SURFACE,
                        EGL14.EGL_NO_CONTEXT
                    )
                    if (surface != EGL14.EGL_NO_SURFACE) EGL14.eglDestroySurface(display, surface)
                    if (context != EGL14.EGL_NO_CONTEXT) EGL14.eglDestroyContext(display, context)
                    EGL14.eglTerminate(display)
                }
            } catch (_: Exception) {
            }
            display = EGL14.EGL_NO_DISPLAY
            surface = EGL14.EGL_NO_SURFACE
            context = EGL14.EGL_NO_CONTEXT
            program = 0
            vbo = 0
            glReady = false
        }

        private fun registerSensor() {
            if (!sensorRegistered && gravitySensor != null) {
                sensorRegistered = sensorManager.registerListener(
                    sensorListener,
                    gravitySensor,
                    SensorManager.SENSOR_DELAY_GAME
                )
                lastSensorNs = 0L
            }
        }

        private fun unregisterSensor() {
            if (sensorRegistered) sensorManager.unregisterListener(sensorListener)
            sensorRegistered = false
            lastSensorNs = 0L
        }

        private fun recycleVelocityTracker() {
            velocityTracker?.recycle()
            velocityTracker = null
        }

        private fun fillSaturatedColors(dst: FloatArray, colors: Array<String>) {
            colors.forEachIndexed { index, value ->
                val c = Color.parseColor(value)
                val rgb = saturateHsl(
                    Color.red(c) / 255f,
                    Color.green(c) / 255f,
                    Color.blue(c) / 255f,
                    COLOR_SATURATION
                )
                dst[index * 3] = rgb[0]
                dst[index * 3 + 1] = rgb[1]
                dst[index * 3 + 2] = rgb[2]
            }
        }

        // Equivalent to THREE.Color.getHSL(); setHSL(h, s * colorSaturation, l).
        private fun saturateHsl(r: Float, g: Float, b: Float, multiplier: Float): FloatArray {
            val maxC = max(r, max(g, b))
            val minC = min(r, min(g, b))
            val l = (maxC + minC) * 0.5f
            if (maxC == minC) return floatArrayOf(l, l, l)

            val d = maxC - minC
            var s = if (l > 0.5f) d / (2f - maxC - minC) else d / (maxC + minC)
            var h = when (maxC) {
                r -> (g - b) / d + if (g < b) 6f else 0f
                g -> (b - r) / d + 2f
                else -> (r - g) / d + 4f
            } / 6f
            h = h - kotlin.math.floor(h)
            s = (s * multiplier).coerceIn(0f, 1f)

            if (s == 0f) return floatArrayOf(l, l, l)
            val q = if (l < 0.5f) l * (1f + s) else l + s - l * s
            val p = 2f * l - q
            return floatArrayOf(
                hueToRgb(p, q, h + 1f / 3f),
                hueToRgb(p, q, h),
                hueToRgb(p, q, h - 1f / 3f)
            )
        }

        private fun hueToRgb(p: Float, q: Float, input: Float): Float {
            var t = input
            if (t < 0f) t += 1f
            if (t > 1f) t -= 1f
            return when {
                t < 1f / 6f -> p + (q - p) * 6f * t
                t < 1f / 2f -> q
                t < 2f / 3f -> p + (q - p) * (2f / 3f - t) * 6f
                else -> p
            }
        }

        private fun normalizeDegrees(value: Float): Float {
            var v = value % 360f
            if (v > 180f) v -= 360f
            if (v < -180f) v += 360f
            return v
        }

        private fun returnYawError(value: Float): Float {
            val n = normalizeDegrees(value)
            val target = if (abs(n) <= 90f) 0f else if (n >= 0f) 180f else -180f
            return normalizeDegrees(target - n)
        }
    }
}
