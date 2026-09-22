package com.swarm.wallpaper

import android.app.WallpaperManager
import android.content.Context
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Paint
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.os.PowerManager
import android.os.SystemClock
import android.service.wallpaper.WallpaperService
import android.view.MotionEvent
import android.view.SurfaceHolder
import kotlin.math.PI
import kotlin.math.cos
import kotlin.math.floor
import kotlin.math.max
import kotlin.math.min
import kotlin.math.sin
import kotlin.random.Random

// ───────────────────────── CẤU HÌNH (chỉnh ở đây) ─────────────────────────
private const val GS_FPS = 60
private const val GS_FPS_SAVER = 15
private const val GS_TRANSITION_MS = 850f
private const val GS_FOCAL = 520f
private const val GS_CHARS = "⌖⎋⍕⌬⧉⧇⧻⧼⧽"
private const val GS_CHARS_FALLBACK = "✦✧◆◇○△□+×"

private fun rand(a: Float = 1f, b: Float = 0f) = b + Random.nextFloat() * (a - b)
private fun clamp(v: Float, a: Float, b: Float) = max(a, min(b, v))
private fun lerp(a: Float, b: Float, t: Float) = a + (b - a) * t
private fun ease(t: Float) = t * t * (3f - 2f * t)

private class Vec3(var x: Float = 0f, var y: Float = 0f, var z: Float = 0f)

private class Glyph(val id: Int, private val chars: String) {
    var char = chars[(Random.nextFloat() * chars.length).toInt()]
    var displayChar = char
    val seed = rand(1000f)
    var phase = rand((PI * 2).toFloat())
    var speed = rand(0.8f, 0.25f)
    var size = rand(26f, 12f)
    var life = rand(9f, 4f)
    var age = rand(life, 0f)
    var glitchMs = rand(420f, 140f)
    var glitchPulse = 0f
    val from = Vec3()
    val to = Vec3()
    val p = Vec3()

    init {
        val pos = Glyphs.positionForMode(0, 0f, id, seed, phase, speed, 1080f, 1920f)
        p.x = pos.x; p.y = pos.y; p.z = pos.z
    }

    fun reset() {
        age = 0f
        life = rand(10f, 5f)
        glitchMs = rand(420f, 140f)
        char = chars[(Random.nextFloat() * chars.length).toInt()]
        displayChar = char
        phase = rand((PI * 2).toFloat())
        speed = rand(0.9f, 0.3f)
        size = rand(26f, 12f)
    }
}

// tính vị trí theo mode — tách riêng để dùng cả lúc init
private object Glyphs {
    fun positionForMode(
        mode: Int, t: Float, id: Int, seed: Float, phase: Float, speed: Float, w: Float, h: Float
    ): Vec3 {
        val minDim = min(w, h)
        val aspectX = max(1f, w / max(1f, h))

        if (mode == 0) { // ORBIT
            val ring = 0.13f + ((id % 12) / 11f) * 0.42f
            val radius = minDim * ring
            val a = phase + t * speed * 0.34f + (id % 12) * PI.toFloat() / 6f
            val wobble = sin(t * 0.7f + seed) * minDim * 0.035f
            return Vec3(
                cos(a) * (radius + wobble) * aspectX,
                sin(a) * radius * 0.58f,
                130f + sin(a * 1.7f + seed) * 310f
            )
        }
        if (mode == 1) { // DRIFT
            val spanX = w * 0.72f
            val spanY = h * 0.62f
            val x = sin(t * 0.13f * speed + seed * 0.7f) * spanX + cos(t * 0.05f + seed) * spanX * 0.25f
            val y = cos(t * 0.11f * speed + seed * 1.2f) * spanY + sin(t * 0.07f + seed * 0.3f) * spanY * 0.22f
            val z = 80f + ((sin(t * 0.19f + seed * 2.2f) + 1f) * 0.5f) * 520f
            return Vec3(x, y, z)
        }
        if (mode == 2) { // MATRIX DEPTH
            val lane = (id % 13) - 6
            val col = lane * (w / 14f)
            val travel = ((t * (90f + speed * 130f) + seed * 800f).mod(h * 1.7f)) - h * 0.85f
            val pulse = sin(t * 0.8f + seed) * 18f
            val depthCycle = (t * (70f + speed * 55f) + seed * 500f).mod(720f)
            return Vec3(col + pulse, travel, 40f + depthCycle)
        }
        // PULSE
        val branch = id % 12
        val layer = id / 12
        val baseR = minDim * (0.10f + (layer % 10) * 0.035f)
        val pulse = 1f + sin(t * 1.35f + layer * 0.45f + seed) * 0.16f
        val angle = branch * PI.toFloat() / 6f + sin(t * 0.35f + layer * 0.2f) * 0.22f
        return Vec3(
            cos(angle) * baseR * pulse * aspectX,
            sin(angle) * baseR * pulse,
            120f + sin(t * 1.15f + branch * 0.5f + layer) * 260f
        )
    }
}

class GlyphSpaceWallpaperService : WallpaperService() {

    override fun onCreateEngine(): Engine = GEngine()

    private inner class GEngine : Engine() {
        private val handler = Handler(Looper.getMainLooper())
        private val pm = getSystemService(Context.POWER_SERVICE) as PowerManager

        private var shown = false
        private var w = 0f
        private var h = 0f

        private val glyphs = ArrayList<Glyph>()
        private var modeIndex = 0
        private var transitioning = false
        private var transitionT = 0f
        private var transitionStart = 0L
        private var timeSec = 0f
        private var lastT = 0L
        private var lastTouchAt = 0L

        private val camera = FloatArray(4) // x, y, tx, ty
        private val paint = Paint(Paint.ANTI_ALIAS_FLAG).apply { textAlign = Paint.Align.CENTER }
        private val bgPaint = Paint().apply { color = Color.BLACK }
        private val hsv = FloatArray(3).apply { this[1] = 0.96f }
        private val chars: String

        init {
            val test = Paint()
            chars = if (GS_CHARS.all { test.hasGlyph(it.toString()) }) GS_CHARS else GS_CHARS_FALLBACK
        }

        private val loop = object : Runnable {
            override fun run() {
                val t0 = SystemClock.uptimeMillis()
                drawFrame(t0)
                if (shown) {
                    val fps = if (pm.isPowerSaveMode) GS_FPS_SAVER else GS_FPS
                    handler.postDelayed(this, max(1L, 1000L / fps - (SystemClock.uptimeMillis() - t0)))
                }
            }
        }

        override fun onCreate(surfaceHolder: SurfaceHolder) {
            super.onCreate(surfaceHolder)
            setTouchEventsEnabled(true)
        }

        override fun onSurfaceChanged(holder: SurfaceHolder, format: Int, width: Int, height: Int) {
            super.onSurfaceChanged(holder, format, width, height)
            w = width.toFloat()
            h = height.toFloat()
            val targetCount = min(180, max(64, ((w * h) / 6200f).toInt()))
            while (glyphs.size < targetCount) glyphs.add(Glyph(glyphs.size, chars))
            while (glyphs.size > targetCount) glyphs.removeAt(glyphs.size - 1)
        }

        override fun onVisibilityChanged(visible: Boolean) {
            shown = visible
            handler.removeCallbacks(loop)
            if (visible) {
                lastT = SystemClock.uptimeMillis()
                handler.post(loop)
            }
        }

        override fun onSurfaceDestroyed(holder: SurfaceHolder) {
            shown = false
            handler.removeCallbacks(loop)
            super.onSurfaceDestroyed(holder)
        }

        override fun onDestroy() {
            shown = false
            handler.removeCallbacks(loop)
            super.onDestroy()
        }

        override fun onTouchEvent(event: MotionEvent) {
            if (event.actionMasked == MotionEvent.ACTION_DOWN) switchMode()
            super.onTouchEvent(event)
        }

        override fun onCommand(
            action: String?, x: Int, y: Int, z: Int, extras: Bundle?, resultRequested: Boolean
        ): Bundle? {
            if (action == WallpaperManager.COMMAND_TAP) switchMode()
            return super.onCommand(action, x, y, z, extras, resultRequested)
        }

        private fun switchMode() {
            val now = SystemClock.uptimeMillis()
            if (transitioning || now - lastTouchAt < 200) return
            lastTouchAt = now
            val next = (modeIndex + 1) % 4
            transitionStart = now
            transitionT = 0f
            transitioning = true
            for (g in glyphs) {
                g.from.x = g.p.x; g.from.y = g.p.y; g.from.z = g.p.z
                val target = Glyphs.positionForMode(
                    next, timeSec + GS_TRANSITION_MS / 1000f, g.id, g.seed, g.phase, g.speed, w, h
                )
                g.to.x = target.x; g.to.y = target.y; g.to.z = target.z
                if (Random.nextFloat() < 0.28f) g.glitchPulse = rand(0.2f, 0.08f)
            }
        }

        // ── khung hình ──
        private fun drawFrame(now: Long) {
            if (w < 1f) return
            val dt = ((now - lastT) / 1000f).coerceIn(0.001f, 0.05f)
            lastT = now
            timeSec += dt

            if (transitioning) {
                transitionT = clamp((now - transitionStart) / GS_TRANSITION_MS, 0f, 1f)
                if (transitionT >= 1f) {
                    modeIndex = (modeIndex + 1) % 4
                    transitioning = false
                    transitionT = 0f
                }
            }

            camera[0] += (camera[2] - camera[0]) * min(1f, dt * 4.5f)
            camera[1] += (camera[3] - camera[1]) * min(1f, dt * 4.5f)

            for (g in glyphs) updateGlyph(g, dt)
            glyphs.sortByDescending { it.p.z }

            val holder = surfaceHolder
            var c: Canvas? = null
            try {
                c = try { holder.lockHardwareCanvas() } catch (e: Exception) { holder.lockCanvas() }
                if (c != null) {
                    c.drawRect(0f, 0f, w, h, bgPaint)
                    for (g in glyphs) drawGlyph(c, g)
                }
            } catch (e: Exception) {
                // bỏ qua khung lỗi
            } finally {
                if (c != null) {
                    try { holder.unlockCanvasAndPost(c) } catch (e: Exception) { }
                }
            }
        }

        private fun updateGlyph(g: Glyph, dt: Float) {
            g.age += dt
            if (g.age > g.life) g.reset()

            if (transitioning) {
                val e = ease(transitionT)
                g.p.x = lerp(g.from.x, g.to.x, e)
                g.p.y = lerp(g.from.y, g.to.y, e)
                g.p.z = lerp(g.from.z, g.to.z, e)
            } else {
                val pos = Glyphs.positionForMode(modeIndex, timeSec, g.id, g.seed, g.phase, g.speed, w, h)
                g.p.x = pos.x; g.p.y = pos.y; g.p.z = pos.z
            }
            if (g.glitchPulse > 0f) g.glitchPulse = max(0f, g.glitchPulse - dt)
        }

        private fun drawGlyph(c: Canvas, g: Glyph) {
            val z = clamp(g.p.z, 0f, 900f)
            val scale = GS_FOCAL / (GS_FOCAL + z)
            val depthParallax = 0.35f + (1f - scale) * 1.4f

            var sx = w * 0.5f + (g.p.x - camera[0] * depthParallax) * scale
            var sy = h * 0.5f + (g.p.y - camera[1] * depthParallax) * scale

            val spawnMs = g.age * 1000f
            val spawning = spawnMs < g.glitchMs
            val glitching = spawning || g.glitchPulse > 0f

            if (glitching) {
                if (Random.nextFloat() < 0.72f) g.displayChar = chars[(Random.nextFloat() * chars.length).toInt()]
                sx += rand(4f, -4f)
                sy += rand(3f, -3f)
            } else {
                g.displayChar = g.char
            }

            val edgeFade = clamp(min(min(sx, w - sx), min(sy, h - sy)) / 80f, 0f, 1f)
            val lifeFadeIn = clamp(g.age / 0.5f, 0f, 1f)
            val lifeFadeOut = clamp((g.life - g.age) / 0.8f, 0f, 1f)
            var alpha = edgeFade * lifeFadeIn * lifeFadeOut * clamp(0.25f + scale * 0.95f, 0f, 1f)
            if (alpha <= 0.01f) return
            if (glitching) alpha *= rand(1f, 0.35f)

            val hueClock = (timeSec * 16f).mod(360f)
            val hue = (hueClock + (1f - scale) * 42f + (g.id % 9) * 2.4f).mod(360f)
            val fontSize = max(8f, g.size * scale)

            hsv[0] = hue
            hsv[2] = if (glitching) 0.90f else 0.82f // HSL→HSV xấp xỉ cho độ sáng L=76/69%
            paint.color = Color.HSVToColor((alpha.coerceIn(0f, 1f) * 255).toInt(), hsv)
            paint.textSize = fontSize
            val fm = paint.fontMetrics
            c.drawText(g.displayChar.toString(), sx, sy - (fm.ascent + fm.descent) / 2f, paint)
        }
    }
}
