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
import kotlin.math.abs
import kotlin.math.cos
import kotlin.math.max
import kotlin.math.min
import kotlin.math.sin
import kotlin.random.Random

// ───────────────────────── CẤU HÌNH (chỉnh ở đây) ─────────────────────────
private const val K_FPS = 30
private const val K_FPS_SAVER = 15
private const val K_SLOTS = 7              // số ký tự lặp lại trong mỗi cánh
private const val K_CHARS = "⌖⎋⍕⌬⧉⧇⧻⧼⧽"
private const val K_CHARS_FALLBACK = "✦✧◆◇○△□+×"
private const val K_FLASH_ON_TAP = true    // nháy nhẹ khi chạm đổi hiệu ứng

// 5 kiểu chuyển động — mỗi kiểu: số cánh đối xứng, có lật gương xen kẽ không, độ đậm vệt mờ
private data class KMode(val name: String, val arms: Int, val mirror: Boolean, val trail: Int)
private val K_MODES = listOf(
    KMode("KALEIDOSCOPE", 12, true, 26),   // xoay tròn êm, đối xứng cổ điển như bản gốc
    KMode("SPIRAL", 8, false, 34),         // ký tự trôi xoáy dần ra ngoài
    KMode("BURST", 10, true, 46),          // từng đợt sóng nổ tỏa tâm
    KMode("BREATHE", 6, true, 18),         // phồng xẹp chậm rãi, rất nhẹ nhàng
    KMode("RAIN", 12, false, 30)           // ký tự rơi theo chiều dọc, đối xứng gương
)

private fun rand(a: Float = 1f, b: Float = 0f) = b + Random.nextFloat() * (a - b)
private fun fmod(v: Float, m: Float): Float { val r = v % m; return if (r < 0f) r + m else r }

// một "ô" ký tự dùng chung cho mọi cánh, chỉ khác pha theo chỉ số cánh
private class Slot(val id: Int, chars: String) {
    val seed = rand(1000f)
    val phase = rand((PI * 2).toFloat())
    val speed = rand(1.1f, 0.5f)
    val baseSize = rand(30f, 11f)
    var char = chars[(Random.nextFloat() * chars.length).toInt()]
    var life = rand(4.5f, 1.5f)
    var age = rand(life, 0f)
}

class KaleidoWallpaperService : WallpaperService() {

    override fun onCreateEngine(): Engine = KEngine()

    private inner class KEngine : Engine() {
        private val handler = Handler(Looper.getMainLooper())
        private val pm = getSystemService(Context.POWER_SERVICE) as PowerManager

        private var shown = false
        private var w = 0f
        private var h = 0f
        private var startAt = 0L
        private var lastT = 0L
        private var timeSec = 0f
        private var modeIndex = 0
        private var lastTapAt = 0L
        private var flash = 0f

        private val chars: String
        private val slots: List<Slot>
        private val paint = Paint(Paint.ANTI_ALIAS_FLAG).apply { textAlign = Paint.Align.CENTER }
        private val trailPaint = Paint()
        private val hsv = FloatArray(3).apply { this[1] = 0.99f; this[2] = 0.70f }

        init {
            val test = Paint()
            chars = if (K_CHARS.all { test.hasGlyph(it.toString()) }) K_CHARS else K_CHARS_FALLBACK
            slots = (0 until K_SLOTS).map { Slot(it, chars) }
        }

        private val loop = object : Runnable {
            override fun run() {
                val t0 = SystemClock.uptimeMillis()
                drawFrame(t0)
                if (shown) {
                    val fps = if (pm.isPowerSaveMode) K_FPS_SAVER else K_FPS
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
            if (now - lastTapAt < 250) return
            lastTapAt = now
            modeIndex = (modeIndex + 1) % K_MODES.size
            if (K_FLASH_ON_TAP) flash = 1f
        }

        // ── khung hình ──
        private fun drawFrame(now: Long) {
            if (w < 1f) return
            val dt = ((now - lastT) / 1000f).coerceIn(0.001f, 0.05f)
            lastT = now
            timeSec += dt

            for (s in slots) {
                s.age += dt
                if (s.age > s.life) {
                    s.age = 0f
                    s.life = rand(4.5f, 1.5f)
                    s.char = chars[(Random.nextFloat() * chars.length).toInt()]
                }
            }

            val holder = surfaceHolder
            var c: Canvas? = null
            try {
                c = try { holder.lockHardwareCanvas() } catch (e: Exception) { holder.lockCanvas() }
                if (c != null) render(c, now)
            } catch (e: Exception) {
                // bỏ qua khung lỗi
            } finally {
                if (c != null) {
                    try { holder.unlockCanvasAndPost(c) } catch (e: Exception) { }
                }
            }
        }

        private fun render(c: Canvas, now: Long) {
            val mode = K_MODES[modeIndex]

            // vệt mờ: phủ đen bán trong suốt lên khung trước — nhẹ hơn nhiều so với bản gốc
            trailPaint.color = Color.argb(mode.trail, 0, 0, 0)
            c.drawRect(0f, 0f, w, h, trailPaint)

            val cx = w / 2f
            val cy = h / 2f
            val minDim = min(w, h)

            c.save()
            c.translate(cx, cy)
            for (arm in 0 until mode.arms) {
                c.save()
                c.rotate(arm * 360f / mode.arms)
                if (mode.mirror && arm % 2 == 1) c.scale(1f, -1f)
                for (slot in slots) drawSlot(c, slot, mode, arm, minDim)
                c.restore()
            }
            c.restore()

            // nháy nhẹ khi vừa đổi hiệu ứng
            if (flash > 0.01f) {
                c.drawColor(Color.argb((flash * 46f).toInt(), 255, 255, 255))
                flash = max(0f, flash - 0.06f)
            }

            // fade-in khi vừa mở màn hình
            val fi = ((now - startAt) / 700f).coerceIn(0f, 1f)
            if (fi < 1f) c.drawColor(Color.argb(((1f - fi) * 255f).toInt(), 0, 0, 0))
        }

        // vị trí + màu trong không gian cục bộ của 1 cánh, theo từng kiểu chuyển động
        private fun drawSlot(c: Canvas, s: Slot, mode: KMode, arm: Int, minDim: Float) {
            val t = timeSec
            val armPhase = arm * 0.37f
            var x = 0f; var y = 0f; var size = s.baseSize; var alpha = 1f

            when (K_MODES.indexOf(mode)) {
                0 -> { // KALEIDOSCOPE — quỹ đạo tròn êm nhiều tầng
                    val a = s.phase + t * s.speed * 0.5f + armPhase
                    val radius = minDim * (0.05f + (s.id % K_SLOTS) / K_SLOTS.toFloat() * 0.42f)
                    x = cos(a) * radius
                    y = sin(a) * radius * 0.62f
                    alpha = 0.55f + 0.45f * sin(t * 0.6f + s.seed)
                }
                1 -> { // SPIRAL — xoáy dần ra ngoài rồi lặp lại theo vòng đời
                    val life01 = (s.age / s.life).coerceIn(0f, 1f)
                    val ang = s.phase + t * s.speed * 1.1f + life01 * 4f + armPhase
                    val radius = minDim * 0.5f * life01
                    x = cos(ang) * radius
                    y = sin(ang) * radius
                    alpha = 1f - life01
                    size = s.baseSize * (0.6f + life01 * 0.9f)
                }
                2 -> { // BURST — từng đợt sóng nổ tỏa tâm
                    val ring = fmod(t * 0.5f + s.id * (1f / K_SLOTS), 1f)
                    val radius = ring * minDim * 0.58f
                    x = cos(s.phase) * radius
                    y = sin(s.phase) * radius
                    alpha = (1f - ring) * (1f - ring)
                    size = s.baseSize * (0.7f + ring * 0.8f)
                }
                3 -> { // BREATHE — phồng xẹp rất chậm, nhẹ nhàng
                    val breathe = 1f + 0.26f * sin(t * 0.55f + s.id * 0.8f)
                    val radius = minDim * (0.08f + (s.id % K_SLOTS) * 0.045f) * breathe
                    val ang = s.phase + t * 0.05f + armPhase
                    x = cos(ang) * radius
                    y = sin(ang) * radius
                    alpha = 0.5f + 0.5f * sin(t * 0.4f + s.seed)
                }
                else -> { // RAIN — rơi dọc, mượt và đối xứng gương
                    val span = minDim * 0.72f
                    y = fmod(t * (70f + s.speed * 90f) + s.seed * 400f, span * 1.3f) - span * 0.65f
                    x = (s.id - K_SLOTS / 2f) / K_SLOTS * minDim * 0.5f + sin(t * 0.3f + s.seed) * 10f
                    alpha = 1f - (abs(y) / (span * 0.65f)).coerceIn(0f, 1f)
                }
            }

            if (alpha <= 0.02f) return
            val hue = fmod(t * 22f + s.id * 33f + arm * 5f, 360f)
            hsv[0] = hue
            paint.color = Color.HSVToColor((alpha.coerceIn(0f, 1f) * 255).toInt(), hsv)
            paint.textSize = size
            val fm = paint.fontMetrics
            c.drawText(s.char.toString(), x, y - (fm.ascent + fm.descent) / 2f, paint)
        }
    }
}
