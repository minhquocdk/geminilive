package com.swarm.wallpaper

import android.content.Context
import android.graphics.Bitmap
import android.graphics.BitmapShader
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.LinearGradient
import android.graphics.Paint
import android.graphics.RadialGradient
import android.graphics.RectF
import android.graphics.Shader
import android.graphics.Typeface
import android.os.Handler
import android.os.Looper
import android.os.PowerManager
import android.os.SystemClock
import android.service.wallpaper.WallpaperService
import android.view.SurfaceHolder
import java.text.SimpleDateFormat
import java.util.Date
import java.util.Locale
import kotlin.math.PI
import kotlin.math.abs
import kotlin.math.exp
import kotlin.math.hypot
import kotlin.math.max
import kotlin.math.min
import kotlin.math.sin
import kotlin.random.Random

// ───────────────────────── CẤU HÌNH (chỉnh ở đây) ─────────────────────────
private const val FPS_NORMAL = 60        // fps bình thường
private const val FPS_SAVER = 12         // fps khi bật Tiết kiệm pin của máy
private const val TYPE_CPS = 48f         // tốc độ gõ chữ (ký tự/giây)

// ───────────────────────── MÀU ─────────────────────────
private object C {
    val BG = 0xFF080907.toInt()
    val PANEL = 0xFF0F100E.toInt()
    val PANEL_ACTIVE = 0xFF17130F.toInt()
    val LINE = 0xFF252720.toInt()
    val LINE_ACTIVE = 0xFF8D603B.toInt()
    val TEXT = 0xFFD8D8CF.toInt()
    val CMD = 0xFFCFCFC6.toInt()
    val MUTED = 0xFF7F8278.toInt()
    val DIM = 0xFF575A52.toInt()
    val TS = 0xFF4D5048.toInt()
    val ORANGE = 0xFFE99B52.toInt()
    val ORANGE_SOFT = 0xFFD8A06A.toInt()
    val GREEN = 0xFF58D68D.toInt()
    val BLUE = 0xFF6CA8FF.toInt()
    val RED = 0xFFFF6B6B.toInt()
    val YELLOW = 0xFFE5C76B.toInt()
    val BOX = 0xFF11120F.toInt()
    val BOX_LINE = 0xFF20221D.toInt()
    val LABEL = 0xFF686B63.toInt()
    val VALUE = 0xFFC9C9C0.toInt()
    val NAME = 0xFFC8C8BF.toInt()
    val BAR_BG = 0xFF262821.toInt()
    val DIFF_BG = 0xFF0E0F0C.toInt()
    val DIFF_BAR = 0xFF31342D.toInt()
    val TOAST = 0xFF131510.toInt()
    val TOAST_LINE = 0xFF2C3128.toInt()
}

// ───────────────────────── DỮ LIỆU ─────────────────────────
private class Seg(val text: String, val color: Int, val bold: Boolean = false)
private class Row(val segs: List<Seg>, val start: Int, val len: Int, val glow: Boolean, val bg: Boolean)
private class Line(val rows: List<Row>, val total: Int, var typed: Float, val typing: Boolean)
private class Agent(val name: String, val role: String, var state: String, var target: Int, var shown: Float)
private class Task(
    val agent: String,
    val title: String,
    val file: String,
    val cmd: String,
    val commit: String,
    val diff: List<String>,
    val result: String
)

private class Ev(val after: Long, val action: () -> Unit)

private val TASKS = listOf(
    Task(
        "ARCHITECT", "Eliminate race condition in distributed cache",
        "src/cache/lease-manager.ts", "pnpm test cache --runInBand",
        "fix(cache): make lease acquisition atomic",
        listOf(
            "- const lease = await store.get(key);",
            "+ const lease = await store.compareAndSwap(key, expected, next);",
            "+ if (!lease.acquired) return retryWithJitter(key);"
        ),
        "18 tests passed · race reproducer no longer triggers"
    ),
    Task(
        "SECURITY", "Harden session token validation path",
        "src/auth/session.ts", "pnpm security:verify",
        "security(auth): enforce issuer and audience checks",
        listOf(
            "- return jwt.decode(token);",
            "+ return jwt.verify(token, key, {",
            "+   algorithms: ['EdDSA'], issuer, audience });"
        ),
        "0 critical · 0 high · policy checks 42/42"
    ),
    Task(
        "CODER", "Reduce API p95 latency in profile aggregation",
        "src/services/profile.ts", "pnpm bench profile",
        "perf(profile): parallelize independent lookups",
        listOf(
            "- const account = await getAccount(id);",
            "- const flags = await getFlags(id);",
            "+ const [account, flags] = await Promise.all([",
            "+   getAccount(id), getFlags(id)]);"
        ),
        "p95 486ms → 173ms · throughput +38.4%"
    ),
    Task(
        "ORCHESTRATOR", "Recover failed migration without downtime",
        "db/migrations/2026_09_expand_events.sql", "pnpm migration:dry-run",
        "fix(db): make event migration resumable",
        listOf(
            "+ CREATE INDEX CONCURRENTLY IF NOT EXISTS",
            "+   idx_events_created_at ON events(created_at DESC);",
            "+ -- checkpoint: resumable phase 2"
        ),
        "dry run complete · lock time 11ms · rollback verified"
    ),
    Task(
        "CODER", "Remove WebSocket listener leak under reconnect storm",
        "src/realtime/socket-pool.ts", "pnpm test:realtime --stress",
        "fix(realtime): dispose listeners on close",
        listOf(
            "+ socket.once('close', () => {",
            "+   listeners.forEach(off => off());",
            "+   pool.delete(socket.id);",
            "+ });"
        ),
        "50k reconnect cycles · heap delta +0.6% · PASS"
    ),
    Task(
        "ARCHITECT", "Split monolith request pipeline into bounded stages",
        "src/http/pipeline.ts", "pnpm test pipeline",
        "refactor(http): isolate validation and execution stages",
        listOf(
            "+ const validated = await validationStage(input);",
            "+ const planned = await planningStage(validated);",
            "+ return executionStage(planned);"
        ),
        "74 tests passed · snapshots unchanged"
    )
)

// ───────────────────────── MÔ PHỎNG (logic thuần, không vẽ) ─────────────────────────
private class Sim {
    val lines = ArrayList<Line>()
    val agents = listOf(
        Agent("ORCHESTRATOR", "planning", "routing", 31, 31f),
        Agent("ARCHITECT", "reasoning", "indexing", 48, 48f),
        Agent("CODER", "execution", "patching", 76, 76f),
        Agent("SECURITY", "verification", "scanning", 59, 59f)
    )
    var active = "ORCHESTRATOR"
    var cols = 48
    var pendingRows = 0

    var tokens = 0L
    var cycle = 0
    var taskIdx = 0

    var mAgents = "4 active"
    var mTokens = "0"
    var mRate = "0 tok/s"
    var mCtx = "12%"
    var mCost = "\$0.000"
    var mCpu = "21%"
    var mRam = "1.8 GB"
    var mQueue = "6 jobs"
    var sessionText = "session 00:00:00 · clean"

    var flash = 0f
    var flashColor = C.GREEN
    var shake = 0f

    var toastTitle = ""
    var toastText = ""
    var toastStart = 0L
    var toastUntil = 0L

    private val queue = ArrayDeque<Ev>()
    private var nextAt = 0L
    private var nextMetric = 0L
    private var lastNow = 0L
    private val started = SystemClock.elapsedRealtime()
    private val fmt = SimpleDateFormat("HH:mm:ss", Locale.US)

    fun resync(now: Long) {
        nextAt = now + 250
        nextMetric = now
        lastNow = now
    }

    fun tick(now: Long) {
        lastNow = now
        var guard = 0
        while (now >= nextAt && guard++ < 12) {
            if (queue.isEmpty()) {
                enqueue(TASKS[taskIdx])
                taskIdx = (taskIdx + 1) % TASKS.size
            }
            val ev = queue.removeFirst()
            ev.action()
            nextAt = now + ev.after
        }
        if (now >= nextMetric) {
            nextMetric = now + 900
            updateMetrics()
        }
    }

    fun advance(dt: Float) {
        for (i in max(0, lines.size - 4) until lines.size) {
            val l = lines[i]
            if (l.typing && l.typed < l.total) l.typed = min(l.total.toFloat(), l.typed + TYPE_CPS * dt)
        }
        for (a in agents) a.shown += (a.target - a.shown) * min(1f, dt * 3f)
    }

    // ── helpers ──
    private fun r(a: Int, b: Int) = Random.nextInt(a, b + 1)
    private fun q(after: Long, action: () -> Unit) { queue.addLast(Ev(after, action)) }
    private fun ts() = Seg(fmt.format(Date()) + " ", C.TS)

    private fun bump(name: String, state: String) {
        for (a in agents) {
            a.target = (a.target + r(-9, 13)).coerceIn(18, 97)
            if (a.name == name) a.state = state
            else if (Random.nextFloat() < 0.25f) a.state = listOf("idle", "indexing", "watching", "reviewing").random()
        }
        active = name
    }

    private fun doFlash(color: Int, amount: Float) { flashColor = color; flash = amount }

    private fun toast(title: String, text: String) {
        toastTitle = title; toastText = text
        toastStart = lastNow; toastUntil = lastNow + 2400
    }

    private fun wrap(segs: List<Seg>): List<List<Seg>> {
        val rows = ArrayList<List<Seg>>()
        var cur = ArrayList<Seg>()
        var used = 0
        for (s in segs) {
            var t = s.text
            while (t.isNotEmpty()) {
                val room = cols - used
                if (room <= 0) {
                    rows.add(cur); cur = ArrayList(); used = 0
                    continue
                }
                val take = min(room, t.length)
                cur.add(Seg(t.substring(0, take), s.color, s.bold))
                used += take
                t = t.substring(take)
            }
        }
        if (cur.isNotEmpty() || rows.isEmpty()) rows.add(cur)
        return rows
    }

    private fun add(segs: List<Seg>, typing: Boolean = false, glow: Boolean = false, bg: Boolean = false) {
        for (i in max(0, lines.size - 4) until lines.size) lines[i].typed = lines[i].total.toFloat()
        val wrapped = wrap(segs)
        val rows = ArrayList<Row>()
        var start = 0
        for (w in wrapped) {
            val len = w.fold(0) { acc, s -> acc + s.text.length }
            rows.add(Row(w, start, len, glow, bg))
            start += len
        }
        lines.add(Line(rows, start, if (typing) 0f else start.toFloat(), typing))
        while (lines.size > 160) lines.removeAt(0)
        pendingRows += rows.size
    }

    private fun blank() = add(listOf(Seg("", C.TEXT)))

    private fun typeEv(text: String, color: Int) {
        q((text.length + 9) * 21L + 240L) {
            tokens += r(20, 60)
            add(listOf(ts(), Seg(text, color)), typing = true)
        }
    }

    private fun diffColor(d: String) = when {
        d.startsWith("+") -> C.GREEN
        d.startsWith("-") -> C.RED
        else -> C.TEXT
    }

    // ── kịch bản 1 task ──
    private fun enqueue(t: Task) {
        cycle++
        val recovery = cycle % 4 == 0

        q(220) {
            bump(t.agent, "executing")
            blank()
            add(listOf(ts(), Seg("[${t.agent}] ", C.ORANGE, true), Seg("❯ ${t.title}", C.TEXT, true)), glow = true)
        }
        typeEv("Analyzing dependency graph and recent repository changes...", C.MUTED)
        q(r(260, 520).toLong()) {
            add(listOf(ts(), Seg("◆ read ", C.BLUE), Seg(t.file, C.TEXT)))
        }
        q(r(200, 380).toLong()) {
            val conf = String.format(Locale.US, "%.3f", 0.91 + Random.nextDouble() * 0.08)
            add(listOf(ts(), Seg("↳ indexed ${r(14, 48)} symbols · ${r(3, 9)} callers · conf $conf", C.DIM)))
        }
        if (recovery) {
            typeEv("Detected invariant violation during patch simulation. Rolling back candidate hunk...", C.YELLOW)
            q(650) {
                add(listOf(ts(), Seg("✗ attempt 1 rejected ", C.RED), Seg("test invariant failed", C.DIM)))
                bump(t.agent, "recovering")
                shake = 1f
                doFlash(C.RED, 1f)
            }
            q(420) {
                add(listOf(ts(), Seg("↻ autonomous recovery ", C.GREEN), Seg("replanning with narrower mutation surface", C.DIM)))
            }
        }
        q(120) {
            bump(t.agent, "patching")
            add(listOf(ts(), Seg("◆ edit ", C.BLUE), Seg(t.file, C.TEXT)))
        }
        q(r(700, 1050).toLong()) {
            for (d in t.diff) add(listOf(Seg(d, diffColor(d))), bg = true)
            tokens += r(180, 420)
        }
        q(r(700, 1300).toLong()) {
            add(listOf(ts(), Seg("\$ ${t.cmd}", C.CMD)))
            bump(t.agent, "testing")
        }
        q(r(320, 600).toLong()) {
            add(listOf(ts(), Seg("✓ ${t.result}", C.GREEN)), glow = true)
            doFlash(C.GREEN, 0.55f)
            add(listOf(ts(), Seg("◆ git ", C.BLUE), Seg("commit --no-verify -m \"${t.commit}\"", C.TEXT)))
        }
        q(r(900, 1500).toLong()) {
            val hash = Random.nextInt(0x1000000, 0x10000000).toString(16)
            add(listOf(ts(), Seg("[feat/autonomous-runtime $hash] ${t.commit}", C.GREEN)))
            toast("DEPLOYMENT READY", "${t.agent} completed · queue advanced")
            bump("ORCHESTRATOR", "routing")
        }
    }

    private fun updateMetrics() {
        tokens += r(8, 29)
        mTokens = String.format(Locale.US, "%,d", tokens)
        mRate = "${r(118, 286)} tok/s"
        mCtx = "${min(89, 12 + (tokens / 1650).toInt())}%"
        mCost = "\$" + String.format(Locale.US, "%.3f", tokens / 1000.0 * 0.0128)
        mCpu = "${r(18, 64)}%"
        mRam = String.format(Locale.US, "%.1f GB", 1.6 + Random.nextDouble() * 1.5)
        mQueue = "${r(4, 9)} jobs"
        mAgents = "${r(3, 4)} active"
        val e = (SystemClock.elapsedRealtime() - started) / 1000
        sessionText = String.format(
            Locale.US, "session %02d:%02d:%02d · %s",
            e / 3600, e % 3600 / 60, e % 60, if (cycle % 4 == 0) "1 recovery" else "clean"
        )
    }
}

// ───────────────────────── WALLPAPER SERVICE ─────────────────────────
class SwarmWallpaperService : WallpaperService() {

    override fun onCreateEngine(): Engine = SwarmEngine()

    private inner class SwarmEngine : Engine() {
        private val handler = Handler(Looper.getMainLooper())
        private val sim = Sim()
        private val pm = getSystemService(Context.POWER_SERVICE) as PowerManager

        private var shown = false
        private var swCanvas = false
        private var startAt = 0L
        private var lastT = 0L
        private var scroll = 0f

        // kích thước / layout
        private var w = 0
        private var h = 0
        private var u = 1f
        private var ts = 30f
        private var charW = 18f
        private var lineH = 42f
        private var padX = 44f
        private var topY = 0f
        private var stripTop = 0f
        private var stripH = 0f
        private var termTop = 0f
        private var termBottom = 0f
        private var footerTop = 0f

        private val text = Paint(Paint.ANTI_ALIAS_FLAG).apply { typeface = Typeface.MONOSPACE }
        private val fill = Paint(Paint.ANTI_ALIAS_FLAG)
        private val stroke = Paint(Paint.ANTI_ALIAS_FLAG).apply { style = Paint.Style.STROKE }
        private val rect = RectF()
        private val scanPaint = Paint()
        private val vignettePaint = Paint()
        private val barPaint = Paint()

        private val labels = arrayOf("AGENTS", "TOKENS", "RATE", "CONTEXT", "COST", "CPU", "RAM", "QUEUE")

        private val loop = object : Runnable {
            override fun run() {
                val t0 = SystemClock.uptimeMillis()
                drawFrame(t0)
                if (shown) {
                    val fps = if (pm.isPowerSaveMode) FPS_SAVER else FPS_NORMAL
                    val interval = 1000L / fps
                    handler.postDelayed(this, max(1L, interval - (SystemClock.uptimeMillis() - t0)))
                }
            }
        }

        override fun onSurfaceChanged(holder: SurfaceHolder, format: Int, width: Int, height: Int) {
            super.onSurfaceChanged(holder, format, width, height)
            layout(width, height)
        }

        override fun onVisibilityChanged(visible: Boolean) {
            shown = visible
            handler.removeCallbacks(loop)
            if (visible) {
                val now = SystemClock.uptimeMillis()
                startAt = now
                lastT = now
                sim.resync(now)
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

        // ── layout ──
        private fun layout(width: Int, height: Int) {
            w = width
            h = height
            u = min(w, h) / 1080f
            ts = 30f * u
            text.textSize = ts
            charW = text.measureText("M")
            lineH = ts * 1.42f
            padX = 44f * u
            sim.cols = max(20, ((w - 2 * padX) / charW).toInt() - 1)

            topY = max(h * 0.045f, 60f * u)
            stripTop = topY + 72f * u
            stripH = 118f * u
            termTop = stripTop + stripH + 24f * u
            val footerH = 2 * 84f * u + 12f * u + 44f * u
            footerTop = h - max(h * 0.045f, 60f * u) - footerH
            termBottom = footerTop - 16f * u

            // scanlines: tile 1x4 px lặp lại, gần như 0 chi phí bộ nhớ
            val tile = Bitmap.createBitmap(1, 4, Bitmap.Config.ARGB_8888)
            tile.setPixel(0, 3, Color.argb(40, 0, 0, 0))
            scanPaint.shader = BitmapShader(tile, Shader.TileMode.REPEAT, Shader.TileMode.REPEAT)

            // vignette
            vignettePaint.shader = RadialGradient(
                w / 2f, h / 2f, hypot(w.toFloat(), h.toFloat()) * 0.55f,
                intArrayOf(Color.TRANSPARENT, Color.TRANSPARENT, Color.argb(190, 0, 0, 0)),
                floatArrayOf(0f, 0.5f, 1f), Shader.TileMode.CLAMP
            )

            // thanh quét sáng chạy dọc màn hình
            val bh = 200f * u
            barPaint.shader = LinearGradient(
                0f, 0f, 0f, bh,
                intArrayOf(Color.TRANSPARENT, Color.argb(16, 255, 255, 255), Color.TRANSPARENT),
                floatArrayOf(0f, 0.5f, 1f), Shader.TileMode.CLAMP
            )
        }

        // ── khung hình ──
        private fun drawFrame(now: Long) {
            if (w == 0) return
            val dt = ((now - lastT) / 1000f).coerceIn(0f, 0.1f)
            lastT = now

            sim.tick(now)
            sim.advance(dt)

            scroll += sim.pendingRows * lineH
            sim.pendingRows = 0
            scroll = min(scroll, lineH * 8f)
            scroll -= scroll * (1f - exp(-dt * 11f))
            if (scroll < 0.5f) scroll = 0f

            val holder = surfaceHolder
            var c: Canvas? = null
            try {
                c = if (!swCanvas) {
                    try {
                        holder.lockHardwareCanvas()
                    } catch (e: Exception) {
                        swCanvas = true
                        holder.lockCanvas()
                    }
                } else holder.lockCanvas()
                if (c != null) render(c, now, dt)
            } catch (e: Exception) {
                // bỏ qua khung lỗi
            } finally {
                if (c != null) {
                    try { holder.unlockCanvasAndPost(c) } catch (e: Exception) { }
                }
            }
        }

        private fun render(c: Canvas, now: Long, dt: Float) {
            c.drawColor(C.BG)

            c.save()
            val sh = sim.shake
            if (sh > 0.01f) {
                c.translate(
                    (Random.nextFloat() - 0.5f) * 2f * sh * 7f * u,
                    (Random.nextFloat() - 0.5f) * 2f * sh * 5f * u
                )
            }
            drawHeader(c, now)
            drawAgents(c)
            drawTerminal(c, now)
            drawFooter(c)
            c.restore()

            val wf = w.toFloat()
            val hf = h.toFloat()

            // scanlines
            c.drawRect(0f, 0f, wf, hf, scanPaint)

            // thanh quét sáng
            val bh = 200f * u
            val y = ((now % 7000L) / 7000f) * (hf + bh) - bh
            c.save()
            c.translate(0f, y)
            c.drawRect(0f, 0f, wf, bh, barPaint)
            c.restore()

            // vignette
            c.drawRect(0f, 0f, wf, hf, vignettePaint)

            // nhấp nháy CRT rất nhẹ
            val fl = (abs(sin((now % 100000L) * 0.011f)) * 6f).toInt()
            if (fl > 0) c.drawColor(Color.argb(fl, 0, 0, 0))

            // flash màu khi thành công / lỗi
            if (sim.flash > 0.01f) {
                val fc = sim.flashColor
                val a = (sim.flash * 34f).toInt().coerceIn(0, 255)
                c.drawColor(Color.argb(a, Color.red(fc), Color.green(fc), Color.blue(fc)))
            }
            sim.flash = max(0f, sim.flash - dt * 2.2f)
            sim.shake = max(0f, sim.shake - dt * 4.5f)

            // fade-in mỗi lần mở màn hình
            val fi = ((now - startAt) / 900f).coerceIn(0f, 1f)
            if (fi < 1f) c.drawColor(Color.argb(((1f - fi) * 255f).toInt(), 0, 0, 0))
        }

        // ── helpers vẽ chữ ──
        private fun drawT(
            c: Canvas, s: String, x: Float, y: Float, size: Float, color: Int,
            bold: Boolean = false, alpha: Int = 255
        ) {
            text.textSize = size
            text.isFakeBoldText = bold
            text.clearShadowLayer()
            text.color = color
            text.alpha = alpha
            c.drawText(s, x, y, text)
        }

        private fun tw(s: String, size: Float): Float {
            text.textSize = size
            text.isFakeBoldText = false
            return text.measureText(s)
        }

        // ── header ──
        private fun drawHeader(c: Canvas, now: Long) {
            val base = topY + 36f * u
            drawT(c, "✦", padX, base, ts * 0.95f, C.ORANGE)
            drawT(c, "claude-code / swarm", padX + 34f * u, base, ts * 0.85f, C.TEXT, bold = true)
            drawT(c, "autonomous engineering session", padX + 34f * u, base + 26f * u, ts * 0.5f, C.MUTED)

            val liveW = tw("LIVE", ts * 0.6f)
            val right = w - padX
            val pulse = 0.55f + 0.45f * sin(((now % 1300L) / 1300f) * 2f * PI.toFloat())
            drawT(c, "LIVE", right - liveW, base - 4f * u, ts * 0.6f, C.GREEN, bold = true)
            val cx = right - liveW - 18f * u
            val cy = base - 13f * u
            fill.color = C.GREEN
            fill.alpha = (70 * pulse).toInt()
            c.drawCircle(cx, cy, 11f * u, fill)
            fill.color = C.GREEN
            fill.alpha = (255 * pulse).toInt()
            c.drawCircle(cx, cy, 6f * u, fill)
        }

        // ── thẻ agent ──
        private fun drawAgents(c: Canvas) {
            val gap = 12f * u
            val cw = (w - 2 * padX - 3 * gap) / 4f
            sim.agents.forEachIndexed { i, a ->
                val x = padX + i * (cw + gap)
                val act = a.name == sim.active
                rect.set(x, stripTop, x + cw, stripTop + stripH)
                fill.color = if (act) C.PANEL_ACTIVE else C.PANEL
                c.drawRoundRect(rect, 14f * u, 14f * u, fill)
                stroke.color = if (act) C.LINE_ACTIVE else C.LINE
                stroke.strokeWidth = 2f * u
                c.drawRoundRect(rect, 14f * u, 14f * u, stroke)

                drawT(c, a.name, x + 14f * u, stripTop + 34f * u, ts * 0.6f, if (act) C.ORANGE else C.NAME, bold = true)
                drawT(c, a.state, x + 14f * u, stripTop + 68f * u, ts * 0.5f, if (act) C.ORANGE_SOFT else C.MUTED)
                val pct = "${a.shown.toInt()}%"
                drawT(c, pct, x + cw - 14f * u - tw(pct, ts * 0.5f), stripTop + 68f * u, ts * 0.5f, if (act) C.ORANGE_SOFT else C.MUTED)

                val bx = x + 14f * u
                val bw = cw - 28f * u
                val by = stripTop + stripH - 26f * u
                rect.set(bx, by, bx + bw, by + 5f * u)
                fill.color = C.BAR_BG
                c.drawRoundRect(rect, 3f * u, 3f * u, fill)
                rect.set(bx, by, bx + bw * (a.shown / 100f), by + 5f * u)
                fill.color = C.ORANGE
                fill.alpha = if (act) 255 else 140
                c.drawRoundRect(rect, 3f * u, 3f * u, fill)
            }
        }

        // ── terminal ──
        private fun drawTerminal(c: Canvas, now: Long) {
            c.save()
            c.clipRect(0f, termTop, w.toFloat(), termBottom)
            text.textSize = ts

            val base = termBottom - lineH * 0.28f + scroll
            val lines = sim.lines
            var k = 0
            val blinkOn = (now / 450L) % 2L == 0L

            outer@ for (li in lines.indices.reversed()) {
                val ln = lines[li]
                val typingNow = ln.typed < ln.total
                val limit = if (typingNow) ln.typed.toInt() else Int.MAX_VALUE
                for (ri in ln.rows.indices.reversed()) {
                    val row = ln.rows[ri]
                    val y = base - k * lineH
                    if (y < termTop) break@outer
                    k++
                    if (y - lineH > termBottom + scroll) continue

                    val fade = ((y - termTop) / (lineH * 7f)).coerceIn(0f, 1f)
                    val alpha = (255f * (0.12f + 0.88f * fade)).toInt()

                    if (row.bg) {
                        rect.set(padX - 12f * u, y - lineH * 0.78f, w - padX + 12f * u, y + lineH * 0.24f)
                        fill.color = C.DIFF_BG
                        c.drawRect(rect, fill)
                        fill.color = C.DIFF_BAR
                        c.drawRect(padX - 12f * u, rect.top, padX - 8f * u, rect.bottom, fill)
                    }

                    var x = padX
                    var idx = row.start
                    for (s in row.segs) {
                        val avail = limit - idx
                        if (avail <= 0) break
                        val t = if (avail >= s.text.length) s.text else s.text.substring(0, avail)
                        text.isFakeBoldText = s.bold
                        text.color = s.color
                        text.alpha = alpha
                        if (row.glow) {
                            text.setShadowLayer(10f * u, 0f, 0f, (s.color and 0x00FFFFFF) or (0x99 shl 24))
                        } else {
                            text.clearShadowLayer()
                        }
                        c.drawText(t, x, y, text)
                        x += s.text.length * charW
                        idx += s.text.length
                    }

                    // con trỏ đang gõ
                    if (typingNow && blinkOn && limit >= row.start && limit < row.start + row.len) {
                        val cx = padX + (limit - row.start) * charW
                        fill.color = C.ORANGE
                        fill.alpha = alpha
                        c.drawRect(cx, y - lineH * 0.7f, cx + charW * 0.85f, y + lineH * 0.08f, fill)
                    }
                }
            }
            text.clearShadowLayer()
            text.isFakeBoldText = false

            // toast
            if (now < sim.toastUntil) {
                val a = min((now - sim.toastStart) / 220f, (sim.toastUntil - now) / 300f).coerceIn(0f, 1f)
                val toastW = 470f * u
                val th = 92f * u
                rect.set(w - padX - toastW, termBottom - th - 14f * u, w - padX, termBottom - 14f * u)
                fill.color = C.TOAST
                fill.alpha = (235 * a).toInt()
                c.drawRoundRect(rect, 16f * u, 16f * u, fill)
                stroke.color = C.TOAST_LINE
                stroke.alpha = (255 * a).toInt()
                stroke.strokeWidth = 2f * u
                c.drawRoundRect(rect, 16f * u, 16f * u, stroke)
                drawT(c, sim.toastTitle, rect.left + 18f * u, rect.top + 36f * u, ts * 0.6f, C.GREEN, true, (255 * a).toInt())
                drawT(c, sim.toastText, rect.left + 18f * u, rect.top + 68f * u, ts * 0.52f, C.MUTED, false, (255 * a).toInt())
            }
            c.restore()
        }

        // ── footer metrics ──
        private fun metric(i: Int): String = when (i) {
            0 -> sim.mAgents
            1 -> sim.mTokens
            2 -> sim.mRate
            3 -> sim.mCtx
            4 -> sim.mCost
            5 -> sim.mCpu
            6 -> sim.mRam
            else -> sim.mQueue
        }

        private fun drawFooter(c: Canvas) {
            val gap = 12f * u
            val bw = (w - 2 * padX - 3 * gap) / 4f
            val bh = 84f * u
            for (i in 0 until 8) {
                val x = padX + (i % 4) * (bw + gap)
                val y = footerTop + (i / 4) * (bh + gap)
                rect.set(x, y, x + bw, y + bh)
                fill.color = C.BOX
                c.drawRoundRect(rect, 12f * u, 12f * u, fill)
                stroke.color = C.BOX_LINE
                stroke.strokeWidth = 2f * u
                c.drawRoundRect(rect, 12f * u, 12f * u, stroke)
                drawT(c, labels[i], x + 14f * u, y + 30f * u, ts * 0.48f, C.LABEL)
                drawT(c, metric(i), x + 14f * u, y + 65f * u, ts * 0.76f, if (i == 0) C.ORANGE else C.VALUE)
            }
            val by = footerTop + 2 * bh + gap + 34f * u
            drawT(c, "git: feat/autonomous-runtime", padX, by, ts * 0.46f, C.LABEL)
            val st = sim.sessionText
            drawT(c, st, w - padX - tw(st, ts * 0.46f), by, ts * 0.46f, C.LABEL)
        }
    }
}
