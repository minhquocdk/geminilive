package com.swarm.wallpaper

import android.app.Activity
import android.app.WallpaperManager
import android.content.ComponentName
import android.content.Intent
import android.graphics.Color
import android.os.Bundle
import android.view.Gravity
import android.widget.Button
import android.widget.LinearLayout
import android.widget.TextView

class MainActivity : Activity() {
    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)

        val root = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            gravity = Gravity.CENTER
            setBackgroundColor(Color.parseColor("#080907"))
            setPadding(64, 64, 64, 64)
        }
        val title = TextView(this).apply {
            text = "Live wallpapers"
            setTextColor(Color.parseColor("#E99B52"))
            textSize = 20f
            gravity = Gravity.CENTER
            setPadding(0, 0, 0, 48)
        }
        val b1 = Button(this).apply { text = "Claude Swarm (terminal)" }
        val b2 = Button(this).apply { text = "Gemini Particles (3D)" }
        b1.setOnClickListener { pick(SwarmWallpaperService::class.java) }
        b2.setOnClickListener { pick(GeminiWallpaperService::class.java) }

        root.addView(title)
        root.addView(b1)
        root.addView(b2)
        setContentView(root)
    }

    private fun pick(service: Class<*>) {
        try {
            val i = Intent(WallpaperManager.ACTION_CHANGE_LIVE_WALLPAPER)
            i.putExtra(
                WallpaperManager.EXTRA_LIVE_WALLPAPER_COMPONENT,
                ComponentName(this, service)
            )
            startActivity(i)
        } catch (e: Exception) {
            startActivity(Intent(WallpaperManager.ACTION_LIVE_WALLPAPER_CHOOSER))
        }
    }
}
