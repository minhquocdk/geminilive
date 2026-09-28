plugins {
    id("com.android.application")
    id("org.jetbrains.kotlin.android")
}

android {
    namespace = "com.swarm.wallpaper"
    compileSdk = 34

    defaultConfig {
        applicationId = "com.swarm.wallpaper"
        minSdk = 26
        targetSdk = 34
        // ⚠️ Lưu ý: Nhớ tăng số versionCode này lên (ví dụ: 2, 3...) mỗi khi bạn cập nhật app để máy người dùng chịu cài đè nhé!
        versionCode = 1 
        versionName = "1.0"
    }

    // ---- KHU VỰC THÊM MỚI: Cấu hình đọc Key từ GitHub Actions ----
    signingConfigs {
        create("release") {
            storeFile = file("release.jks")
            storePassword = System.getenv("SIGNING_STORE_PASSWORD")
            keyAlias = System.getenv("SIGNING_KEY_ALIAS")
            keyPassword = System.getenv("SIGNING_KEY_PASSWORD")
        }
    }

    buildTypes {
        release { 
            isMinifyEnabled = false 
            // ---- KHU VỰC THÊM MỚI: Ép bản Release phải dùng Key vừa cấu hình ở trên ----
            signingConfig = signingConfigs.getByName("release")
        }
    }
    compileOptions {
        sourceCompatibility = JavaVersion.VERSION_17
        targetCompatibility = JavaVersion.VERSION_17
    }
    kotlinOptions { jvmTarget = "17" }
}
