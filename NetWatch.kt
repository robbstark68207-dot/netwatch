@file:OptIn(ExperimentalMaterial3Api::class)

package com.netwatch.app

import android.app.AppOpsManager
import android.app.usage.NetworkStats
import android.app.usage.NetworkStatsManager
import android.content.Context
import android.content.Intent
import android.content.SharedPreferences
import android.content.pm.ApplicationInfo
import android.content.pm.PackageManager
import android.net.ConnectivityManager
import android.net.NetworkCapabilities
import android.net.Uri
import android.net.VpnService
import android.os.Bundle
import android.os.ParcelFileDescriptor
import android.os.Process
import android.provider.Settings
import android.system.OsConstants
import android.widget.Toast
import androidx.activity.ComponentActivity
import androidx.activity.compose.setContent
import androidx.activity.result.contract.ActivityResultContracts
import androidx.compose.animation.animateContentSize
import androidx.compose.foundation.Image
import androidx.compose.foundation.background
import androidx.compose.foundation.border
import androidx.compose.foundation.clickable
import androidx.compose.foundation.horizontalScroll
import androidx.compose.foundation.isSystemInDarkTheme
import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.PaddingValues
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.height
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.layout.size
import androidx.compose.foundation.layout.width
import androidx.compose.foundation.lazy.LazyColumn
import androidx.compose.foundation.lazy.items
import androidx.compose.foundation.rememberScrollState
import androidx.compose.foundation.shape.CircleShape
import androidx.compose.material3.AlertDialog
import androidx.compose.material3.Button
import androidx.compose.material3.Card
import androidx.compose.material3.ExperimentalMaterial3Api
import androidx.compose.material3.FilterChip
import androidx.compose.material3.HorizontalDivider
import androidx.compose.material3.LinearProgressIndicator
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.NavigationBar
import androidx.compose.material3.NavigationBarItem
import androidx.compose.material3.OutlinedButton
import androidx.compose.material3.OutlinedTextField
import androidx.compose.material3.Scaffold
import androidx.compose.material3.Surface
import androidx.compose.material3.Switch
import androidx.compose.material3.Text
import androidx.compose.material3.TextButton
import androidx.compose.material3.TopAppBar
import androidx.compose.material3.darkColorScheme
import androidx.compose.material3.lightColorScheme
import androidx.compose.runtime.Composable
import androidx.compose.runtime.CompositionLocalProvider
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.collectAsState
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableIntStateOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.draw.clip
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.ImageBitmap
import androidx.compose.ui.graphics.asImageBitmap
import androidx.compose.ui.platform.LocalClipboardManager
import androidx.compose.ui.platform.LocalContext
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.text.AnnotatedString
import androidx.compose.ui.text.font.FontWeight
import androidx.compose.ui.text.style.TextOverflow
import androidx.compose.ui.unit.Density
import androidx.compose.ui.unit.dp
import androidx.core.graphics.drawable.toBitmap
import java.io.File
import java.io.FileInputStream
import java.io.FileOutputStream
import java.net.DatagramPacket
import java.net.DatagramSocket
import java.net.InetAddress
import java.net.InetSocketAddress
import java.text.SimpleDateFormat
import java.util.Arrays
import java.util.Calendar
import java.util.Date
import java.util.Locale
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.ExecutorService
import java.util.concurrent.Executors
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.flow.MutableStateFlow
import kotlinx.coroutines.flow.StateFlow
import kotlinx.coroutines.withContext

/** Minimal IPv4 / IPv6 / UDP / DNS helpers. Only what the VPN needs. */
object PacketUtils {

    class DnsPacket(
        val src: ByteArray,   // sender (the phone's VPN address)
        val dst: ByteArray,   // the fake DNS server address
        val srcPort: Int,
        val dstPort: Int,
        val payload: ByteArray
    )

    /** Basic facts about any IP packet: protocol, who to who, which ports. */
    class PktInfo(
        val proto: Int,
        val src: ByteArray,
        val dst: ByteArray,
        val srcPort: Int,
        val dstPort: Int
    )

    fun protoName(p: Int): String = when (p) {
        6 -> "TCP"
        17 -> "UDP"
        1 -> "ICMP"
        58 -> "ICMPv6"
        else -> "IP $p"
    }

    /** Header facts of an IPv4 or IPv6 packet, or null if it is not one. */
    fun summarize(buf: ByteArray, len: Int): PktInfo? {
        if (len < 20) return null
        val version = (buf[0].toInt() and 0xF0) shr 4
        if (version == 4) {
            val ihl = (buf[0].toInt() and 0x0F) * 4
            if (ihl < 20 || len < ihl) return null
            val proto = buf[9].toInt() and 0xFF
            var sp = 0
            var dp = 0
            if ((proto == 6 || proto == 17) && len >= ihl + 4) {
                sp = u16(buf, ihl)
                dp = u16(buf, ihl + 2)
            }
            return PktInfo(proto, buf.copyOfRange(12, 16), buf.copyOfRange(16, 20), sp, dp)
        }
        if (version == 6) {
            if (len < 40) return null
            val proto = buf[6].toInt() and 0xFF
            var sp = 0
            var dp = 0
            if ((proto == 6 || proto == 17) && len >= 44) {
                sp = u16(buf, 40)
                dp = u16(buf, 42)
            }
            return PktInfo(proto, buf.copyOfRange(8, 24), buf.copyOfRange(24, 40), sp, dp)
        }
        return null
    }

    /** Returns the DNS query inside an IPv4/UDP packet to port 53, or null for anything else. */
    fun parseUdpDns(buf: ByteArray, len: Int): DnsPacket? {
        if (len < 28) return null
        val version = (buf[0].toInt() and 0xF0) shr 4
        if (version != 4) return null
        val ihl = (buf[0].toInt() and 0x0F) * 4
        if (ihl < 20 || len < ihl + 8) return null
        val proto = buf[9].toInt() and 0xFF
        if (proto != 17) return null
        val dstPort = u16(buf, ihl + 2)
        if (dstPort != 53) return null
        val udpLen = u16(buf, ihl + 4)
        val payloadLen = minOf(udpLen - 8, len - ihl - 8)
        if (payloadLen <= 0) return null
        return DnsPacket(
            buf.copyOfRange(12, 16),
            buf.copyOfRange(16, 20),
            u16(buf, ihl),
            dstPort,
            buf.copyOfRange(ihl + 8, ihl + 8 + payloadLen)
        )
    }

    /** Server name asked for in the first question of a DNS message. */
    fun queryName(p: ByteArray): String? {
        if (p.size < 13) return null
        if (u16(p, 4) < 1) return null
        var i = 12
        val sb = StringBuilder()
        while (i < p.size) {
            val l = p[i].toInt() and 0xFF
            if (l == 0) break
            if ((l and 0xC0) != 0) return null
            if (i + 1 + l > p.size) return null
            if (sb.isNotEmpty()) sb.append('.')
            sb.append(String(p, i + 1, l, Charsets.ISO_8859_1))
            i += 1 + l
        }
        val name = sb.toString().lowercase()
        return if (name.isEmpty()) null else name
    }

    /** Wraps a DNS answer into an IPv4/UDP packet addressed back to whoever asked. */
    fun buildUdpReply(req: DnsPacket, data: ByteArray): ByteArray {
        val dataLen = data.size
        val total = 20 + 8 + dataLen
        val out = ByteArray(total)
        out[0] = 0x45.toByte()
        putU16(out, 2, total)
        putU16(out, 6, 0x4000)
        out[8] = 64
        out[9] = 17
        System.arraycopy(req.dst, 0, out, 12, 4)
        System.arraycopy(req.src, 0, out, 16, 4)
        putU16(out, 10, checksum(out, 0, 20))
        putU16(out, 20, req.dstPort)
        putU16(out, 22, req.srcPort)
        putU16(out, 24, 8 + dataLen)
        // UDP checksum 0 = "not used", which is allowed over IPv4
        System.arraycopy(data, 0, out, 28, dataLen)
        return out
    }

    private fun u16(b: ByteArray, off: Int): Int =
        ((b[off].toInt() and 0xFF) shl 8) or (b[off + 1].toInt() and 0xFF)

    private fun putU16(b: ByteArray, off: Int, v: Int) {
        b[off] = ((v shr 8) and 0xFF).toByte()
        b[off + 1] = (v and 0xFF).toByte()
    }

    private fun checksum(b: ByteArray, off: Int, len: Int): Int {
        var sum = 0L
        var i = off
        while (i < off + len - 1) {
            sum += ((b[i].toInt() and 0xFF) shl 8) or (b[i + 1].toInt() and 0xFF)
            i += 2
        }
        if (len % 2 == 1) sum += (b[off + len - 1].toInt() and 0xFF) shl 8
        while ((sum shr 16) != 0L) {
            sum = (sum and 0xFFFFL) + (sum shr 16)
        }
        return (sum.inv() and 0xFFFFL).toInt()
    }
}

/**
 * Very simple keyword check on server names. It is a hint, not proof:
 * a flagged name is not always bad, and an unflagged name is not always harmless.
 */
object Domains {
    private val trackerWords = listOf(
        "analytics", "telemetry", "crashlytics", "crash-report", "metrics",
        "tracking", "tracker", "beacon", "sentry", "doubleclick",
        "googleadservices", "adservice", "appsflyer", "adjust.com", "mixpanel",
        "amplitude", "app-measurement", "firebaselogging", "umeng", "bugly",
        "applovin", "vungle", "inmobi", "unityads"
    )

    private val oemWords = listOf(
        "heytapmobi", "heytap", "oppomobile", "coloros", "realme.com", "realmemobile"
    )

    fun flag(domain: String): String? {
        val d = domain.lowercase()
        if (Prefs.customFlagList().any { d.contains(it) }) return "Matches your keyword"
        if (trackerWords.any { d.contains(it) }) return "Analytics / tracking"
        if (oemWords.any { d.contains(it) }) return "realme / OPPO service"
        return null
    }
}

/** All user settings plus the list of blocked apps. Saved on the phone. */
object Prefs {
    private var sp: SharedPreferences? = null

    /** 0 = follow phone, 1 = light, 2 = dark */
    var theme by mutableIntStateOf(0)
        private set

    var accent by mutableIntStateOf(0)
        private set

    /** 0 small, 1 normal, 2 large, 3 extra large */
    var textSize by mutableIntStateOf(1)
        private set

    var compact by mutableStateOf(false)
        private set

    var showSystem by mutableStateOf(false)
        private set

    var uploadAlertMb by mutableIntStateOf(5)
        private set

    var customFlags by mutableStateOf("")
        private set

    var blocked by mutableStateOf<Set<String>>(emptySet())
        private set

    /** "monitor" or "firewall": what the VPN does when it is switched on */
    var mode by mutableStateOf("monitor")
        private set

    @Synchronized
    fun init(context: Context) {
        if (sp != null) return
        val p = context.applicationContext.getSharedPreferences("netwatch", Context.MODE_PRIVATE)
        sp = p
        theme = p.getInt("theme", 0)
        accent = p.getInt("accent", 0)
        textSize = p.getInt("textSize", 1)
        compact = p.getBoolean("compact", false)
        showSystem = p.getBoolean("showSystem", false)
        uploadAlertMb = p.getInt("uploadAlertMb", 5)
        customFlags = p.getString("customFlags", "") ?: ""
        blocked = p.getStringSet("blocked", emptySet())?.toSet() ?: emptySet()
        mode = p.getString("mode", "monitor") ?: "monitor"
    }

    fun setTheme(v: Int) {
        theme = v
        sp?.edit()?.putInt("theme", v)?.apply()
    }

    fun setAccent(v: Int) {
        accent = v
        sp?.edit()?.putInt("accent", v)?.apply()
    }

    fun setTextSize(v: Int) {
        textSize = v
        sp?.edit()?.putInt("textSize", v)?.apply()
    }

    fun setCompact(v: Boolean) {
        compact = v
        sp?.edit()?.putBoolean("compact", v)?.apply()
    }

    fun setShowSystem(v: Boolean) {
        showSystem = v
        sp?.edit()?.putBoolean("showSystem", v)?.apply()
    }

    fun setUploadAlertMb(v: Int) {
        uploadAlertMb = v
        sp?.edit()?.putInt("uploadAlertMb", v)?.apply()
    }

    fun setCustomFlags(v: String) {
        customFlags = v
        sp?.edit()?.putString("customFlags", v)?.apply()
    }

    fun addCustomFlag(word: String) {
        val w = word.trim().lowercase()
        if (w.isEmpty() || customFlagList().contains(w)) return
        setCustomFlags(if (customFlags.isBlank()) w else "$customFlags, $w")
    }

    fun customFlagList(): List<String> =
        customFlags.split(',').map { it.trim().lowercase() }.filter { it.isNotEmpty() }

    fun setMode(v: String) {
        mode = v
        sp?.edit()?.putString("mode", v)?.apply()
    }

    fun toggleBlocked(pkg: String) {
        blocked = if (blocked.contains(pkg)) blocked - pkg else blocked + pkg
        sp?.edit()?.putStringSet("blocked", HashSet(blocked))?.apply()
    }
}

/** One place a blocked app tried to reach, merged over repeats. */
data class BlockEntry(
    val pkg: String,
    val app: String,
    val dest: String,
    val port: Int,
    val proto: String,
    val tries: Int,
    val bytes: Long,
    val last: Long
)

/** What blocked apps tried to contact while the firewall was on (kept in memory). */
object BlockStore {
    private val map = LinkedHashMap<String, BlockEntry>()
    private val state = MutableStateFlow<List<BlockEntry>>(emptyList())
    val entries: StateFlow<List<BlockEntry>> = state

    @Synchronized
    fun add(pkg: String, app: String, dest: String, port: Int, proto: String, bytes: Int) {
        val key = "$pkg|$dest|$port|$proto"
        val now = System.currentTimeMillis()
        val old = map[key]
        map[key] = if (old == null) {
            BlockEntry(pkg, app, dest, port, proto, 1, bytes.toLong(), now)
        } else {
            old.copy(tries = old.tries + 1, bytes = old.bytes + bytes, last = now)
        }
        if (map.size > 1500) {
            val oldest = map.entries.minByOrNull { it.value.last }?.key
            if (oldest != null) map.remove(oldest)
        }
        state.value = map.values.sortedByDescending { it.last }
    }

    @Synchronized
    fun clear() {
        map.clear()
        state.value = emptyList()
    }
}

data class LogEntry(
    val time: Long,
    val uid: Int,
    val app: String,
    val pkg: String,
    val domain: String,
    val flag: String?,
    val blocked: Boolean = false
)

/** Keeps the latest server lookups in memory (newest first) and in a small file. */
object LogStore {
    private const val MAX = 3000

    private val state = MutableStateFlow<List<LogEntry>>(emptyList())
    val entries: StateFlow<List<LogEntry>> = state

    private var file: File? = null

    @Synchronized
    fun init(context: Context) {
        if (file != null) return
        val f = File(context.applicationContext.filesDir, "server_log.tsv")
        file = f
        if (!f.exists()) return
        try {
            val loaded = ArrayList<LogEntry>()
            for (line in f.readLines().takeLast(MAX)) {
                val p = line.split('\t')
                if (p.size < 6) continue
                loaded.add(
                    LogEntry(
                        p[0].toLong(), p[1].toInt(), p[2], p[3], p[4],
                        if (p[5].isEmpty()) null else p[5],
                        p.getOrNull(6) == "1"
                    )
                )
            }
            if (loaded.isNotEmpty()) {
                // file is oldest-first, the list is newest-first
                loaded.reverse()
                state.value = loaded
                f.writeText(loaded.asReversed().joinToString("\n") { toLine(it) } + "\n")
            }
        } catch (e: Exception) {
            // a damaged log file is not worth crashing for
        }
    }

    @Synchronized
    fun add(e: LogEntry) {
        state.value = (listOf(e) + state.value).take(MAX)
        try {
            file?.appendText(toLine(e) + "\n")
        } catch (ex: Exception) {
        }
    }

    @Synchronized
    fun clear() {
        state.value = emptyList()
        try {
            file?.writeText("")
        } catch (ex: Exception) {
        }
    }

    private fun toLine(e: LogEntry): String =
        listOf(
            e.time, e.uid, clean(e.app), clean(e.pkg), clean(e.domain),
            e.flag ?: "", if (e.blocked) "1" else "0"
        ).joinToString("\t")

    private fun clean(s: String): String = s.replace('\t', ' ').replace('\n', ' ')
}

data class AppUsage(
    val uid: Int,
    val label: String,
    val packageName: String,
    val bgRx: Long,
    val bgTx: Long,
    val fgRx: Long,
    val fgTx: Long,
    val system: Boolean
) {
    val bgTotal: Long get() = bgRx + bgTx
    val total: Long get() = bgRx + bgTx + fgRx + fgTx
}

/** An installed app that is allowed to use the internet (so it can be blocked). */
data class InstalledApp(
    val label: String,
    val pkg: String,
    val uid: Int,
    val system: Boolean
)

object UsageRepository {

    /** All apps on the phone that have the internet permission, except NetWatch itself. */
    fun installedApps(context: Context): List<InstalledApp> {
        val pm = context.packageManager
        val apps = try {
            pm.getInstalledApplications(0)
        } catch (e: Exception) {
            emptyList<ApplicationInfo>()
        }
        val out = ArrayList<InstalledApp>()
        for (ai in apps) {
            if (ai.packageName == context.packageName) continue
            val granted = pm.checkPermission(
                android.Manifest.permission.INTERNET, ai.packageName
            ) == PackageManager.PERMISSION_GRANTED
            if (!granted) continue
            val label = try {
                pm.getApplicationLabel(ai).toString()
            } catch (e: Exception) {
                ai.packageName
            }
            val system = (ai.flags and ApplicationInfo.FLAG_SYSTEM) != 0
            out.add(InstalledApp(label, ai.packageName, ai.uid, system))
        }
        return out
    }

    fun hasPermission(context: Context): Boolean {
        val appOps = context.getSystemService(Context.APP_OPS_SERVICE) as AppOpsManager
        val mode = appOps.unsafeCheckOpNoThrow(
            AppOpsManager.OPSTR_GET_USAGE_STATS,
            Process.myUid(),
            context.packageName
        )
        return mode == AppOpsManager.MODE_ALLOWED
    }

    /** 0 = since midnight, 1 = last 24 hours, 2 = last 7 days */
    fun sinceMillis(range: Int): Long {
        val now = System.currentTimeMillis()
        return when (range) {
            0 -> Calendar.getInstance().apply {
                set(Calendar.HOUR_OF_DAY, 0)
                set(Calendar.MINUTE, 0)
                set(Calendar.SECOND, 0)
                set(Calendar.MILLISECOND, 0)
            }.timeInMillis
            1 -> now - 24L * 3600_000L
            else -> now - 7L * 24L * 3600_000L
        }
    }

    /**
     * Per-app traffic since [since], split into background and foreground.
     * Wi-Fi and mobile data are added together.
     */
    fun load(context: Context, since: Long): List<AppUsage> {
        val nsm = context.getSystemService(Context.NETWORK_STATS_SERVICE) as NetworkStatsManager
        val pm = context.packageManager
        val end = System.currentTimeMillis()

        // uid -> [bgRx, bgTx, fgRx, fgTx]
        val totals = HashMap<Int, LongArray>()

        for (type in intArrayOf(ConnectivityManager.TYPE_WIFI, ConnectivityManager.TYPE_MOBILE)) {
            val stats = try {
                nsm.querySummary(type, null, since, end)
            } catch (e: Exception) {
                null
            }
            if (stats == null) continue
            try {
                val bucket = NetworkStats.Bucket()
                while (stats.hasNextBucket()) {
                    stats.getNextBucket(bucket)
                    val arr = totals.getOrPut(bucket.uid) { LongArray(4) }
                    if (bucket.state == NetworkStats.Bucket.STATE_FOREGROUND) {
                        arr[2] += bucket.rxBytes
                        arr[3] += bucket.txBytes
                    } else {
                        arr[0] += bucket.rxBytes
                        arr[1] += bucket.txBytes
                    }
                }
            } finally {
                stats.close()
            }
        }

        val result = ArrayList<AppUsage>()
        for ((uid, a) in totals) {
            if (a[0] + a[1] + a[2] + a[3] == 0L) continue
            val pkg = try {
                pm.getPackagesForUid(uid)?.firstOrNull()
            } catch (e: Exception) {
                null
            }
            var label: String = ""
            var system = true
            if (pkg != null) {
                label = pkg
                try {
                    val ai = pm.getApplicationInfo(pkg, 0)
                    label = pm.getApplicationLabel(ai).toString()
                    system = (ai.flags and ApplicationInfo.FLAG_SYSTEM) != 0 &&
                        (ai.flags and ApplicationInfo.FLAG_UPDATED_SYSTEM_APP) == 0
                } catch (e: Exception) {
                }
            } else {
                label = when (uid) {
                    0 -> "Root / kernel"
                    1000 -> "Android system"
                    -4 -> "Removed apps"
                    -5 -> "Hotspot / tethering"
                    else -> "uid $uid"
                }
            }
            result.add(AppUsage(uid, label, pkg ?: "", a[0], a[1], a[2], a[3], system))
        }
        return result
    }
}

fun fmt(bytes: Long): String {
    if (bytes < 1024) return "$bytes B"
    val kb = bytes / 1024.0
    if (kb < 1024) return String.format(Locale.US, "%.1f KB", kb)
    val mb = kb / 1024.0
    if (mb < 1024) return String.format(Locale.US, "%.1f MB", mb)
    return String.format(Locale.US, "%.2f GB", mb / 1024.0)
}

/**
 * One local VPN with two jobs (Android allows only one VPN at a time):
 *
 * MONITOR: only DNS lookups are routed into this app. Each lookup is written to the log
 * and passed on to the phone's normal DNS server, so everything keeps working.
 *
 * FIREWALL: only the apps you chose to block are routed into this app, and every packet
 * they send is dropped. Those apps cannot reach the internet. Other apps are untouched.
 * Blocked attempts are recorded so you can see what the app tried to contact.
 *
 * Nothing is ever sent to any NetWatch server.
 */
class DnsVpnService : VpnService() {

    companion object {
        const val ACTION_START = "com.netwatch.app.START"
        const val ACTION_STOP = "com.netwatch.app.STOP"
        private const val DNS_ADDR = "10.111.222.1"
        private const val LOCAL_ADDR = "10.111.222.2"
        private const val LOCAL_ADDR6 = "fd00:111:222::2"

        /** "off", "monitor" or "firewall" */
        val state = MutableStateFlow("off")
    }

    private var tun: ParcelFileDescriptor? = null
    private var reader: Thread? = null
    private var pool: ExecutorService? = null

    @Volatile
    private var active = false

    @Volatile
    private var session = 0

    private val appCache = ConcurrentHashMap<Int, Pair<String, String>>()
    private val lastSeen = ConcurrentHashMap<String, Long>()
    private val blockSeen = ConcurrentHashMap<String, Long>()

    @Volatile
    private var upstreamCache: List<InetAddress> = emptyList()

    @Volatile
    private var upstreamAt = 0L

    override fun onStartCommand(intent: Intent?, flags: Int, startId: Int): Int {
        if (intent?.action == ACTION_STOP) {
            stopVpn()
            stopSelf()
            return START_NOT_STICKY
        }
        // a start request always rebuilds the VPN, so a changed mode or block list takes effect
        stopVpn()
        startVpn()
        return START_STICKY
    }

    override fun onRevoke() {
        stopVpn()
        stopSelf()
        super.onRevoke()
    }

    override fun onDestroy() {
        stopVpn()
        super.onDestroy()
    }

    private fun startVpn() {
        if (active) return
        Prefs.init(applicationContext)
        LogStore.init(applicationContext)
        val firewall = Prefs.mode == "firewall"

        val builder = Builder()
            .addAddress(LOCAL_ADDR, 32)
            .addDnsServer(DNS_ADDR)
            .setMtu(1500)
            .setBlocking(true)

        if (firewall) {
            builder.setSession("NetWatch firewall")
            try {
                builder.addAddress(LOCAL_ADDR6, 128)
            } catch (e: Exception) {
            }
            builder.addRoute("0.0.0.0", 0)
            try {
                builder.addRoute("::", 0)
            } catch (e: Exception) {
            }
            var added = 0
            for (pkg in Prefs.blocked) {
                try {
                    builder.addAllowedApplication(pkg)
                    added++
                } catch (e: Exception) {
                    // app no longer installed
                }
            }
            if (added == 0) {
                stopSelf()
                return
            }
        } else {
            builder.setSession("NetWatch")
            builder.addRoute(DNS_ADDR, 32)
            try {
                builder.addDisallowedApplication(packageName)
            } catch (e: Exception) {
            }
        }

        val pfd = try {
            builder.establish()
        } catch (e: Exception) {
            null
        }
        if (pfd == null) {
            stopSelf()
            return
        }

        tun = pfd
        active = true
        val id = ++session
        state.value = if (firewall) "firewall" else "monitor"
        if (!firewall) pool = Executors.newFixedThreadPool(6)
        reader = Thread(
            { if (firewall) firewallLoop(pfd, id) else readLoop(pfd, id) },
            "netwatch-reader"
        ).also { it.start() }
    }

    private fun stopVpn() {
        session++
        active = false
        state.value = "off"
        try {
            tun?.close()
        } catch (e: Exception) {
        }
        tun = null
        reader?.interrupt()
        reader = null
        pool?.shutdownNow()
        pool = null
    }

    // ------------------------------------------------------------------ monitor mode

    private fun readLoop(pfd: ParcelFileDescriptor, id: Int) {
        val input = FileInputStream(pfd.fileDescriptor)
        val output = FileOutputStream(pfd.fileDescriptor)
        val buf = ByteArray(32767)
        try {
            while (active && id == session) {
                val n = input.read(buf)
                if (n < 0) break
                if (n == 0) continue
                val pkt = PacketUtils.parseUdpDns(buf, n) ?: continue
                try {
                    pool?.execute { handleQuery(pkt, output) }
                } catch (e: Exception) {
                    break
                }
            }
        } catch (e: Exception) {
            // tunnel closed
        } finally {
            if (active && id == session) {
                // ended without anyone asking for it
                stopVpn()
                stopSelf()
            }
        }
    }

    private fun handleQuery(p: PacketUtils.DnsPacket, output: FileOutputStream) {
        try {
            val name = PacketUtils.queryName(p.payload)
            if (name != null) logQuery(p, name)
            val answer = forward(p.payload) ?: return
            val reply = PacketUtils.buildUdpReply(p, answer)
            synchronized(output) { output.write(reply) }
        } catch (e: Exception) {
            // one failed lookup must not stop the rest
        }
    }

    private fun logQuery(p: PacketUtils.DnsPacket, domain: String) {
        val uid = ownerUid(OsConstants.IPPROTO_UDP, p.src, p.srcPort, p.dst, p.dstPort)
        val key = "$uid|$domain"
        val now = System.currentTimeMillis()
        val prev = lastSeen[key]
        if (prev != null && now - prev < 3000) return // phones ask A and AAAA back to back
        lastSeen[key] = now
        if (lastSeen.size > 5000) lastSeen.clear()
        val (label, pkg) = appInfo(uid)
        LogStore.add(LogEntry(now, uid, label, pkg, domain, Domains.flag(domain)))
    }

    // ------------------------------------------------------------------ firewall mode

    private fun firewallLoop(pfd: ParcelFileDescriptor, id: Int) {
        val input = FileInputStream(pfd.fileDescriptor)
        val buf = ByteArray(32767)
        try {
            while (active && id == session) {
                val n = input.read(buf)
                if (n < 0) break
                if (n == 0) continue
                try {
                    recordBlocked(buf, n)
                } catch (e: Exception) {
                }
                // nothing is written back: the packet is dropped, the app gets no connection
            }
        } catch (e: Exception) {
            // tunnel closed
        } finally {
            if (active && id == session) {
                stopVpn()
                stopSelf()
            }
        }
    }

    private fun recordBlocked(buf: ByteArray, n: Int) {
        val info = PacketUtils.summarize(buf, n) ?: return
        val key = "${info.proto}|${info.srcPort}|${info.dstPort}|${Arrays.hashCode(info.dst)}"
        val now = System.currentTimeMillis()
        val prev = blockSeen[key]
        if (prev != null && now - prev < 2000) return // retries come in bursts
        blockSeen[key] = now
        if (blockSeen.size > 5000) blockSeen.clear()

        val uid = if (info.proto == 6 || info.proto == 17) {
            ownerUid(info.proto, info.src, info.srcPort, info.dst, info.dstPort)
        } else {
            -1
        }
        val (label, pkg) = blockedOwner(uid)

        val dns = PacketUtils.parseUdpDns(buf, n)
        val name = if (dns != null) PacketUtils.queryName(dns.payload) else null
        if (name != null) {
            BlockStore.add(pkg, label, name, 53, "DNS lookup", n)
        } else {
            BlockStore.add(pkg, label, ipString(info.dst), info.dstPort, PacketUtils.protoName(info.proto), n)
        }
    }

    private fun blockedOwner(uid: Int): Pair<String, String> {
        if (uid >= 10000) return appInfo(uid)
        val blocked = Prefs.blocked
        if (blocked.size == 1) {
            val pkg = blocked.first()
            return Pair(labelFor(pkg), pkg)
        }
        return Pair("Blocked app (unknown which)", "")
    }

    private fun ipString(b: ByteArray): String {
        return try {
            InetAddress.getByAddress(b).hostAddress ?: "?"
        } catch (e: Exception) {
            "?"
        }
    }

    // ------------------------------------------------------------------ shared helpers

    /**
     * Which app owns this connection? Android often does DNS through a system service,
     * so in monitor mode this can come back as "Android system" for a real app's lookup.
     */
    private fun ownerUid(proto: Int, src: ByteArray, srcPort: Int, dst: ByteArray, dstPort: Int): Int {
        return try {
            val cm = getSystemService(ConnectivityManager::class.java)
            cm.getConnectionOwnerUid(
                proto,
                InetSocketAddress(InetAddress.getByAddress(src), srcPort),
                InetSocketAddress(InetAddress.getByAddress(dst), dstPort)
            )
        } catch (e: Exception) {
            -1
        }
    }

    private fun labelFor(pkg: String): String {
        return try {
            packageManager.getApplicationLabel(packageManager.getApplicationInfo(pkg, 0)).toString()
        } catch (e: Exception) {
            pkg
        }
    }

    private fun appInfo(uid: Int): Pair<String, String> {
        return appCache.getOrPut(uid) {
            when {
                uid < 0 -> Pair("Unknown app", "")
                uid < 10000 -> Pair("Android system / resolver", "")
                else -> {
                    val pkg = try {
                        packageManager.getPackagesForUid(uid)?.firstOrNull()
                    } catch (e: Exception) {
                        null
                    }
                    if (pkg == null) Pair("uid $uid", "") else Pair(labelFor(pkg), pkg)
                }
            }
        }
    }

    /** DNS servers of the real (non-VPN) network, Wi-Fi first. */
    private fun upstreamServers(): List<InetAddress> {
        val now = System.currentTimeMillis()
        if (now - upstreamAt < 10_000 && upstreamCache.isNotEmpty()) return upstreamCache

        val found = ArrayList<InetAddress>()
        try {
            val cm = getSystemService(ConnectivityManager::class.java)
            val nets = cm.allNetworks.filter { n ->
                val caps = cm.getNetworkCapabilities(n)
                caps != null &&
                    !caps.hasTransport(NetworkCapabilities.TRANSPORT_VPN) &&
                    caps.hasCapability(NetworkCapabilities.NET_CAPABILITY_INTERNET)
            }.sortedBy { n ->
                val wifi = cm.getNetworkCapabilities(n)
                    ?.hasTransport(NetworkCapabilities.TRANSPORT_WIFI) == true
                if (wifi) 0 else 1
            }
            for (n in nets) {
                val lp = cm.getLinkProperties(n) ?: continue
                for (a in lp.dnsServers) {
                    if (!found.contains(a)) found.add(a)
                }
            }
        } catch (e: Exception) {
        }

        if (found.isEmpty()) {
            try {
                found.add(InetAddress.getByName("1.1.1.1"))
                found.add(InetAddress.getByName("8.8.8.8"))
            } catch (e: Exception) {
            }
        }
        upstreamCache = found
        upstreamAt = now
        return found
    }

    private fun forward(query: ByteArray): ByteArray? {
        for (server in upstreamServers().take(3)) {
            var sock: DatagramSocket? = null
            try {
                sock = DatagramSocket()
                protect(sock)
                sock.soTimeout = 3000
                sock.send(DatagramPacket(query, query.size, InetSocketAddress(server, 53)))
                val buf = ByteArray(4096)
                val resp = DatagramPacket(buf, buf.size)
                sock.receive(resp)
                return buf.copyOf(resp.length)
            } catch (e: Exception) {
                // try the next server
            } finally {
                sock?.close()
            }
        }
        return null
    }
}

data class Accent(val name: String, val light: Color, val dark: Color)

val ACCENTS = listOf(
    Accent("Teal", Color(0xFF00796B), Color(0xFF4DB6AC)),
    Accent("Blue", Color(0xFF1565C0), Color(0xFF90CAF9)),
    Accent("Purple", Color(0xFF6A1B9A), Color(0xFFCE93D8)),
    Accent("Orange", Color(0xFFE65100), Color(0xFFFFB74D)),
    Accent("Pink", Color(0xFFC2185B), Color(0xFFF48FB1))
)

class MainActivity : ComponentActivity() {

    private var resumeTick by mutableIntStateOf(0)

    private val vpnPermission =
        registerForActivityResult(ActivityResultContracts.StartActivityForResult()) { result ->
            if (result.resultCode == RESULT_OK) startVpnService()
        }

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        Prefs.init(this)
        LogStore.init(this)
        setContent {
            val systemDark = isSystemInDarkTheme()
            val dark = when (Prefs.theme) {
                1 -> false
                2 -> true
                else -> systemDark
            }
            val accent = ACCENTS[Prefs.accent.coerceIn(0, ACCENTS.size - 1)]
            val primary = if (dark) accent.dark else accent.light
            val scheme = if (dark) {
                darkColorScheme(
                    primary = primary,
                    onPrimary = Color(0xFF101010),
                    secondaryContainer = primary.copy(alpha = 0.28f)
                )
            } else {
                lightColorScheme(
                    primary = primary,
                    onPrimary = Color.White,
                    secondaryContainer = primary.copy(alpha = 0.18f)
                )
            }
            val scales = floatArrayOf(0.88f, 1f, 1.15f, 1.3f)
            val scale = scales[Prefs.textSize.coerceIn(0, scales.size - 1)]
            val base = LocalDensity.current
            CompositionLocalProvider(
                LocalDensity provides Density(base.density, base.fontScale * scale)
            ) {
                MaterialTheme(colorScheme = scheme) {
                    Surface(modifier = Modifier.fillMaxSize()) {
                        NetWatchApp(
                            resumeTick = resumeTick,
                            onMonitor = { on -> setMonitor(on) },
                            onFirewall = { on -> setFirewall(on) },
                            onToggleBlock = { pkg -> toggleBlock(pkg) },
                            onOpenUsageAccess = { openUsageAccess() }
                        )
                    }
                }
            }
        }
    }

    override fun onResume() {
        super.onResume()
        resumeTick++
    }

    private fun setMonitor(on: Boolean) {
        if (on) beginVpn("monitor") else stopVpnService()
    }

    private fun setFirewall(on: Boolean) {
        if (on) {
            if (Prefs.blocked.isEmpty()) {
                Toast.makeText(
                    this,
                    "Switch on Block for at least one app first",
                    Toast.LENGTH_LONG
                ).show()
                return
            }
            beginVpn("firewall")
        } else {
            stopVpnService()
        }
    }

    private fun toggleBlock(pkg: String) {
        Prefs.toggleBlocked(pkg)
        // if the firewall is running, rebuild it so the new list applies at once
        if (DnsVpnService.state.value == "firewall") startVpnService()
    }

    private fun beginVpn(mode: String) {
        Prefs.setMode(mode)
        val intent = VpnService.prepare(this)
        if (intent != null) vpnPermission.launch(intent) else startVpnService()
    }

    private fun startVpnService() {
        startService(
            Intent(this, DnsVpnService::class.java).setAction(DnsVpnService.ACTION_START)
        )
    }

    private fun stopVpnService() {
        startService(
            Intent(this, DnsVpnService::class.java).setAction(DnsVpnService.ACTION_STOP)
        )
    }

    private fun openUsageAccess() {
        try {
            startActivity(
                Intent(Settings.ACTION_USAGE_ACCESS_SETTINGS, Uri.parse("package:$packageName"))
            )
        } catch (e: Exception) {
            startActivity(Intent(Settings.ACTION_USAGE_ACCESS_SETTINGS))
        }
    }
}

// ------------------------------------------------------------------ shell

@Composable
fun NetWatchApp(
    resumeTick: Int,
    onMonitor: (Boolean) -> Unit,
    onFirewall: (Boolean) -> Unit,
    onToggleBlock: (String) -> Unit,
    onOpenUsageAccess: () -> Unit
) {
    var tab by remember { mutableIntStateOf(0) }
    val titles = listOf("Apps", "Servers", "Blocked", "Settings")
    val icons = listOf("📱", "🌐", "🚫", "⚙️")
    Scaffold(
        topBar = { TopAppBar(title = { Text("NetWatch") }) },
        bottomBar = {
            NavigationBar {
                titles.forEachIndexed { i, t ->
                    NavigationBarItem(
                        selected = tab == i,
                        onClick = { tab = i },
                        icon = { Text(icons[i]) },
                        label = { Text(t) }
                    )
                }
            }
        }
    ) { padding ->
        Box(Modifier.padding(padding).fillMaxSize()) {
            when (tab) {
                0 -> AppsScreen(resumeTick, onOpenUsageAccess, onToggleBlock, onFirewall)
                1 -> ServersScreen(onMonitor, onToggleBlock)
                2 -> BlockedScreen()
                else -> SettingsScreen()
            }
        }
    }
}

fun cardPad() = if (Prefs.compact) 6.dp else 12.dp

// ------------------------------------------------------------------ Apps tab

@Composable
fun AppsScreen(
    resumeTick: Int,
    onOpenUsageAccess: () -> Unit,
    onToggleBlock: (String) -> Unit,
    onFirewall: (Boolean) -> Unit
) {
    val ctx = LocalContext.current
    var granted by remember { mutableStateOf(UsageRepository.hasPermission(ctx)) }
    var range by remember { mutableIntStateOf(1) }
    var sort by remember { mutableIntStateOf(0) }
    var query by remember { mutableStateOf("") }
    var onlyBlocked by remember { mutableStateOf(false) }
    var installed by remember { mutableStateOf<List<InstalledApp>>(emptyList()) }
    var usage by remember { mutableStateOf<Map<Int, AppUsage>>(emptyMap()) }
    var loading by remember { mutableStateOf(false) }
    var refresh by remember { mutableIntStateOf(0) }
    var expanded by remember { mutableStateOf<String?>(null) }
    var confirm by remember { mutableStateOf<InstalledApp?>(null) }

    LaunchedEffect(resumeTick) {
        granted = UsageRepository.hasPermission(ctx)
    }
    LaunchedEffect(granted, range, resumeTick, refresh) {
        loading = true
        val result = withContext(Dispatchers.IO) {
            val apps = UsageRepository.installedApps(ctx)
            val u = if (granted) {
                UsageRepository.load(ctx, UsageRepository.sinceMillis(range)).associateBy { it.uid }
            } else {
                emptyMap<Int, AppUsage>()
            }
            Pair(apps, u)
        }
        installed = result.first
        usage = result.second
        loading = false
    }

    val blocked = Prefs.blocked
    val showSystem = Prefs.showSystem
    val rows = remember(installed, usage, sort, query, onlyBlocked, blocked, showSystem) {
        installed.filter { a ->
            (showSystem || !a.system || blocked.contains(a.pkg)) &&
                (!onlyBlocked || blocked.contains(a.pkg)) &&
                (query.isBlank() ||
                    a.label.contains(query, ignoreCase = true) ||
                    a.pkg.contains(query, ignoreCase = true))
        }.sortedWith(
            when (sort) {
                0 -> compareByDescending<InstalledApp> { usage[it.uid]?.bgTotal ?: 0L }
                1 -> compareByDescending<InstalledApp> { usage[it.uid]?.total ?: 0L }
                else -> compareBy<InstalledApp> { it.label.lowercase() }
            }
        )
    }
    val maxBg = (rows.maxOfOrNull { usage[it.uid]?.bgTotal ?: 0L } ?: 1L).coerceAtLeast(1L)
    val pad = cardPad()

    confirm?.let { a ->
        AlertDialog(
            onDismissRequest = { confirm = null },
            title = { Text("Block a system app?") },
            text = {
                Text(
                    "${a.label} is part of your phone's software. Blocking it can break " +
                        "features such as messages, updates or the Play Store. " +
                        "You can undo this at any time."
                )
            },
            confirmButton = {
                TextButton(onClick = {
                    onToggleBlock(a.pkg)
                    confirm = null
                }) { Text("Block it") }
            },
            dismissButton = { TextButton(onClick = { confirm = null }) { Text("Cancel") } }
        )
    }

    LazyColumn(
        Modifier.fillMaxSize(),
        contentPadding = PaddingValues(pad),
        verticalArrangement = Arrangement.spacedBy(pad / 2 + 2.dp)
    ) {
        item { FirewallCard(onFirewall) }

        if (!granted) {
            item {
                Card(Modifier.fillMaxWidth()) {
                    Column(Modifier.padding(pad), verticalArrangement = Arrangement.spacedBy(6.dp)) {
                        Text("Data amounts are hidden", fontWeight = FontWeight.SemiBold)
                        Text(
                            "Allow \"Usage access\" for NetWatch to see how much each app " +
                                "uploads and downloads. Blocking works without it.",
                            style = MaterialTheme.typography.bodySmall
                        )
                        Button(onClick = onOpenUsageAccess) { Text("Open settings") }
                    }
                }
            }
        }

        item {
            OutlinedTextField(
                value = query,
                onValueChange = { query = it },
                label = { Text("Search apps") },
                singleLine = true,
                modifier = Modifier.fillMaxWidth()
            )
        }
        item {
            Row(
                Modifier.horizontalScroll(rememberScrollState()),
                horizontalArrangement = Arrangement.spacedBy(8.dp),
                verticalAlignment = Alignment.CenterVertically
            ) {
                listOf("Today", "24 hours", "7 days").forEachIndexed { i, n ->
                    FilterChip(selected = range == i, onClick = { range = i }, label = { Text(n) })
                }
                TextButton(onClick = { refresh++ }) { Text("Refresh") }
            }
        }
        item {
            Row(
                Modifier.horizontalScroll(rememberScrollState()),
                horizontalArrangement = Arrangement.spacedBy(8.dp),
                verticalAlignment = Alignment.CenterVertically
            ) {
                listOf("Most background", "Most total", "A–Z").forEachIndexed { i, n ->
                    FilterChip(selected = sort == i, onClick = { sort = i }, label = { Text(n) })
                }
                FilterChip(
                    selected = onlyBlocked,
                    onClick = { onlyBlocked = !onlyBlocked },
                    label = { Text("Blocked only") }
                )
            }
        }
        if (loading && installed.isEmpty()) {
            item { LinearProgressIndicator(Modifier.fillMaxWidth()) }
        }
        if (!loading && rows.isEmpty()) {
            item { Text("No apps match.") }
        }
        items(rows, key = { it.pkg }) { a ->
            AppCard(
                app = a,
                usage = usage[a.uid],
                maxBg = maxBg,
                blocked = blocked.contains(a.pkg),
                expanded = expanded == a.pkg,
                onClick = { expanded = if (expanded == a.pkg) null else a.pkg },
                onToggle = {
                    if (a.system && !blocked.contains(a.pkg)) confirm = a else onToggleBlock(a.pkg)
                }
            )
        }
        item {
            Text(
                "Background = traffic while the app was not on screen (screen off included). " +
                    "↓ download, ↑ upload. Wi-Fi and mobile data added together. " +
                    "Tap an app for details.",
                style = MaterialTheme.typography.bodySmall
            )
        }
    }
}

@Composable
fun FirewallCard(onFirewall: (Boolean) -> Unit) {
    val st by DnsVpnService.state.collectAsState()
    val on = st == "firewall"
    val pad = cardPad()
    Card(Modifier.fillMaxWidth()) {
        Column(Modifier.padding(pad), verticalArrangement = Arrangement.spacedBy(4.dp)) {
            Row(verticalAlignment = Alignment.CenterVertically) {
                Column(Modifier.weight(1f)) {
                    Text(
                        if (on) "Firewall is ON" else "Firewall is OFF",
                        style = MaterialTheme.typography.titleMedium
                    )
                    Text(
                        "${Prefs.blocked.size} app(s) set to Block",
                        style = MaterialTheme.typography.bodySmall
                    )
                }
                Switch(checked = on, onCheckedChange = { onFirewall(it) })
            }
            if (on) {
                Text(
                    "Blocked apps cannot reach any server. Other apps are not affected.",
                    style = MaterialTheme.typography.bodySmall
                )
            } else if (Prefs.blocked.isEmpty()) {
                Text(
                    "Step 1: switch on Block for the apps you want to freeze. " +
                        "Step 2: turn the firewall on.",
                    style = MaterialTheme.typography.bodySmall
                )
            }
            if (st == "monitor") {
                Text(
                    "Turning the firewall on pauses server monitoring " +
                        "(Android allows one VPN at a time).",
                    style = MaterialTheme.typography.bodySmall
                )
            }
        }
    }
}

private val iconCache = HashMap<String, ImageBitmap>()

@Composable
fun AppIcon(pkg: String) {
    val ctx = LocalContext.current
    val bmp = remember(pkg) {
        val cached = iconCache[pkg]
        if (cached != null) {
            cached
        } else {
            val made = try {
                ctx.packageManager.getApplicationIcon(pkg).toBitmap(96, 96).asImageBitmap()
            } catch (e: Exception) {
                null
            }
            if (made != null) iconCache[pkg] = made
            made
        }
    }
    if (bmp != null) {
        Image(bitmap = bmp, contentDescription = null, modifier = Modifier.size(40.dp))
    } else {
        Box(Modifier.size(40.dp))
    }
}

@Composable
fun AppCard(
    app: InstalledApp,
    usage: AppUsage?,
    maxBg: Long,
    blocked: Boolean,
    expanded: Boolean,
    onClick: () -> Unit,
    onToggle: () -> Unit
) {
    val pad = cardPad()
    Card(Modifier.fillMaxWidth().animateContentSize()) {
        Column(Modifier.clickable(onClick = onClick).padding(pad)) {
            Row(verticalAlignment = Alignment.CenterVertically) {
                AppIcon(app.pkg)
                Spacer(Modifier.width(10.dp))
                Column(Modifier.weight(1f)) {
                    Text(
                        app.label,
                        fontWeight = FontWeight.SemiBold,
                        maxLines = 1,
                        overflow = TextOverflow.Ellipsis
                    )
                    if (usage != null) {
                        Text(
                            "Background  ↓ ${fmt(usage.bgRx)}   ↑ ${fmt(usage.bgTx)}",
                            style = MaterialTheme.typography.bodySmall,
                            color = MaterialTheme.colorScheme.primary
                        )
                    } else {
                        Text("No data in this period", style = MaterialTheme.typography.bodySmall)
                    }
                }
                Column(horizontalAlignment = Alignment.CenterHorizontally) {
                    Switch(checked = blocked, onCheckedChange = { onToggle() })
                    Text(
                        if (blocked) "Blocked" else "Allowed",
                        style = MaterialTheme.typography.labelSmall
                    )
                }
            }
            if (usage != null) {
                LinearProgressIndicator(
                    progress = { (usage.bgTotal.toFloat() / maxBg.toFloat()).coerceIn(0f, 1f) },
                    modifier = Modifier.fillMaxWidth().padding(top = 6.dp)
                )
                if (usage.bgTx > Prefs.uploadAlertMb * 1024L * 1024L) {
                    Text(
                        "⚠ Background upload is above your ${Prefs.uploadAlertMb} MB limit",
                        color = MaterialTheme.colorScheme.error,
                        style = MaterialTheme.typography.bodySmall,
                        modifier = Modifier.padding(top = 4.dp)
                    )
                }
            }
            if (expanded) AppDetails(app, usage)
        }
    }
}

@Composable
fun AppDetails(app: InstalledApp, usage: AppUsage?) {
    val servers by LogStore.entries.collectAsState()
    val attempts by BlockStore.entries.collectAsState()
    val mine = remember(servers, app.pkg) {
        servers.filter { it.pkg == app.pkg }
            .groupingBy { it.domain }.eachCount()
            .entries.sortedByDescending { it.value }.take(8)
    }
    val tried = remember(attempts, app.pkg) { attempts.filter { it.pkg == app.pkg }.take(8) }

    Column(Modifier.padding(top = 8.dp), verticalArrangement = Arrangement.spacedBy(4.dp)) {
        HorizontalDivider()
        Text(app.pkg, style = MaterialTheme.typography.bodySmall)
        if (app.system) Text("System app", style = MaterialTheme.typography.bodySmall)
        if (usage != null) {
            Text("On screen  ↓ ${fmt(usage.fgRx)}   ↑ ${fmt(usage.fgTx)}")
            Text("Total  ${fmt(usage.total)}", fontWeight = FontWeight.Medium)
        }
        Text("Servers this app looked up", style = MaterialTheme.typography.titleSmall)
        if (mine.isEmpty()) {
            Text(
                "None recorded under this app. Turn on monitoring in the Servers tab. " +
                    "Android often logs lookups as \"Android system\" instead.",
                style = MaterialTheme.typography.bodySmall
            )
        } else {
            mine.forEach { Text("• ${it.key}   ×${it.value}") }
        }
        if (tried.isNotEmpty()) {
            Text("Tried to reach while blocked", style = MaterialTheme.typography.titleSmall)
            tried.forEach {
                Text("• ${it.dest}  (${it.proto} ${it.port})   ×${it.tries}")
            }
        }
    }
}

// ------------------------------------------------------------------ Servers tab

@Composable
fun ServersScreen(onMonitor: (Boolean) -> Unit, onToggleBlock: (String) -> Unit) {
    val st by DnsVpnService.state.collectAsState()
    val entries by LogStore.entries.collectAsState()
    val clip = LocalClipboardManager.current
    var onlyFlagged by remember { mutableStateOf(false) }
    var grouped by remember { mutableStateOf(false) }
    var query by remember { mutableStateOf("") }
    var open by remember { mutableStateOf<String?>(null) }
    val keywords = Prefs.customFlags
    val blocked = Prefs.blocked
    val pad = cardPad()
    val timeFormat = remember { SimpleDateFormat("dd MMM  HH:mm:ss", Locale.getDefault()) }

    val rows = remember(entries, onlyFlagged, grouped, query, keywords) {
        val f = entries.filter { e ->
            (!onlyFlagged || Domains.flag(e.domain) != null) &&
                (query.isBlank() ||
                    e.domain.contains(query, ignoreCase = true) ||
                    e.app.contains(query, ignoreCase = true))
        }
        if (grouped) {
            f.groupBy { it.domain }
                .map { entry -> Pair(entry.value.first(), entry.value.size) }
                .sortedByDescending { it.second }
        } else {
            f.map { Pair(it, 1) }
        }
    }

    LazyColumn(
        Modifier.fillMaxSize(),
        contentPadding = PaddingValues(pad),
        verticalArrangement = Arrangement.spacedBy(4.dp)
    ) {
        item {
            Column(verticalArrangement = Arrangement.spacedBy(8.dp)) {
                Text(
                    when (st) {
                        "monitor" -> "Monitoring is ON"
                        "firewall" -> "Firewall is running (monitoring paused)"
                        else -> "Monitoring is OFF"
                    },
                    style = MaterialTheme.typography.titleMedium
                )
                Text(
                    "Lists every server name your phone looks up, in the background too. " +
                        "A lookup means a connection is about to happen. Tap a row for actions.",
                    style = MaterialTheme.typography.bodySmall
                )
                Row(
                    horizontalArrangement = Arrangement.spacedBy(8.dp),
                    verticalAlignment = Alignment.CenterVertically
                ) {
                    Button(onClick = { onMonitor(st != "monitor") }) {
                        Text(if (st == "monitor") "Stop" else "Start monitoring")
                    }
                    OutlinedButton(onClick = { LogStore.clear() }) { Text("Clear log") }
                }
                OutlinedTextField(
                    value = query,
                    onValueChange = { query = it },
                    label = { Text("Search servers or apps") },
                    singleLine = true,
                    modifier = Modifier.fillMaxWidth()
                )
                Row(
                    Modifier.horizontalScroll(rememberScrollState()),
                    horizontalArrangement = Arrangement.spacedBy(8.dp)
                ) {
                    FilterChip(
                        selected = grouped,
                        onClick = { grouped = !grouped },
                        label = { Text("Group by server") }
                    )
                    FilterChip(
                        selected = onlyFlagged,
                        onClick = { onlyFlagged = !onlyFlagged },
                        label = { Text("Flagged only") }
                    )
                }
                HorizontalDivider()
            }
        }
        if (rows.isEmpty()) {
            item {
                Text(
                    if (st == "monitor") "Waiting for lookups…"
                    else "Nothing to show. Tap Start monitoring."
                )
            }
        }
        items(rows) { row ->
            val e = row.first
            val count = row.second
            val k = "${e.time}|${e.uid}|${e.domain}"
            val flag = Domains.flag(e.domain)
            Column(Modifier.fillMaxWidth()) {
            Column(
                Modifier.fillMaxWidth()
                    .clickable { open = if (open == k) null else k }
                    .padding(vertical = 4.dp)
            ) {
                Row(verticalAlignment = Alignment.CenterVertically) {
                    Column(Modifier.weight(1f)) {
                        Text(e.domain, fontWeight = FontWeight.Medium)
                        Text(
                            "${timeFormat.format(Date(e.time))}  ·  ${e.app}",
                            style = MaterialTheme.typography.bodySmall
                        )
                    }
                    if (count > 1) Text("×$count", fontWeight = FontWeight.SemiBold)
                }
                if (flag != null) {
                    Text(
                        flag,
                        color = MaterialTheme.colorScheme.tertiary,
                        style = MaterialTheme.typography.bodySmall
                    )
                }
                if (open == k) {
                    Row(
                        Modifier.horizontalScroll(rememberScrollState()),
                        horizontalArrangement = Arrangement.spacedBy(4.dp)
                    ) {
                        TextButton(onClick = { clip.setText(AnnotatedString(e.domain)) }) {
                            Text("Copy")
                        }
                        TextButton(onClick = { Prefs.addCustomFlag(e.domain) }) {
                            Text("Flag this server")
                        }
                        if (e.pkg.isNotEmpty()) {
                            TextButton(onClick = { onToggleBlock(e.pkg) }) {
                                Text(
                                    if (blocked.contains(e.pkg)) "Unblock ${e.app}"
                                    else "Block ${e.app}"
                                )
                            }
                        }
                    }
                }
            }
            HorizontalDivider()
            }
        }
    }
}

// ------------------------------------------------------------------ Blocked tab

@Composable
fun BlockedScreen() {
    val st by DnsVpnService.state.collectAsState()
    val list by BlockStore.entries.collectAsState()
    var query by remember { mutableStateOf("") }
    val pad = cardPad()
    val timeFormat = remember { SimpleDateFormat("dd MMM  HH:mm:ss", Locale.getDefault()) }
    val shown = remember(list, query) {
        if (query.isBlank()) list
        else list.filter {
            it.app.contains(query, ignoreCase = true) || it.dest.contains(query, ignoreCase = true)
        }
    }

    LazyColumn(
        Modifier.fillMaxSize(),
        contentPadding = PaddingValues(pad),
        verticalArrangement = Arrangement.spacedBy(6.dp)
    ) {
        item {
            Column(verticalArrangement = Arrangement.spacedBy(8.dp)) {
                Text(
                    if (st == "firewall") "Firewall is ON" else "Firewall is OFF",
                    style = MaterialTheme.typography.titleMedium
                )
                Text(
                    "Blocked apps are cut off, so nothing is sent. This list shows who they " +
                        "tried to contact: a server name (from lookups) or an IP address, and " +
                        "the port. Repeats within 2 seconds are merged. What they would have " +
                        "sent is not visible because it is encrypted.",
                    style = MaterialTheme.typography.bodySmall
                )
                OutlinedButton(onClick = { BlockStore.clear() }) { Text("Clear list") }
                OutlinedTextField(
                    value = query,
                    onValueChange = { query = it },
                    label = { Text("Search") },
                    singleLine = true,
                    modifier = Modifier.fillMaxWidth()
                )
                HorizontalDivider()
            }
        }
        if (shown.isEmpty()) {
            item {
                Text(
                    if (st == "firewall") "No attempts yet. They appear when a blocked app " +
                        "tries to connect."
                    else "Nothing recorded. Turn on the firewall in the Apps tab."
                )
            }
        }
        items(shown) { b ->
            Column(Modifier.fillMaxWidth()) {
                Text(b.dest, fontWeight = FontWeight.Medium)
                Text(
                    "${b.app}  ·  ${b.proto} ${b.port}  ·  ×${b.tries} tries",
                    style = MaterialTheme.typography.bodySmall
                )
                Text(
                    "Last: ${timeFormat.format(Date(b.last))}  ·  ${fmt(b.bytes)} stopped",
                    style = MaterialTheme.typography.bodySmall
                )
                Spacer(Modifier.height(4.dp))
                HorizontalDivider()
            }
        }
    }
}

// ------------------------------------------------------------------ Settings tab

@Composable
fun SettingsScreen() {
    var keywords by remember { mutableStateOf(Prefs.customFlags) }
    val pad = cardPad()

    LazyColumn(
        Modifier.fillMaxSize(),
        contentPadding = PaddingValues(pad),
        verticalArrangement = Arrangement.spacedBy(16.dp)
    ) {
        item {
            SettingBlock("Theme") {
                ChipRow(listOf("Auto", "Light", "Dark"), Prefs.theme) { Prefs.setTheme(it) }
            }
        }
        item {
            SettingBlock("Accent colour") {
                Row(horizontalArrangement = Arrangement.spacedBy(12.dp)) {
                    ACCENTS.forEachIndexed { i, a ->
                        val selected = Prefs.accent == i
                        Box(
                            Modifier.size(40.dp)
                                .clip(CircleShape)
                                .background(a.light)
                                .border(
                                    if (selected) 3.dp else 0.dp,
                                    MaterialTheme.colorScheme.onSurface,
                                    CircleShape
                                )
                                .clickable { Prefs.setAccent(i) }
                        )
                    }
                }
            }
        }
        item {
            SettingBlock("Text size") {
                ChipRow(listOf("Small", "Normal", "Large", "Extra large"), Prefs.textSize) {
                    Prefs.setTextSize(it)
                }
            }
        }
        item {
            SwitchRow(
                "Compact lists",
                "Less spacing so more fits on screen",
                Prefs.compact
            ) { Prefs.setCompact(it) }
        }
        item {
            SwitchRow(
                "Show system apps",
                "Include phone software in the Apps list. Be careful when blocking these.",
                Prefs.showSystem
            ) { Prefs.setShowSystem(it) }
        }
        item {
            SettingBlock("Warn when an app uploads more than this in the background") {
                val options = listOf(1, 5, 20, 50)
                ChipRow(options.map { "$it MB" }, options.indexOf(Prefs.uploadAlertMb)) {
                    Prefs.setUploadAlertMb(options[it])
                }
            }
        }
        item {
            SettingBlock("Your own keywords to flag in the Servers tab") {
                OutlinedTextField(
                    value = keywords,
                    onValueChange = {
                        keywords = it
                        Prefs.setCustomFlags(it)
                    },
                    label = { Text("e.g. ads, xyz.com, cdn") },
                    modifier = Modifier.fillMaxWidth()
                )
                Text(
                    "Separate with commas. Any server name containing a keyword is flagged.",
                    style = MaterialTheme.typography.bodySmall
                )
            }
        }
        item {
            SettingBlock("Data") {
                Row(horizontalArrangement = Arrangement.spacedBy(8.dp)) {
                    OutlinedButton(onClick = { LogStore.clear() }) { Text("Clear server log") }
                    OutlinedButton(onClick = { BlockStore.clear() }) { Text("Clear blocked list") }
                }
            }
        }
        item {
            Text(
                "Tip: for a firewall that stays on after a restart, open phone Settings > " +
                    "Network > VPN > NetWatch and switch on Always-on VPN. Nothing from this " +
                    "app is ever sent to any server.",
                style = MaterialTheme.typography.bodySmall
            )
        }
    }
}

@Composable
fun SettingBlock(title: String, content: @Composable () -> Unit) {
    Column(verticalArrangement = Arrangement.spacedBy(8.dp)) {
        Text(title, style = MaterialTheme.typography.titleSmall)
        content()
    }
}

@Composable
fun ChipRow(names: List<String>, selected: Int, onSelect: (Int) -> Unit) {
    Row(
        Modifier.horizontalScroll(rememberScrollState()),
        horizontalArrangement = Arrangement.spacedBy(8.dp)
    ) {
        names.forEachIndexed { i, n ->
            FilterChip(selected = selected == i, onClick = { onSelect(i) }, label = { Text(n) })
        }
    }
}

@Composable
fun SwitchRow(title: String, desc: String, checked: Boolean, onChange: (Boolean) -> Unit) {
    Row(verticalAlignment = Alignment.CenterVertically) {
        Column(Modifier.weight(1f)) {
            Text(title, style = MaterialTheme.typography.titleSmall)
            Text(desc, style = MaterialTheme.typography.bodySmall)
        }
        Switch(checked = checked, onCheckedChange = onChange)
    }
}
