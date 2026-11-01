@file:OptIn(ExperimentalMaterial3Api::class)

package com.netwatch.app

import android.app.AppOpsManager
import android.app.usage.NetworkStats
import android.app.usage.NetworkStatsManager
import android.content.Context
import android.content.Intent
import android.net.ConnectivityManager
import android.net.NetworkCapabilities
import android.net.Uri
import android.net.VpnService
import android.os.Bundle
import android.os.ParcelFileDescriptor
import android.os.Process
import android.provider.Settings
import android.system.OsConstants
import androidx.activity.ComponentActivity
import androidx.activity.compose.setContent
import androidx.activity.result.contract.ActivityResultContracts
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
import androidx.compose.foundation.layout.width
import androidx.compose.foundation.lazy.LazyColumn
import androidx.compose.foundation.lazy.items
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
import androidx.compose.material3.Scaffold
import androidx.compose.material3.Surface
import androidx.compose.material3.Switch
import androidx.compose.material3.Text
import androidx.compose.material3.TextButton
import androidx.compose.material3.TopAppBar
import androidx.compose.material3.darkColorScheme
import androidx.compose.material3.lightColorScheme
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.collectAsState
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableIntStateOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.platform.LocalContext
import androidx.compose.ui.text.font.FontWeight
import androidx.compose.ui.unit.dp
import java.io.File
import java.io.FileInputStream
import java.io.FileOutputStream
import java.net.DatagramPacket
import java.net.DatagramSocket
import java.net.InetAddress
import java.net.InetSocketAddress
import java.text.SimpleDateFormat
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

/** Minimal IPv4 / UDP / DNS helpers. Only what the DNS-logging VPN needs. */
object PacketUtils {

    class DnsPacket(
        val src: ByteArray,   // sender (the phone's VPN address)
        val dst: ByteArray,   // the fake DNS server address
        val srcPort: Int,
        val dstPort: Int,
        val payload: ByteArray
    )

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
        if (trackerWords.any { d.contains(it) }) return "Analytics / tracking"
        if (oemWords.any { d.contains(it) }) return "realme / OPPO service"
        return null
    }
}

data class LogEntry(
    val time: Long,
    val uid: Int,
    val app: String,
    val pkg: String,
    val domain: String,
    val flag: String?
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
                        if (p[5].isEmpty()) null else p[5]
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
        listOf(e.time, e.uid, clean(e.app), clean(e.pkg), clean(e.domain), e.flag ?: "")
            .joinToString("\t")

    private fun clean(s: String): String = s.replace('\t', ' ').replace('\n', ' ')
}

data class AppUsage(
    val uid: Int,
    val label: String,
    val packageName: String,
    val bgRx: Long,
    val bgTx: Long,
    val fgRx: Long,
    val fgTx: Long
) {
    val bgTotal: Long get() = bgRx + bgTx
    val total: Long get() = bgRx + bgTx + fgRx + fgTx
}

object UsageRepository {

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
            val label = when {
                pkg != null -> try {
                    pm.getApplicationLabel(pm.getApplicationInfo(pkg, 0)).toString()
                } catch (e: Exception) {
                    pkg
                }
                uid == 0 -> "Root / kernel"
                uid == 1000 -> "Android system"
                uid == -4 -> "Removed apps"
                uid == -5 -> "Hotspot / tethering"
                else -> "uid $uid"
            }
            result.add(AppUsage(uid, label, pkg ?: "", a[0], a[1], a[2], a[3]))
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
 * A local "DNS-only" VPN. Only DNS lookups are routed into this app; everything else
 * goes to the internet exactly as before. Each lookup is written to the log and then
 * passed on to the phone's normal DNS server, so browsing keeps working.
 * Nothing leaves the phone except the normal DNS lookup itself.
 */
class DnsVpnService : VpnService() {

    companion object {
        const val ACTION_START = "com.netwatch.app.START"
        const val ACTION_STOP = "com.netwatch.app.STOP"
        private const val DNS_ADDR = "10.111.222.1"
        private const val LOCAL_ADDR = "10.111.222.2"
        val running = MutableStateFlow(false)
    }

    private var tun: ParcelFileDescriptor? = null
    private var reader: Thread? = null
    private var pool: ExecutorService? = null

    @Volatile
    private var active = false

    private val appCache = ConcurrentHashMap<Int, Pair<String, String>>()
    private val lastSeen = ConcurrentHashMap<String, Long>()

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
        LogStore.init(applicationContext)

        val builder = Builder()
            .setSession("NetWatch")
            .addAddress(LOCAL_ADDR, 32)
            .addDnsServer(DNS_ADDR)
            .addRoute(DNS_ADDR, 32)
            .setMtu(1500)
            .setBlocking(true)
        try {
            builder.addDisallowedApplication(packageName)
        } catch (e: Exception) {
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
        running.value = true
        pool = Executors.newFixedThreadPool(6)
        reader = Thread({ readLoop(pfd) }, "netwatch-reader").also { it.start() }
    }

    private fun stopVpn() {
        active = false
        running.value = false
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

    private fun readLoop(pfd: ParcelFileDescriptor) {
        val input = FileInputStream(pfd.fileDescriptor)
        val output = FileOutputStream(pfd.fileDescriptor)
        val buf = ByteArray(32767)
        try {
            while (active) {
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
            if (active) {
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
        val uid = ownerUid(p)
        val key = "$uid|$domain"
        val now = System.currentTimeMillis()
        val prev = lastSeen[key]
        if (prev != null && now - prev < 3000) return // phones ask A and AAAA back to back
        lastSeen[key] = now
        if (lastSeen.size > 5000) lastSeen.clear()
        val (label, pkg) = appInfo(uid)
        LogStore.add(LogEntry(now, uid, label, pkg, domain, Domains.flag(domain)))
    }

    /**
     * Which app asked? Android often does DNS through a system service, so this can
     * come back as "Android system" even when an app was the real cause.
     */
    private fun ownerUid(p: PacketUtils.DnsPacket): Int {
        return try {
            val cm = getSystemService(ConnectivityManager::class.java)
            cm.getConnectionOwnerUid(
                OsConstants.IPPROTO_UDP,
                InetSocketAddress(InetAddress.getByAddress(p.src), p.srcPort),
                InetSocketAddress(InetAddress.getByAddress(p.dst), p.dstPort)
            )
        } catch (e: Exception) {
            -1
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
                    if (pkg == null) {
                        Pair("uid $uid", "")
                    } else {
                        val label = try {
                            packageManager.getApplicationLabel(
                                packageManager.getApplicationInfo(pkg, 0)
                            ).toString()
                        } catch (e: Exception) {
                            pkg
                        }
                        Pair(label, pkg)
                    }
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

class MainActivity : ComponentActivity() {

    private var resumeTick by mutableIntStateOf(0)

    private val vpnPermission =
        registerForActivityResult(ActivityResultContracts.StartActivityForResult()) { result ->
            if (result.resultCode == RESULT_OK) startVpnService()
        }

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        LogStore.init(this)
        setContent {
            val dark = isSystemInDarkTheme()
            MaterialTheme(colorScheme = if (dark) darkColorScheme() else lightColorScheme()) {
                Surface(modifier = Modifier.fillMaxSize()) {
                    NetWatchApp(
                        resumeTick = resumeTick,
                        onSetVpn = { start -> setVpn(start) },
                        onOpenUsageAccess = { openUsageAccess() }
                    )
                }
            }
        }
    }

    override fun onResume() {
        super.onResume()
        resumeTick++
    }

    private fun setVpn(start: Boolean) {
        if (start) {
            val intent = VpnService.prepare(this)
            if (intent != null) vpnPermission.launch(intent) else startVpnService()
        } else {
            startService(
                Intent(this, DnsVpnService::class.java).setAction(DnsVpnService.ACTION_STOP)
            )
        }
    }

    private fun startVpnService() {
        startService(
            Intent(this, DnsVpnService::class.java).setAction(DnsVpnService.ACTION_START)
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

@Composable
fun NetWatchApp(
    resumeTick: Int,
    onSetVpn: (Boolean) -> Unit,
    onOpenUsageAccess: () -> Unit
) {
    var tab by remember { mutableIntStateOf(0) }
    Scaffold(
        topBar = { TopAppBar(title = { Text("NetWatch") }) },
        bottomBar = {
            NavigationBar {
                NavigationBarItem(
                    selected = tab == 0,
                    onClick = { tab = 0 },
                    icon = { Text("📊") },
                    label = { Text("Data usage") }
                )
                NavigationBarItem(
                    selected = tab == 1,
                    onClick = { tab = 1 },
                    icon = { Text("🌐") },
                    label = { Text("Servers") }
                )
            }
        }
    ) { padding ->
        Box(Modifier.padding(padding).fillMaxSize()) {
            if (tab == 0) {
                UsageScreen(resumeTick, onOpenUsageAccess)
            } else {
                ServersScreen(onSetVpn)
            }
        }
    }
}

// ---------------------------------------------------------------- Data usage tab

@Composable
fun UsageScreen(resumeTick: Int, onOpenUsageAccess: () -> Unit) {
    val ctx = LocalContext.current
    var granted by remember { mutableStateOf(UsageRepository.hasPermission(ctx)) }
    var range by remember { mutableIntStateOf(1) }
    var sortBackground by remember { mutableStateOf(true) }
    var apps by remember { mutableStateOf<List<AppUsage>>(emptyList()) }
    var loading by remember { mutableStateOf(false) }
    var refresh by remember { mutableIntStateOf(0) }

    LaunchedEffect(resumeTick) {
        granted = UsageRepository.hasPermission(ctx)
    }
    LaunchedEffect(granted, range, resumeTick, refresh) {
        if (!granted) return@LaunchedEffect
        loading = true
        apps = withContext(Dispatchers.IO) {
            UsageRepository.load(ctx, UsageRepository.sinceMillis(range))
        }
        loading = false
    }

    if (!granted) {
        Column(Modifier.padding(24.dp), verticalArrangement = Arrangement.spacedBy(12.dp)) {
            Text("Usage access needed", style = MaterialTheme.typography.titleLarge)
            Text(
                "To see how much each app uploads and downloads, allow NetWatch under " +
                    "\"Usage access\" and switch it on. The numbers stay on your phone."
            )
            Button(onClick = onOpenUsageAccess) { Text("Open settings") }
        }
        return
    }

    val sorted = remember(apps, sortBackground) {
        if (sortBackground) apps.sortedByDescending { it.bgTotal }
        else apps.sortedByDescending { it.total }
    }
    val rangeNames = listOf("Today", "24 hours", "7 days")

    Column(Modifier.fillMaxSize()) {
        Row(
            Modifier.padding(horizontal = 12.dp, vertical = 4.dp),
            horizontalArrangement = Arrangement.spacedBy(8.dp)
        ) {
            rangeNames.forEachIndexed { i, name ->
                FilterChip(selected = range == i, onClick = { range = i }, label = { Text(name) })
            }
        }
        Row(
            Modifier.padding(horizontal = 12.dp),
            horizontalArrangement = Arrangement.spacedBy(8.dp),
            verticalAlignment = Alignment.CenterVertically
        ) {
            FilterChip(
                selected = sortBackground,
                onClick = { sortBackground = true },
                label = { Text("Most background") }
            )
            FilterChip(
                selected = !sortBackground,
                onClick = { sortBackground = false },
                label = { Text("Most total") }
            )
            TextButton(onClick = { refresh++ }) { Text("Refresh") }
        }
        if (loading && apps.isEmpty()) {
            LinearProgressIndicator(Modifier.fillMaxWidth())
        }
        LazyColumn(
            Modifier.fillMaxSize(),
            contentPadding = PaddingValues(12.dp),
            verticalArrangement = Arrangement.spacedBy(8.dp)
        ) {
            if (!loading && sorted.isEmpty()) {
                item { Text("No data found for this period.") }
            }
            items(sorted) { app -> UsageRow(app) }
            item {
                Text(
                    "Background = traffic while the app was not on screen (screen off included). " +
                        "↓ download, ↑ upload. Wi-Fi and mobile data added together.",
                    style = MaterialTheme.typography.bodySmall
                )
            }
        }
    }
}

@Composable
fun UsageRow(a: AppUsage) {
    Card(Modifier.fillMaxWidth()) {
        Column(Modifier.padding(12.dp)) {
            Text(a.label, fontWeight = FontWeight.SemiBold)
            if (a.packageName.isNotEmpty()) {
                Text(a.packageName, style = MaterialTheme.typography.bodySmall)
            }
            Spacer(Modifier.height(6.dp))
            Text(
                "Background   ↓ ${fmt(a.bgRx)}   ↑ ${fmt(a.bgTx)}",
                color = MaterialTheme.colorScheme.primary
            )
            Text(
                "On screen      ↓ ${fmt(a.fgRx)}   ↑ ${fmt(a.fgTx)}",
                style = MaterialTheme.typography.bodySmall
            )
        }
    }
}

// ---------------------------------------------------------------- Servers tab

@Composable
fun ServersScreen(onSetVpn: (Boolean) -> Unit) {
    val running by DnsVpnService.running.collectAsState()
    val entries by LogStore.entries.collectAsState()
    var onlyFlagged by remember { mutableStateOf(false) }
    val shown = remember(entries, onlyFlagged) {
        if (onlyFlagged) entries.filter { it.flag != null } else entries
    }
    val timeFormat = remember { SimpleDateFormat("dd MMM  HH:mm:ss", Locale.getDefault()) }

    Column(Modifier.fillMaxSize()) {
        Column(Modifier.padding(12.dp), verticalArrangement = Arrangement.spacedBy(8.dp)) {
            Text(
                if (running) "Monitoring is ON" else "Monitoring is OFF",
                style = MaterialTheme.typography.titleMedium
            )
            Text(
                "Lists every server name your phone looks up, in the background too. " +
                    "A lookup means a connection is about to happen; it does not show what was sent.",
                style = MaterialTheme.typography.bodySmall
            )
            Row(
                horizontalArrangement = Arrangement.spacedBy(8.dp),
                verticalAlignment = Alignment.CenterVertically
            ) {
                Button(onClick = { onSetVpn(!running) }) {
                    Text(if (running) "Stop" else "Start monitoring")
                }
                OutlinedButton(onClick = { LogStore.clear() }) { Text("Clear log") }
            }
            Row(verticalAlignment = Alignment.CenterVertically) {
                Switch(checked = onlyFlagged, onCheckedChange = { onlyFlagged = it })
                Spacer(Modifier.width(8.dp))
                Text("Only analytics / tracking / realme servers")
            }
        }
        HorizontalDivider()
        LazyColumn(
            Modifier.fillMaxSize(),
            contentPadding = PaddingValues(12.dp),
            verticalArrangement = Arrangement.spacedBy(8.dp)
        ) {
            if (shown.isEmpty()) {
                item {
                    Text(
                        if (running) "Waiting for lookups…"
                        else "Nothing logged yet. Tap Start monitoring."
                    )
                }
            }
            items(shown) { e ->
                Column {
                    Text(e.domain, fontWeight = FontWeight.Medium)
                    Text(
                        "${timeFormat.format(Date(e.time))}  ·  ${e.app}",
                        style = MaterialTheme.typography.bodySmall
                    )
                    if (e.flag != null) {
                        Text(
                            e.flag,
                            color = Color(0xFFD32F2F),
                            style = MaterialTheme.typography.bodySmall
                        )
                    }
                }
            }
        }
    }
}
