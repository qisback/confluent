
import asyncio
import base64
import codecs
import confluent.exceptions as exc
import confluent.vinzmanager as vinzmanager
import confluent.util as util
import confluent.messages as msg
import confluent.tasks as tasks
import aiohmi.util.webclient as webclient
import aiohmi.exceptions as pygexc
import confluent.interface.console as conapi
import confluent.log as log
import confluent.firmwaremanager as firmwaremanager
import functools
import random
import io
import json
import os
import re
import secrets
import tarfile
import time
import urllib.parse as urlparse
import aiohttp

def pve_error(body, status):
    # Non-2xx bodies arrive as raw bytes: JSON with 'message' and per-field 'errors'.
    if isinstance(body, bytes):
        try:
            body = json.loads(body)
        except ValueError:
            body = body.decode('utf8', 'replace')
    if isinstance(body, dict):
        message = (body.get('message') or '').strip()
        errors = body.get('errors')
        if isinstance(errors, dict):
            message = '{} ({})'.format(message, ', '.join(
                '{}: {}'.format(k, str(v).strip()) for k, v in errors.items()))
        body = message
    body = str(body or '').strip()
    return 'HTTP {}{}'.format(status, ': ' + body[:200] if body else '')


def next_config(pending):
    """Config as of the next start, from a /pending listing."""
    cfg = {}
    for datum in pending:
        if datum.get('delete'):
            continue
        if 'pending' in datum:
            cfg[datum['key']] = datum['pending']
        elif 'value' in datum:
            cfg[datum['key']] = datum['value']
    return cfg


# PVE's resolve_first_disk order.
_DRIVEBUSES = ('ide', 'scsi', 'virtio', 'sata')


def _devkey(dev):
    bus, num = re.match(r'([a-z]+)(\d+)$', dev).groups()
    busrank = _DRIVEBUSES.index(bus) if bus in _DRIVEBUSES else len(_DRIVEBUSES)
    return busrank, bus, int(num)


# confluent boot device -> device class moved to the front; None: disks first, network last.
BOOTCLASS = {'network': 'net', 'net': 'net', 'hd': 'disk', 'cd': 'cdrom', 'usb': 'usb', 'default': None}
# misc/proxmox/confluent-boot-oneshot.pl; makes a boot device one-time.
ONESHOT_HOOK = 'confluent-boot-oneshot.pl'
ONESHOT_MARKER = re.compile(r'^confluent-boot-restore: .*(?:\n|$)', re.M)


def device_class(dev, cfg):
    """net, usb, cdrom or disk, for a device named in a boot order."""
    if re.match(r'net\d+$', dev):
        return 'net'
    if re.match(r'usb\d+$', dev):
        # PVE ignores SPICE USB ports in the boot order.
        return None if (cfg.get(dev) or '').startswith('spice') else 'usb'
    if re.match(r'({})\d+$'.format('|'.join(_DRIVEBUSES)), dev):
        return 'cdrom' if 'media=cdrom' in (cfg.get(dev) or '') else 'disk'
    return None


def boot_devices(cfg):
    """Boot order as a device list: 'order=a;b' or legacy letters (default 'cdn').

    c: bootdisk or first disk, d: first CD-ROM, n: every NIC.
    """
    legacy = 'cdn'
    for item in (cfg.get('boot') or '').split(','):
        key, sep, val = item.partition('=')
        if key == 'order' and sep:
            return [dev for dev in val.split(';') if dev]
        if key == 'legacy' and sep:
            legacy = val
        elif key and not sep:
            legacy = key
    drives = sorted((key for key in cfg if re.match(r'({})\d+$'.format('|'.join(_DRIVEBUSES)), key)),
                    key=_devkey)
    cdroms = [key for key in drives if 'media=cdrom' in cfg[key]]
    disks = [key for key in drives if key not in cdroms]
    nets = sorted((key for key in cfg if re.match(r'net\d+$', key)), key=_devkey)
    devices = []
    for letter in legacy:
        if letter == 'c':
            bootdisk = cfg.get('bootdisk') if cfg.get('bootdisk') in disks else None
            if bootdisk or disks:
                devices.append(bootdisk or disks[0])
        elif letter == 'd' and cdroms:
            devices.append(cdroms[0])
        elif letter == 'n':
            devices.extend(nets)
    return devices


_SMBIOSFIELDS = (
    ('uuid', 'UUID'),
    ('manufacturer', 'Manufacturer'),
    ('product', 'Product name'),
    ('version', 'Version'),
    ('serial', 'Serial Number'),
    ('sku', 'SKU'),
    ('family', 'Family'),
)


def parse_smbios1(text):
    """smbios1 as a dict; with base64=1 every field but uuid is base64."""
    fields = {}
    for item in text.split(','):
        key, sep, val = item.partition('=')
        if sep:
            fields[key] = val
    if fields.get('base64') == '1':
        for key, val in fields.items():
            if key in ('uuid', 'base64'):
                continue
            try:
                fields[key] = base64.b64decode(val, validate=True).decode('utf8')
            except (ValueError, UnicodeDecodeError):
                pass
    return fields


# netN options; the remaining 'model=mac' pair is the NIC.
_NICOPTIONS = ('bridge', 'firewall', 'link_down', 'mtu', 'queues', 'rate', 'tag', 'trunks')


def parse_nic(text):
    """(model, mac) from a netN value: 'virtio=BC:24:..,bridge=vmbr0'."""
    model = mac = None
    for item in text.split(','):
        key, sep, val = item.partition('=')
        if key == 'model':
            model = val
        elif key == 'macaddr':
            mac = val
        elif sep and key not in _NICOPTIONS and model is None:
            model, mac = key, val
    return model, mac


_DRIVERE = re.compile(r'({})\d+$'.format('|'.join(_DRIVEBUSES)))
# Slots for a new CD-ROM, PVE's default first.
_CDROMSLOTS = ['ide2', 'ide0', 'ide1', 'ide3'] + ['sata{}'.format(n) for n in range(6)]


def drive_options(text):
    """(volume, {option: value}) from a drive value: 'local:iso/x.iso,media=cdrom'."""
    volume, _, rest = (text or '').partition(',')
    if volume.startswith('file='):
        volume = volume[len('file='):]
    opts = {}
    for item in rest.split(','):
        key, sep, val = item.partition('=')
        if sep:
            opts[key] = val
    return volume, opts


def cdrom_drives(cfg):
    return sorted((k for k in cfg if _DRIVERE.match(k) and 'media=cdrom' in (cfg[k] or '')), key=_devkey)


def disk_drives(cfg):
    return sorted((k for k in cfg if _DRIVERE.match(k) and 'media=cdrom' not in (cfg[k] or '')), key=_devkey)


def memory_mib(cfg):
    # Plain MiB, or 'current=N,...' (PVE 8.1+).
    text = str(cfg.get('memory', '512'))
    if '=' in text:
        text = dict(item.partition('=')[::2] for item in text.split(',')).get('current', '512')
    return int(text)


def simplify(name):
    """Component name as used in confluent paths."""
    return name.lower().replace(' ', '_')


def tag_list(cfg):
    return [tag for tag in re.split(r'[;, ]+', cfg.get('tags') or '') if tag]


# nodeidentify: no LED on a VM, so a tag shown in the PVE UI.
IDENTIFY_TAG = 'confluent-identify'

_MIB = 1048576.0
# name, status/current key, scale, units, valid while stopped.
_SENSORS = (
    ('CPU Usage', 'cpu', 100.0, '%', False),
    ('CPUs', 'cpus', 1, None, True),
    ('Memory Used', 'mem', 1 / _MIB, 'MiB', False),
    ('Memory Total', 'maxmem', 1 / _MIB, 'MiB', True),
    ('Disk Read', 'diskread', 1 / _MIB, 'MiB', False),
    ('Disk Written', 'diskwrite', 1 / _MIB, 'MiB', False),
    ('Network Received', 'netin', 1 / _MIB, 'MiB', False),
    ('Network Sent', 'netout', 1 / _MIB, 'MiB', False),
    ('Uptime', 'uptime', 1, 's', False),
    # PVE 9+.
    ('CPU Pressure', 'pressurecpusome', 1, '%', False),
    ('Memory Pressure', 'pressurememorysome', 1, '%', False),
    ('IO Pressure', 'pressureiosome', 1, '%', False),
)


def vm_sensors(status):
    running = status.get('status') == 'running'
    readings = []
    for name, key, scale, units, static in _SENSORS:
        if key not in status:
            continue
        reading = {'name': name, 'value': None, 'units': units, 'states': [], 'health': 'ok', 'type': 'VM'}
        if running or static:
            value = status[key]
            try:
                reading['value'] = round(float(value) * scale, 2)
            except (TypeError, ValueError):
                reading['states'] = ['Unavailable']
        else:
            reading['states'] = ['Unavailable']
        readings.append(reading)
    return readings


# Unhealthy QEMU run states.
_QMPHEALTH = {'paused': 'warning', 'io-error': 'critical', 'internal-error': 'critical',
              'guest-panicked': 'critical'}


def vm_health(status):
    """(health, non-ok readings) from status/current."""
    bad = []
    if status.get('status') == 'running':
        qmp = status.get('qmpstatus')
        if qmp in _QMPHEALTH:
            bad.append({'name': 'VM State', 'value': None, 'units': None, 'states': [qmp],
                        'health': _QMPHEALTH[qmp], 'type': 'VM'})
    hastate = (status.get('ha') or {}).get('state')
    if hastate == 'error':
        bad.append({'name': 'HA State', 'value': None, 'units': None, 'states': [hastate],
                    'health': 'critical', 'type': 'VM'})
    health = 'ok'
    for reading in bad:
        if reading['health'] == 'critical' or health == 'ok':
            health = reading['health']
    return health, bad


_TASKNAMES = {
    'qmstart': 'Start', 'qmstop': 'Stop', 'qmshutdown': 'Shutdown', 'qmreboot': 'Reboot',
    'qmreset': 'Reset', 'qmsuspend': 'Suspend', 'qmresume': 'Resume', 'qmpause': 'Pause',
    'qmigrate': 'Migrate', 'qmclone': 'Clone', 'qmcreate': 'Create', 'qmdestroy': 'Destroy',
    'qmconfig': 'Configure', 'qmmove': 'Move disk', 'qmrestore': 'Restore', 'qmtemplate': 'Make template',
    'qmsnapshot': 'Snapshot', 'qmdelsnapshot': 'Delete snapshot', 'qmrollback': 'Roll back snapshot',
    'vzdump': 'Backup', 'vncproxy': 'VNC console', 'termproxy': 'Serial console',
    'hamigrate': 'HA migrate', 'hastart': 'HA start', 'hastop': 'HA stop',
}


def task_event(task):
    """Event log entry from a PVE task list item."""
    status = task.get('status') or 'running'
    if status in ('OK', 'running'):
        severity = 'ok'
    elif status.startswith('WARNINGS'):
        severity = 'warning'
    else:
        severity = 'critical'
    name = _TASKNAMES.get(task.get('type'), task.get('type'))
    return {
        'severity': severity,
        'timestamp': time.strftime('%Y-%m-%dT%H:%M:%S', time.localtime(int(task.get('starttime', 0)))),
        'event': '{}: {}'.format(name, status),
        'message': '{} by {} on {}'.format(name, task.get('user'), task.get('node')),
        'component': 'VM {}'.format(task.get('id')),
        'component_type': 'Task',
        'id': task.get('type'),
        'record_id': task.get('upid'),
        'log_id': 'tasks',
    }


def agent_enabled(cfg):
    # '1', '1,fstrim_cloned_disks=1' or 'enabled=1,...'.
    first = str(cfg.get('agent', '0')).split(',')[0]
    return first.partition('=')[2] == '1' if '=' in first else first == '1'


def vm_inventory(cfg, host, vmid, guest=None):
    """nodeinventory items from the config; guest: agent {'os', 'interfaces'} or {'error'}."""
    smbios = parse_smbios1(cfg.get('smbios1', ''))
    info = {
        'Product name': 'Proxmox qemu virtual machine',
        'Manufacturer': 'qemu',
    }
    for field, label in _SMBIOSFIELDS:
        if smbios.get(field):
            info[label] = smbios[field]
    info['Model'] = info['Product name']
    info['Proxmox node'] = host
    info['VM ID'] = vmid
    items = [{'name': 'System', 'present': True, 'information': info}]
    cputype = (cfg.get('cpu') or 'kvm64').split(',')[0]
    if cputype.startswith('cputype='):
        cputype = cputype[len('cputype='):]
    sockets, cores = int(cfg.get('sockets', 1)), int(cfg.get('cores', 1))
    items.append({'name': 'CPU', 'present': True, 'information': {
        'Model': cputype, 'Sockets': sockets, 'Cores per socket': cores,
        'vCPUs': int(cfg.get('vcpus') or sockets * cores)}})
    items.append({'name': 'Memory', 'present': True, 'information': {
        'Size (MiB)': memory_mib(cfg), 'Balloon minimum (MiB)': cfg.get('balloon')}})
    guest = guest or {}
    addrsbymac = {}
    for iface in guest.get('interfaces') or []:
        mac = (iface.get('hardware-address') or '').lower()
        addrs = ['{}/{}'.format(a['ip-address'], a.get('prefix')) for a in iface.get('ip-addresses') or []
                 if a.get('ip-address') and not a['ip-address'].startswith(('127.', '::1', 'fe80:'))]
        if mac and addrs:
            addrsbymac.setdefault(mac, []).extend(addrs)
    for key in sorted((k for k in cfg if re.match(r'net\d+$', k)), key=_devkey):
        model, mac = parse_nic(cfg[key])
        info = {'Type': 'Ethernet', 'Model': model, 'MAC Address 1': mac}
        if addrsbymac.get((mac or '').lower()):
            info['IP Addresses'] = ', '.join(addrsbymac[mac.lower()])
        items.append({'name': 'Network adapter {}'.format(key), 'present': True, 'information': info})
    if guest.get('os'):
        osinfo = guest['os']
        items.append({'name': 'Guest OS', 'present': True, 'information': {
            'Name': osinfo.get('pretty-name') or osinfo.get('name'), 'Version': osinfo.get('version'),
            'Kernel': osinfo.get('kernel-release'), 'Architecture': osinfo.get('machine')}})
    elif guest.get('error'):
        items.append({'name': 'Guest OS', 'present': False, 'information': {
            'Status': 'QEMU guest agent: {}'.format(guest['error'])}})
    for key in disk_drives(cfg):
        volume, opts = drive_options(cfg[key])
        items.append({'name': 'Disk {}'.format(key), 'present': True, 'information': {
            'Type': 'Disk', 'Volume': volume, 'Size': opts.get('size'), 'Serial Number': opts.get('serial')}})
    for key in cdrom_drives(cfg):
        volume, _ = drive_options(cfg[key])
        items.append({'name': 'CD-ROM {}'.format(key), 'present': True, 'information': {
            'Type': 'CD-ROM', 'Media': None if volume == 'none' else volume}})
    if cfg.get('tpmstate0'):
        volume, opts = drive_options(cfg['tpmstate0'])
        items.append({'name': 'TPM', 'present': True, 'information': {
            'Version': opts.get('version', 'v1.2'), 'Volume': volume}})
    return items


# nodeconfig name -> (PVE key, PVE default, possible values, help).
_OSTYPES = ['other', 'wxp', 'w2k', 'w2k3', 'w2k8', 'wvista', 'win7', 'win8', 'win10', 'win11',
            'l24', 'l26', 'solaris']
SYSTEMSETTINGS = {
    'cores': ('cores', '1', None, 'CPU cores per socket'),
    'sockets': ('sockets', '1', None, 'CPU sockets'),
    'vcpus': ('vcpus', '', None, 'vCPUs plugged at start (empty: sockets x cores)'),
    'cpu': ('cpu', 'kvm64', None, 'Emulated CPU type, with optional flags'),
    'memory': ('memory', '512', None, 'Memory in MiB'),
    'balloon': ('balloon', '', None, 'Balloon target minimum in MiB; 0 disables the balloon device'),
    'numa': ('numa', '0', ['0', '1'], 'NUMA topology'),
    'bios': ('bios', 'seabios', ['seabios', 'ovmf'],
             'Firmware. Changing it under an installed OS usually leaves it unbootable'),
    'machine': ('machine', '', None, 'QEMU machine type (empty: newest i440fx)'),
    'ostype': ('ostype', 'other', _OSTYPES, 'Guest OS type, for PVE-side optimisations'),
    'onboot': ('onboot', '0', ['0', '1'], 'Start with the Proxmox node'),
    'agent': ('agent', '0', None, 'QEMU guest agent (1, or 1,fstrim_cloned_disks=1, ...)'),
    'tablet': ('tablet', '1', ['0', '1'], 'USB tablet for absolute pointer'),
    'protection': ('protection', '0', ['0', '1'], 'Refuse removal of the VM and its disks'),
}
TPMVERSIONS = ['none', 'v1.2', 'v2.0']


def system_settings(nextcfg, curcfg):
    """value: as of the next start; active: now."""
    settings = {}
    for name, (key, default, possible, helptext) in SYSTEMSETTINGS.items():
        setting = {'value': str(nextcfg.get(key, default)), 'active': str(curcfg.get(key, default)),
                   'default': default, 'help': helptext}
        if possible:
            setting['possible'] = possible
        settings[name] = setting
    tpm = [drive_options(cfg.get('tpmstate0'))[1].get('version', 'v1.2') if cfg.get('tpmstate0') else 'none'
           for cfg in (nextcfg, curcfg)]
    settings['tpm'] = {'value': tpm[0], 'active': tpm[1], 'default': 'none', 'possible': TPMVERSIONS,
                       'help': 'TPM state device. Removing it destroys the keys it holds'}
    secure = []
    for cfg in (nextcfg, curcfg):
        if cfg.get('bios') != 'ovmf':
            secure.append('n/a')
        elif drive_options(cfg.get('efidisk0'))[1].get('pre-enrolled-keys') == '1':
            secure.append('enabled')
        else:
            secure.append('disabled')
    settings['secure_boot'] = {
        'value': secure[0], 'active': secure[1], 'default': 'n/a',
        'help': 'UEFI Secure Boot (EFI disk with pre-enrolled keys). Read only: changing it means '
                'recreating the EFI disk'}
    return settings


class TaskFailed(Exception):
    """A PVE task ended with an error."""


class CustomVerifier(aiohttp.Fingerprint):
    def __init__(self, verifycallback):
        self._certverify = verifycallback

    def check(self, transport):
        sslobj = transport.get_extra_info("ssl_object")
        cert = sslobj.getpeercert(binary_form=True)
        if not self._certverify(cert):
            transport.close()
            raise pygexc.UnrecognizedCertificate('Unknown certificate',
                                                 cert)


class RetainedIO(io.BytesIO):
    # Need to retain buffer after close
    def __init__(self):
        self.resultbuffer = None
    def close(self):
        self.resultbuffer = self.getbuffer()
        super().close()

class KvmConnection:
    def __init__(self, consdata):
        #self.ws = WrappedWebSocket(host=bmc)
        #self.ws.set_verify_callback(kv)
        ticket = consdata['ticket']
        #user = consdata['user']
        port = consdata['port']
        urlticket = urlparse.quote(ticket)
        host = consdata['host']
        guest = consdata['guest']
        pac = consdata['pac']  # fortunately, we terminate this on our end, but it does kind of reduce the value of the
        # 'ticket' approach, as the general cookie must be provided as cookie along with the VNC ticket
        hosturl = host
        if ':' in hosturl:
            hosturl = '[' + hosturl + ']'
        self.url = f'/api2/json/nodes/{host}/{guest}/vncwebsocket?port={port}&vncticket={urlticket}'
        self.fprint = consdata['fprint']
        self.cookies = {
            'PVEAuthCookie': pac,
            }
        self.protos = ['binary']
        # The manager issued the ticket and owns the pinned fingerprint. It forwards the
        # websocket to the node running the guest, whose name may not resolve here.
        self.host = consdata['server']
        self.portnum = 8006
        self.password = consdata['ticket']


class KvmConnHandler:
    def __init__(self, pmxclient, node):
        self.pmxclient = pmxclient
        self.node = node

    async def connect(self):
        consdata = await self.pmxclient.get_vm_ikvm(self.node)
        consdata['fprint'] = self.pmxclient.fprint
        return KvmConnection(consdata)

class PmxConsole(conapi.Console):
    # termproxy drops idle sessions; xterm.js pings every 30s.
    keepalive_interval = 30

    def __init__(self, consdata, node, configmanager, apiclient):
        self.ws = None
        self.clisess = None
        self.consdata = consdata
        self.nodeconfig = configmanager
        self.connected = False
        self.bmc = consdata['server']
        self.node = node
        self.recvr = None
        self.keeper = None
        self.datacallback = None
        self.apiclient = apiclient
        # A UTF-8 character may span two writes.
        self.decoder = codecs.getincrementaldecoder('utf-8')('replace')

    async def lost(self):
        # Report the disconnect once.
        callback, self.datacallback = self.datacallback, None
        self.connected = False
        if callback:
            await callback(conapi.ConsoleEvent.Disconnect)

    async def recvdata(self):
        try:
            while self.connected:
                pendingdata = await self.ws.receive()
                if pendingdata.type == aiohttp.WSMsgType.BINARY:
                    await self.datacallback(pendingdata.data)
                elif pendingdata.type == aiohttp.WSMsgType.TEXT:
                    await self.datacallback(pendingdata.data.encode())
                elif pendingdata.type in (aiohttp.WSMsgType.PING, aiohttp.WSMsgType.PONG):
                    continue
                else:
                    # CLOSE, CLOSING, CLOSED or ERROR: session over.
                    await self.lost()
                    return
        except asyncio.CancelledError:
            pass

    async def keepalive(self):
        try:
            while self.connected:
                await asyncio.sleep(self.keepalive_interval)
                if self.connected:
                    await self.ws.send_str('2')
        except asyncio.CancelledError:
            pass
        except Exception:
            await self.lost()

    async def connect(self, callback):
        if await self.apiclient.get_vm_power(self.node) != 'on':
            await callback(conapi.ConsoleEvent.Disconnect)
            return
        # socket = new WebSocket(socketURL, 'binary'); - subprotocol binary
        # client handshake is:
        #     socket.send(PVE.UserName + ':' + ticket + "\n");

        # Peer sends 'OK' on handshake, other than that it's direct pass through
        # send '2' every 30 seconds for keepalive
        # data is xmitted with 0:<len>:data
        # resize is sent with 1:columns:rows:""
        self.datacallback = callback
        kv = util.TLSCertVerifier(
            self.nodeconfig, self.node, 'pubkeys.tls_hardwaremanager').verify_cert
        if ':' in self.bmc and not self.bmc.startswith('['):
            self.bmc = '[{0}]'.format(self.bmc)
        self.ssl = CustomVerifier(kv)
        ticket = self.consdata['ticket']
        user = self.consdata['user']
        port = self.consdata['port']
        urlticket = urlparse.quote(ticket)
        host = self.consdata['host']
        guest = self.consdata['guest']
        pac = self.consdata['pac']  # fortunately, we terminate this on our end, but it does kind of reduce the value of the
        # 'ticket' approach, as the general cookie must be provided as cookie along with the VNC ticket
        cookies = aiohttp.CookieJar(unsafe=True, quote_cookie=False)
        headers = {}
        if pac:
            cookies.update_cookies({'PVEAuthCookie': pac})
        if self.consdata.get('authorization'):
            headers['Authorization'] = self.consdata['authorization']
        self.clisess = aiohttp.ClientSession(cookie_jar=cookies)
        try:
            self.ws = await self.clisess.ws_connect(
                f'wss://{self.bmc}:8006/api2/json/nodes/{host}/{guest}/vncwebsocket?port={port}&vncticket={urlticket}',
                protocols=['binary'], ssl=self.ssl, headers=headers)
            await self.ws.send_str(f'{user}:{ticket}\n')
            data = await self.ws.receive()
            if data.data not in (b'OK', 'OK'):
                raise exc.TargetEndpointUnreachable(
                    'termproxy refused the session for {}: {!r}'.format(self.node, data.data))
            await self.ws.receive()  # swallow the 'starting serial terminal' message
        except Exception:
            await self.close()
            await callback(conapi.ConsoleEvent.Disconnect)
            return
        self.connected = True
        self.recvr = tasks.spawn_task(self.recvdata())
        self.keeper = tasks.spawn_task(self.keepalive())

    async def write(self, data):
        try:
            text = self.decoder.decode(data)
            if not text:
                return
            # Length in UTF-8 bytes, as xterm.js sends it.
            await self.ws.send_str('0:{}:{}'.format(len(text.encode('utf-8')), text))
        except Exception:
            await self.lost()

    async def close(self):
        if self.recvr:
            self.recvr.cancel()
            self.recvr = None
        if self.keeper:
            self.keeper.cancel()
            self.keeper = None
        if self.ws:
            await self.ws.close()
        if self.clisess:
            await self.clisess.close()
        self.connected = False
        self.datacallback = None

class PmxApiClient:
    def __init__(self, server, user, password, configmanager, node=None):
        self.user = user
        self.password = password
        self.pac = None
        pinnode, pinfield = server, 'pubkeys.tls'
        if configmanager and node is not None and \
                server not in configmanager.get_node_attributes(server, 'pubkeys.tls'):
            # Manager is not a confluent node: pin on the guest's node, as the console does.
            pinnode, pinfield = node, 'pubkeys.tls_hardwaremanager'
        if configmanager:
            cv = util.TLSCertVerifier(
                configmanager, pinnode, pinfield, subject=server
            ).verify_cert
        else:
            def cv(x):
                return True

        try:
            self.user = self.user.decode()
            self.password = self.password.decode()
        except Exception:
            pass
        self.server = server
        self.wc = webclient.WebConnection(server, port=8006, verifycallback=cv)
        self.fprint = None
        if configmanager:
            self.fprint = configmanager.get_node_attributes(pinnode, pinfield).get(pinnode, {}).get(pinfield, {}).get('value', None)
        self.vmmap = {}
        self.vmdupes = {}
        self.vmlist = {}
        self.vmbyid = {}
        self.pvenodes = []
        self.logged = False

    @property
    def token(self):
        # 'user@realm!tokenid', secret as the password.
        return '!' in (self.user or '')

    async def login(self):
        if self.token:
            # Stateless: no ticket or CSRF token; a bad token is a 401 on first use.
            self.wc.set_header('Authorization', 'PVEAPIToken={}={}'.format(self.user, self.password))
            self.logged = True
            return
        loginform = {
                'username': self.user,
                'password': self.password,
            }
        loginbody = urlparse.urlencode(loginform)
        try:
            body, status = await self.wc.grab_json_response_with_status('/api2/json/access/ticket', loginbody, headers={'Content-Type': 'application/x-www-form-urlencoded'})
        except Exception:
            raise exc.TargetEndpointUnreachable("Unable to reach Proxmox server '{}'".format(self.server))
        if status == 401:
            raise exc.TargetEndpointBadCredentials("Bad credentials")
        data = body.get('data') if isinstance(body, dict) else None
        if status != 200 or not isinstance(data, dict) or 'ticket' not in data:
            raise exc.TargetEndpointUnreachable("Proxmox server '{}' refused login: {}".format(
                self.server, pve_error(body, status)))
        if data.get('NeedTFA'):
            raise exc.TargetEndpointBadCredentials(
                "Proxmox user '{}' requires two-factor authentication, which is not supported".format(self.user))
        self.pac = data['ticket']
        self.wc.cookies.update_cookies({'PVEAuthCookie': self.pac})
        self.wc.set_header('CSRFPreventionToken', data['CSRFPreventionToken'])
        self.logged = True

    async def api(self, method, path, data=None, vm=None):
        """Call the PVE API; returns 'data'.

        With vm, path is relative to /nodes/<node>/qemu/<id>/. Retries once
        after a 401 (expired ticket) and once after a migration.
        """
        retried = set()
        while True:
            if not self.logged:
                await self.login()
            url = path
            if vm is not None:
                host, guest = await self.get_vm(vm)
                url = f'/api2/json/nodes/{host}/{guest}/{path}'
            try:
                body, status = await self.wc.grab_json_response_with_status(url, data, method=method)
            except Exception:
                raise exc.TargetEndpointUnreachable("Unable to reach Proxmox server '{}'".format(self.server))
            if 200 <= status < 300:
                return body.get('data') if isinstance(body, dict) else body
            message = pve_error(body, status)
            if status == 401 and 'login' not in retried:
                retried.add('login')
                self.logged = False
                continue
            if vm is not None and 'does not exist' in message and 'map' not in retried:
                retried.add('map')
                self.vmmap.pop(vm, None)
                continue
            if status == 401:
                raise exc.TargetEndpointBadCredentials(message)
            raise exc.TargetResourceUnavailable(
                'Proxmox server {} {} {}: {}'.format(self.server, method, url, message))

    def get_screenshot(self, vm, outfile):
        raise Exception("Not implemented")

    async def map_vms(self):
        resources = await self.api('GET', '/api2/json/cluster/resources')
        # Names need not be unique; templates are skipped.
        byname = {}
        self.pvenodes = sorted(datum['node'] for datum in resources or []
                               if datum['type'] == 'node' and datum.get('status') != 'offline')
        for datum in resources or []:
            if datum['type'] == 'qemu' and not datum.get('template'):
                byname.setdefault(datum.get('name'), []).append((datum['node'], datum['id']))
        self.vmmap = dict((name, vms[0]) for name, vms in byname.items() if len(vms) == 1)
        self.vmdupes = dict((name, [guest for _, guest in vms]) for name, vms in byname.items() if len(vms) > 1)
        return self.vmmap


    async def get_vm(self, vm):
        if vm not in self.vmmap:
            await self.map_vms()
        if vm in self.vmdupes:
            raise exc.InvalidArgumentException(
                "VM name {} is used by more than one guest on Proxmox server {} ({}); "
                "rename all but one".format(vm, self.server, ', '.join(self.vmdupes[vm])))
        if vm not in self.vmmap:
            raise exc.NotFoundException("VM {} not found on Proxmox server {}".format(vm, self.server))
        return self.vmmap[vm]


    async def get_vm_inventory(self, vm, component='all'):
        # Current config: pending NICs are not present yet.
        cfg = await self.api('GET', 'config', vm=vm)
        host, guest = await self.get_vm(vm)
        guestinfo = None
        if component in ('all', 'guest_os') or component.startswith('network'):
            guestinfo = await self.get_guest_info(vm, cfg)
        invitems = vm_inventory(cfg, host, guest.split('/')[-1], guestinfo)
        if component != 'all':
            invitems = [item for item in invitems if component in (item['name'], simplify(item['name']))]
        yield msg.KeyValueData({'inventory': invitems}, vm)

    async def get_guest_info(self, vm, cfg):
        """Guest agent OS and interfaces; None if no agent or VM off, {'error'} if it fails.

        Needs VM.GuestAgent.Audit (PVE 9) or VM.Monitor (PVE 8).
        """
        if not agent_enabled(cfg) or await self.get_vm_power(vm) != 'on':
            return None
        info = {}
        try:
            info['os'] = ((await self.api('GET', 'agent/get-osinfo', vm=vm)) or {}).get('result')
            info['interfaces'] = ((await self.api('GET', 'agent/network-get-interfaces', vm=vm)) or {}).get('result')
        except exc.TargetResourceUnavailable as e:
            # e.g. 'HTTP 500: QEMU guest agent is not running'.
            return {'error': 'HTTP ' + str(e).split(': HTTP ', 1)[-1]}
        return info

    # Most recent task logs to include.
    servicedata_tasklogs = 25

    async def collect_servicedata(self, vm, filename, progress, data=None):
        """nodesupport servicedata: config, pending, status, agent, tasks and task logs.

        Writes <filename>.tar.gz; returns the path.
        """
        if not filename.endswith(('.tar.gz', '.tgz')):
            filename += '.tar.gz'
        if os.path.exists(filename):
            raise exc.InvalidArgumentException('{} already exists, cannot overwrite'.format(filename))
        host, guest = await self.get_vm(vm)
        vmid = guest.split('/')[-1]
        members = {}
        members['config.json'] = await self.api('GET', 'config', vm=vm)
        members['pending.json'] = await self.api('GET', 'pending', vm=vm)
        members['status.json'] = await self.get_vm_status(vm)
        members['guest-agent.json'] = await self.get_guest_info(vm, members['config.json'])
        members['version.json'] = await self.api('GET', '/api2/json/version')
        progress({'phase': 'download', 'progress': 10.0})
        tasks = []
        for pvenode in self.pvenodes or [host]:
            try:
                tasks.extend(t for t in await self.api(
                    'GET', '/api2/json/nodes/{}/tasks?vmid={}&limit=500&source=all'.format(pvenode, vmid)) or []
                    if str(t.get('id')) == vmid)
            except exc.TargetResourceUnavailable as e:
                if pvenode == host:
                    raise
                tasks.append({'node': pvenode, 'error': str(e)})
        tasks.sort(key=lambda task: int(task.get('starttime', 0)))
        members['tasks.json'] = tasks
        recent = [t for t in tasks if t.get('upid')][-self.servicedata_tasklogs:]
        for num, task in enumerate(recent):
            lines = await self.api('GET', '/api2/json/nodes/{}/tasks/{}/log?limit=5000'.format(
                task['node'], urlparse.quote(task['upid'], safe='')))
            name = 'tasklogs/{}-{}-{}.log'.format(task.get('starttime'), task.get('type'), task['node'])
            members[name] = '\n'.join(line.get('t', '') for line in lines or []) + '\n'
            progress({'phase': 'download', 'progress': 10.0 + 85.0 * (num + 1) / len(recent)})

        def write():
            topdir = '{}-pve-{}'.format(vm, time.strftime('%Y%m%dT%H%M%S'))
            with tarfile.open(filename, 'w:gz') as tar:
                for name, content in members.items():
                    if not isinstance(content, str):
                        content = json.dumps(content, indent=2, sort_keys=True) + '\n'
                    blob = content.encode('utf8')
                    info = tarfile.TarInfo('{}/{}'.format(topdir, name))
                    info.size = len(blob)
                    info.mtime = int(time.time())
                    tar.addfile(info, io.BytesIO(blob))
        await asyncio.to_thread(write)
        return filename

    async def get_vm_status(self, vm):
        return await self.api('GET', 'status/current', vm=vm)

    async def get_vm_firmware(self, vm):
        cfg = await self.api('GET', 'config', vm=vm)
        status = await self.get_vm_status(vm)
        version = await self.api('GET', '/api2/json/version')
        running = status.get('status') == 'running'
        return [
            {'BIOS': {'version': 'OVMF (UEFI)' if cfg.get('bios') == 'ovmf' else 'SeaBIOS'}},
            {'QEMU': {'version': status.get('running-qemu') if running else None}},
            {'Machine type': {'version': (status.get('running-machine') if running else None)
                              or cfg.get('machine') or 'pc (newest i440fx)'}},
            {'Proxmox VE': {'version': (version or {}).get('version')}},
        ]

    async def get_vm_events(self, vm):
        """Task history from every cluster node (migrated VMs span several).

        Without Sys.Audit, PVE lists only the caller's own tasks.
        """
        host, guest = await self.get_vm(vm)
        vmid = guest.split('/')[-1]
        events = []
        for pvenode in self.pvenodes or [host]:
            try:
                tasklist = await self.api('GET', '/api2/json/nodes/{}/tasks?vmid={}&limit=500&source=all'.format(
                    pvenode, vmid))
            except exc.TargetResourceUnavailable:
                if pvenode == host:
                    raise
                continue
            events.extend(task for task in tasklist or [] if str(task.get('id')) == vmid)
        events.sort(key=lambda task: int(task.get('starttime', 0)))
        return [task_event(task) for task in events]

    async def get_vm_location(self, vm):
        host, guest = await self.get_vm(vm)
        return {'manager': self.server, 'pve_node': host, 'vmid': guest.split('/')[-1]}

    async def get_vm_identify(self, vm):
        cfg = await self.api('GET', 'config', vm=vm)
        return 'on' if IDENTIFY_TAG in tag_list(cfg) else 'off'

    async def set_vm_identify(self, vm, state):
        if state not in ('on', 'off', 'blink'):
            raise exc.InvalidArgumentException('Unsupported identify state {}'.format(state))
        cfg = await self.api('GET', 'config', vm=vm)
        tags = tag_list(cfg)
        want = state != 'off'
        if (IDENTIFY_TAG in tags) == want:
            return
        tags = [tag for tag in tags if tag != IDENTIFY_TAG] + ([IDENTIFY_TAG] if want else [])
        await self.api('PUT', 'config', {'tags': ';'.join(tags)} if tags else {'delete': 'tags'}, vm=vm)

    async def reseat_vm(self, vm):
        # Hard off, then on; a cold start applies pending config.
        if await self.get_vm_power(vm) == 'on':
            await self.set_vm_power(vm, 'off')
        await self.set_vm_power(vm, 'on')

    async def wait_task(self, host, upid, timeout):
        loop = asyncio.get_running_loop()
        deadline = loop.time() + timeout
        while True:
            task = await self.api('GET', '/api2/json/nodes/{}/tasks/{}/status'.format(
                host, urlparse.quote(upid, safe='')))
            if task.get('status') == 'stopped':
                exitstatus = task.get('exitstatus') or ''
                if exitstatus != 'OK' and not exitstatus.startswith('WARNINGS'):
                    raise TaskFailed('PVE task {} failed: {}'.format(
                        upid.split(':')[5] if upid.count(':') > 5 else upid, exitstatus))
                return
            if loop.time() >= deadline:
                raise exc.TargetResourceUnavailable('PVE task {} still running after {} seconds'.format(
                    upid, timeout))
            await asyncio.sleep(1)

    # nodemedia: virtual CD-ROMs.

    async def get_vm_media(self, vm):
        cfg = next_config(await self.api('GET', 'pending', vm=vm))
        media = []
        for key in cdrom_drives(cfg):
            volume, _ = drive_options(cfg[key])
            if volume == 'none':
                continue
            location, sep, name = volume.rpartition('/')
            media.append({'name': name, 'url': location if sep else None, 'secure': True})
        return media

    async def iso_storage(self, host):
        """First active ISO storage on host."""
        stores = await self.api('GET', '/api2/json/nodes/{}/storage?content=iso&enabled=1'.format(host))
        for store in sorted(stores or [], key=lambda s: s['storage']):
            if store.get('active', 1):
                return store['storage']
        # PVE lists only storages the user can audit.
        raise exc.InvalidArgumentException(
            'No active storage for ISO images (content type iso) on Proxmox node {} is visible to {}; '
            'it needs Datastore.Audit on that storage'.format(host, self.user))

    async def attach_media(self, vm, url):
        """Insert url in the CD-ROM: http(s)/ftp is downloaded to ISO storage
        (reused if present); pve://storage:path is an existing volume.

        The confluent input check treats anything without '://' as a local file.
        """
        if url.startswith('pve://'):
            url = url[len('pve://'):]
        if re.match(r'(https?|ftp)://', url):
            host, _ = await self.get_vm(vm)
            storage = await self.iso_storage(host)
            name = urlparse.unquote(urlparse.urlsplit(url).path.rsplit('/', 1)[-1])
            if not re.match(r'[\w.+-]+\.(iso|img)$', name, re.I):
                raise exc.InvalidArgumentException(
                    'The URL must name an .iso or .img file, as Proxmox stores it under that name: {}'.format(url))
            volid = '{}:iso/{}'.format(storage, name)
            content = await self.api('GET', '/api2/json/nodes/{}/storage/{}/content?content=iso'.format(
                host, storage))
            if volid not in [item.get('volid') for item in content or []]:
                try:
                    upid = await self.api('POST', '/api2/json/nodes/{}/storage/{}/download-url'.format(
                        host, storage), {'content': 'iso', 'filename': name, 'url': url})
                except exc.TargetResourceUnavailable as e:
                    if 'HTTP 403' not in str(e):
                        raise
                    # PVE's 403 does not say which right (PVE 9.2).
                    raise exc.TargetResourceUnavailable(
                        '{} may not download to {}: that needs Datastore.AllocateTemplate on the storage '
                        'and both Sys.Audit and Sys.Modify on / ({})'.format(self.user, storage, e))
                await self.wait_task(host, upid, 3600)
        elif re.match(r'[\w.-]+:[^/]', url):
            volid = url
        else:
            raise exc.InvalidArgumentException(
                'Proxmox media must be an http(s) or ftp URL, or a volume (pve://storage:iso/name.iso); '
                'use nodemedia upload for a local file')
        await self.insert_cdrom(vm, volid)

    async def insert_cdrom(self, vm, volid):
        cfg = next_config(await self.api('GET', 'pending', vm=vm))
        drives = cdrom_drives(cfg)
        if drives:
            slot = drives[0]
        else:
            free = [slot for slot in _CDROMSLOTS if slot not in cfg]
            if not free:
                raise exc.InvalidArgumentException('{} has no CD-ROM and no free IDE/SATA slot'.format(vm))
            slot = free[0]
        await self.api('PUT', 'config', {slot: '{},media=cdrom'.format(volid)}, vm=vm)
        if not drives and await self.get_vm_power(vm) == 'on':
            log.log({'info': '{}: added CD-ROM {} with {}; a running VM sees it after its next cold '
                             'start'.format(vm, slot, volid)})

    async def detach_media(self, vm):
        cfg = next_config(await self.api('GET', 'pending', vm=vm))
        update = {}
        for key in cdrom_drives(cfg):
            if drive_options(cfg[key])[0] != 'none':
                update[key] = 'none,media=cdrom'
        if update:
            await self.api('PUT', 'config', update, vm=vm)

    async def upload_media(self, vm, filename, progress, data=None):
        """nodemedia upload: stream a local image to ISO storage, then insert it."""
        host, _ = await self.get_vm(vm)
        storage = await self.iso_storage(host)
        if not self.logged:
            await self.login()
        name = os.path.basename(filename)
        fileobj = data if data is not None else open(filename, 'rb')
        try:
            fileobj.seek(0, 2)
            size = fileobj.tell()
            fileobj.seek(0)
            boundary = secrets.token_hex(16)
            head = ('--{0}\r\nContent-Disposition: form-data; name="content"\r\n\r\niso\r\n'
                    '--{0}\r\nContent-Disposition: form-data; name="filename"; filename="{1}"\r\n'
                    'Content-Type: application/octet-stream\r\n\r\n').format(boundary, name).encode()
            tail = '\r\n--{0}--\r\n'.format(boundary).encode()

            async def body():
                yield head
                sent = 0
                while True:
                    chunk = await asyncio.to_thread(fileobj.read, 1 << 20)
                    if not chunk:
                        break
                    sent += len(chunk)
                    progress({'phase': 'upload', 'progress': 100.0 * sent / size if size else 100.0})
                    yield chunk
                yield tail
            headers = dict(self.wc.stdheaders)
            headers['Content-Type'] = 'multipart/form-data; boundary=' + boundary
            headers['Content-Length'] = str(len(head) + size + len(tail))
            url = 'https://{}:8006/api2/json/nodes/{}/storage/{}/upload'.format(self.wc.host, host, storage)
            async with aiohttp.ClientSession(cookie_jar=self.wc.cookies,
                                             timeout=aiohttp.ClientTimeout(total=None)) as session:
                async with session.post(url, data=body(), headers=headers, ssl=self.wc.ssl) as rsp:
                    rspbody = await rsp.read()
                    if rsp.status != 200:
                        raise exc.TargetResourceUnavailable('Upload of {} to {} on {} failed: {}'.format(
                            name, storage, host, pve_error(rspbody, rsp.status)))
                    upid = json.loads(rspbody).get('data')
        finally:
            fileobj.close()
        if upid:
            # Task moves the upload into the storage.
            await self.wait_task(host, upid, 600)
        await self.insert_cdrom(vm, '{}:iso/{}'.format(storage, name))

    # nodeconfig: VM settings.

    async def get_vm_settings(self, vm):
        nextcfg = next_config(await self.api('GET', 'pending', vm=vm))
        curcfg = await self.api('GET', 'config', vm=vm)
        return system_settings(nextcfg, curcfg)

    async def set_vm_settings(self, vm, changes):
        update = {}
        delete = []
        for name, value in changes.items():
            value = '' if value is None else str(value)
            if name == 'tpm':
                await self.set_vm_tpm(vm, value)
                continue
            if name == 'secure_boot':
                raise exc.InvalidArgumentException(
                    'secure_boot is read only: it is set by the keys enrolled on the EFI disk')
            if name not in SYSTEMSETTINGS:
                raise exc.InvalidArgumentException('{} is not a Proxmox VM setting; settable: {}'.format(
                    name, ', '.join(sorted(list(SYSTEMSETTINGS) + ['tpm']))))
            key, _, possible, _ = SYSTEMSETTINGS[name]
            if value == '':
                delete.append(key)
            elif possible and value not in possible:
                raise exc.InvalidArgumentException('{} must be one of {}'.format(name, ', '.join(possible)))
            else:
                update[key] = value
        if delete:
            update['delete'] = ','.join(delete)
        if update:
            await self.api('PUT', 'config', update, vm=vm)

    async def set_vm_tpm(self, vm, version):
        if version not in TPMVERSIONS:
            raise exc.InvalidArgumentException('tpm must be one of {}'.format(', '.join(TPMVERSIONS)))
        cfg = next_config(await self.api('GET', 'pending', vm=vm))
        current = drive_options(cfg['tpmstate0'])[1].get('version', 'v1.2') if cfg.get('tpmstate0') else 'none'
        if version == current:
            return
        if version == 'none':
            await self.api('PUT', 'config', {'delete': 'tpmstate0'}, vm=vm)
            return
        if current != 'none':
            raise exc.InvalidArgumentException(
                '{} already has a {} TPM; set tpm=none first (this destroys its keys)'.format(vm, current))
        # TPM state on the EFI disk's storage, else the first disk's.
        source = cfg.get('efidisk0') or next((cfg[k] for k in disk_drives(cfg)), None)
        if not source or ':' not in source:
            raise exc.InvalidArgumentException('{} has no disk storage to put a TPM state on'.format(vm))
        storage = drive_options(source)[0].split(':', 1)[0]
        await self.api('PUT', 'config', {'tpmstate0': '{}:1,version={}'.format(storage, version)}, vm=vm)


    async def get_vm_ikvm(self, vm):
        return await self.get_vm_consproxy(vm, 'vnc')

    async def get_vm_serial(self, vm):
        return await self.get_vm_consproxy(vm, 'term')

    async def get_vm_consproxy(self, vm, constype):
        powstate = await self.get_vm_power(vm)
        if powstate != 'on':
            await asyncio.sleep(1 + random.random())
        consdata = await self.api('POST', f'{constype}proxy', vm=vm)
        # vmmap is current after api().
        host, guest = await self.get_vm(vm)
        consdata['server'] = self.server
        consdata['host'] = host
        consdata['guest'] = guest
        consdata['pac'] = self.pac
        consdata['authorization'] = self.wc.stdheaders.get('Authorization')
        return consdata

    async def get_vm_bootdev(self, vm):
        """(nextdevice, bootmode, persistent)."""
        cfg = next_config(await self.api('GET', 'pending', vm=vm))
        devices = boot_devices(cfg)
        first = device_class(devices[0], cfg) if devices else None
        nextdev = {'net': 'network', 'cdrom': 'cd', 'usb': 'usb'}.get(first, 'default')
        bootmode = 'uefi' if cfg.get('bios') == 'ovmf' else 'bios'
        persistent = ONESHOT_MARKER.search(cfg.get('description') or '') is None
        return nextdev, bootmode, persistent


    async def get_vm_power(self, vm):
        rsp = await self.api('GET', 'status/current', vm=vm)
        # 'status' is whether the QEMU process exists: any live process is on.
        currstatus = rsp.get('status')
        if currstatus == 'running':
            return 'on'
        elif currstatus == 'stopped':
            return 'off'
        raise exc.TargetResourceUnavailable(
            'Unknown power status {!r} (qmpstatus {!r}) for {}'.format(currstatus, rsp.get('qmpstatus'), vm))

    async def get_vm_powerstate(self, vm):
        """on, off, paused, suspended (to RAM) or hibernated (to disk)."""
        rsp = await self.get_vm_status(vm)
        if rsp.get('status') == 'running':
            return {'paused': 'paused', 'suspended': 'suspended'}.get(rsp.get('qmpstatus'), 'on')
        if rsp.get('status') == 'stopped':
            return 'hibernated' if rsp.get('lock') == 'suspended' else 'off'
        return await self.get_vm_power(vm)

    async def inject_nmi(self, vm):
        if await self.get_vm_power(vm) != 'on':
            raise exc.InvalidArgumentException('{} is not running; an NMI needs a running VM'.format(vm))
        try:
            await self.api('POST', 'monitor', {'command': 'nmi'}, vm=vm)
        except exc.TargetResourceUnavailable as e:
            # 'nmi' is root@pam only (PVE 9); other non-info commands need Sys.Modify on /.
            if 'HTTP 403' in str(e) or 'root-only' in str(e):
                raise exc.TargetResourceUnavailable(
                    'diag sends an NMI through the QEMU monitor, which Proxmox allows for root@pam '
                    'only: {}'.format(e))
            raise

    # Seconds per action; shutdown waits on the guest's ACPI handling.
    power_timeout = {'start': 60, 'stop': 60, 'shutdown': 300}

    async def set_vm_power(self, vm, state):
        current = None
        if state == 'diag':
            await self.inject_nmi(vm)
            return 'diag', None
        if state not in ('on', 'off', 'shutdown', 'boot', 'reset'):
            raise exc.InvalidArgumentException('Unsupported power state {}'.format(state))
        if state == 'on':
            current = await self.get_vm_powerstate(vm)
            if current in ('paused', 'suspended'):
                # PVE refuses start on a paused/suspended VM.
                host, _ = await self.get_vm(vm)
                upid = await self.api('POST', 'status/resume', vm=vm)
                try:
                    await self.wait_task(host, upid, self.power_timeout['start'])
                except TaskFailed as e:
                    raise exc.TargetResourceUnavailable(str(e))
                return 'on', current
            # Hibernated: start resumes from disk.
            current = None
        if state == 'boot':
            current = await self.get_vm_power(vm)
            action = 'reset' if current == 'on' else 'start'
        elif state == 'reset':
            action = 'reset'
        else:
            # IPMI semantics: on when on, off when off, is a no-op.
            target = 'on' if state == 'on' else 'off'
            if await self.get_vm_power(vm) == target:
                return target, None
            action = {'on': 'start', 'off': 'stop', 'shutdown': 'shutdown'}[state]
        if action == 'reset':
            # Pending boot order needs a cold start.
            cfg = await self.api('GET', 'pending', vm=vm)
            if any(datum['key'] == 'boot' and 'pending' in datum for datum in cfg):
                await self.set_vm_power(vm, 'off')
                await self.set_vm_power(vm, 'on')
            else:
                await self.api('POST', 'status/reset', vm=vm)
            return 'reset', current
        target = 'on' if action == 'start' else 'off'
        # Retry a task that lost the config lock race.
        for attempt in range(3):
            # PVE's own shutdown timeout is shorter.
            params = {'timeout': self.power_timeout['shutdown']} if action == 'shutdown' else None
            upid = await self.api('POST', f'status/{action}', params, vm=vm)
            try:
                return await self.wait_power(vm, target, self.power_timeout[action], upid), current
            except TaskFailed as e:
                if "can't lock file" not in str(e) or attempt == 2:
                    raise exc.TargetResourceUnavailable(str(e))
                await asyncio.sleep(2)

    async def wait_power(self, vm, target, timeout, upid=None):
        """Wait for the power state; fail early if the action's task fails."""
        loop = asyncio.get_running_loop()
        deadline = loop.time() + timeout
        while True:
            newstate = await self.get_vm_power(vm)
            if newstate == target:
                return newstate
            if upid:
                host, _ = await self.get_vm(vm)
                task = await self.api('GET', '/api2/json/nodes/{}/tasks/{}/status'.format(
                    host, urlparse.quote(upid, safe='')))
                if task.get('status') == 'stopped' and task.get('exitstatus') != 'OK':
                    raise TaskFailed('PVE task {} failed: {}'.format(
                        upid.split(':')[5] if upid.count(':') > 5 else 'action', task.get('exitstatus')))
            if loop.time() >= deadline:
                raise exc.TargetResourceUnavailable(
                    '{} did not reach power state {} within {} seconds'.format(vm, target, timeout))
            await asyncio.sleep(0.5)

    async def set_vm_bootdev(self, vm, bootdev, persistent=True, bootmode='unspecified'):
        """Set the next boot device; returns True if applied persistently.

        One-time needs the confluent-boot-oneshot hookscript: the order to
        restore goes in the description and the hookscript restores it after
        the next start. It holds until a cold start. Without the hookscript
        the order is applied persistently.
        """
        if bootdev in ('setup', 'floppy', 'http'):
            raise exc.InvalidArgumentException(
                'Proxmox VMs have no {} boot target; use network, hd, cd, usb or default'.format(bootdev))
        if bootdev not in BOOTCLASS:
            raise exc.InvalidArgumentException('Requested boot device {} not supported'.format(bootdev))
        cfg = next_config(await self.api('GET', 'pending', vm=vm))
        current = await self.api('GET', 'config', vm=vm)
        # bootmode is advisory: never change firmware under an installed OS.
        # nodesetboot sends uefi unless -b; the reply reports the actual mode.
        devices = boot_devices(cfg)
        want = BOOTCLASS[bootdev]
        if want is None:
            # Disks first, network last (undoes cd and usb too); unlisted NICs appended.
            disks = [d for d in devices if device_class(d, cfg) == 'disk']
            middle = [d for d in devices if device_class(d, cfg) not in ('disk', 'net')]
            nets = [d for d in devices if device_class(d, cfg) == 'net'] or \
                sorted((k for k in cfg if device_class(k, cfg) == 'net'), key=_devkey)
            front, rest = disks + middle, nets
        else:
            front = [d for d in devices if device_class(d, cfg) == want]
            if not front:
                # Not yet in the order.
                front = sorted((k for k in cfg if device_class(k, cfg) == want), key=_devkey)
            if not front:
                raise exc.InvalidArgumentException('{} has no {} device to boot from'.format(vm, bootdev))
            rest = [d for d in devices if d not in front]
        # Only the chosen class moves.
        neworder = 'order=' + ';'.join(front + rest)
        description = current.get('description') or ''
        marker = ONESHOT_MARKER.search(description)
        oneshot = not persistent and ONESHOT_HOOK in (current.get('hookscript') or '')
        update = {}
        if oneshot:
            if not marker:
                # Keep the original order across repeated one-time requests.
                restore = cfg.get('boot') or 'none'
                update['description'] = (description.rstrip('\n') + '\n' if description else '') + \
                    'confluent-boot-restore: {}\n'.format(restore)
        elif marker:
            # Persistent supersedes a pending restore.
            update['description'] = ONESHOT_MARKER.sub('', description)
        if neworder != cfg.get('boot'):
            update['boot'] = neworder
        if update:
            await self.api('PUT', 'config', update, vm=vm)
        if not persistent and not oneshot:
            log.log({'warning': '{}: one-time boot requested, applied persistently: attach the '
                                '{} hookscript to the VM for one-time boot'.format(vm, ONESHOT_HOOK)})
        return not oneshot


async def prep_proxmox_clients(nodes, configmanager):
    cfginfo = configmanager.get_node_attributes(nodes, ['hardwaremanagement.manager', 'secret.hardwaremanagementuser', 'secret.hardwaremanagementpassword'], decrypt=True)
    clientsbypmx = {}
    clientsbynode = {}
    for node in nodes:
        cfg = cfginfo[node]
        currpmx = cfg['hardwaremanagement.manager']['value']
        if currpmx not in clientsbypmx:
            user = cfg.get('secret.hardwaremanagementuser', {}).get('value', None)
            passwd = cfg.get('secret.hardwaremanagementpassword', {}).get('value', None)
            clientsbypmx[currpmx] = PmxApiClient(currpmx, user, passwd, configmanager, node)
            try:
                await clientsbypmx[currpmx].login()
            except exc.TargetEndpointBadCredentials as e:
                clientsbypmx[currpmx] = e
            except exc.TargetEndpointUnreachable as e:
                clientsbypmx[currpmx] = e
        clientsbynode[node] = clientsbypmx[currpmx]
    return clientsbynode


def _unsupported(node, element):
    return msg.ConfluentNodeError(node, '{} is not supported for Proxmox VMs'.format('/'.join(element)))


async def _per_node(nodes, element, configmanager, handler):
    """Run handler(client, node) per node; errors are reported per node."""
    clientsbynode = await prep_proxmox_clients(nodes, configmanager)
    for node in nodes:
        currclient = clientsbynode[node]
        if isinstance(currclient, Exception):
            yield msg.ConfluentNodeError(node, str(currclient))
            continue
        try:
            await currclient.get_vm(node)
        except Exception as e:
            yield msg.ConfluentNodeError(node, str(e))
            continue
        try:
            async for rsp in handler(currclient, node):
                yield rsp
        except (exc.ConfluentException, TaskFailed) as e:
            yield msg.ConfluentNodeError(node, str(e))


async def _inventory_items(client, node):
    cfg = await client.api('GET', 'config', vm=node)
    host, guest = await client.get_vm(node)
    return vm_inventory(cfg, host, guest.split('/')[-1], await client.get_guest_info(node, cfg))


async def _retrieve_node(client, node, element):
    if element == ['power', 'state']:
        yield msg.PowerState(node, await client.get_vm_powerstate(node))
    elif element == ['boot', 'nextdevice']:
        nextdev, bootmode, persistent = await client.get_vm_bootdev(node)
        yield msg.BootDevice(node, nextdev, bootmode=bootmode, persistent=persistent)
    elif element[:2] == ['inventory', 'hardware'] and len(element) == 3:
        yield msg.ChildCollection('all')
        for item in await _inventory_items(client, node):
            yield msg.ChildCollection(simplify(item['name']))
    elif element[:2] == ['inventory', 'hardware'] and len(element) == 4:
        async for rsp in client.get_vm_inventory(node, element[3]):
            yield rsp
    elif element[:2] == ['inventory', 'firmware']:
        if len(element) < 3 or element[2] not in ('all', 'core', 'adapters', 'disks', 'misc'):
            yield _unsupported(node, element)
            return
        items = await client.get_vm_firmware(node) if element[2] in ('all', 'core') else []
        if len(element) == 3:
            yield msg.ChildCollection('all')
            for item in items:
                for name in item:
                    yield msg.ChildCollection(simplify(name))
            return
        if element[3] != 'all':
            items = [item for item in items if element[3] in [simplify(name) for name in item] + list(item)]
        yield msg.Firmware(items, node)
    elif element == ['health', 'hardware']:
        health, bad = vm_health(await client.get_vm_status(node))
        yield msg.HealthSummary(health, node)
        yield msg.SensorReadings(bad, node)
    elif element[:2] == ['sensors', 'hardware'] and len(element) >= 3:
        if element[2] == 'normalized':
            yield _unsupported(node, element)
            return
        # No temperature, fan, power or energy sensors on a VM.
        readings = vm_sensors(await client.get_vm_status(node)) if element[2] == 'all' else []
        if len(element) == 3:
            yield msg.ChildCollection('all')
            for reading in readings:
                yield msg.ChildCollection(simplify(reading['name']))
            return
        if element[3] != 'all':
            readings = [r for r in readings if simplify(r['name']) == element[3]]
        yield msg.SensorReadings(readings, node)
    elif element == ['events', 'hardware', 'log']:
        yield msg.EventCollection(await client.get_vm_events(node), node)
    elif element == ['identify']:
        yield msg.IdentifyState(node, await client.get_vm_identify(node))
    elif element == ['media', 'current']:
        for media in await client.get_vm_media(node):
            yield msg.Media(node, rawmedia=media)
    elif element[:2] == ['configuration', 'system'] and element[2:] in (['all'], ['advanced']):
        yield msg.ConfigSet(node, await client.get_vm_settings(node))
    elif element[:3] == ['configuration', 'management_controller', 'extended']:
        # Manager, current PVE node and VMID.
        settings = {}
        if element[3:] == ['all']:
            settings = dict((key, {'value': val}) for key, val in (await client.get_vm_location(node)).items())
        yield msg.ConfigSet(node, settings)
    elif element == ['configuration', 'management_controller', 'location']:
        yield msg.KeyValueData(await client.get_vm_location(node), node)
    elif element == ['configuration', 'management_controller', 'net_interfaces']:
        yield msg.ChildCollection('management')
    elif element == ['configuration', 'management_controller', 'net_interfaces', 'management']:
        # No management controller.
        yield msg.NetworkConfiguration(name=node)
    elif element == ['configuration', 'management_controller', 'hostname']:
        yield msg.Hostname(node, None)
    elif element[:2] == ['configuration', 'storage'] and len(element) >= 3:
        if element[2] not in ('all', 'disks'):
            return
        cfg = await client.api('GET', 'config', vm=node)
        disks = disk_drives(cfg)
        if element[2] == 'disks' and len(element) == 3:
            for key in disks:
                yield msg.ChildCollection(key)
            return
        if element[2] == 'disks':
            disks = [key for key in disks if key == element[3]]
        for key in disks:
            volume, opts = drive_options(cfg[key])
            yield msg.Disk(node, label=key, description='{} ({})'.format(volume, opts.get('size', 'size unknown')),
                           diskid=key, state='online', serial=opts.get('serial'))
    elif element == ['console', 'ikvm_methods']:
        yield msg.KeyValueData({'ikvm_methods': ['vnc']}, node)
    elif element == ['console', 'ikvm_screenshot']:
        # good background for the webui, and kitty
        yield msg.ConfluentNodeError(node, "vnc available, screenshot not available")
    else:
        yield _unsupported(node, element)


_TRANSFERS = (('media/uploads', 'mediaupload'), ('support/servicedata', 'ffdc'))


async def retrieve(nodes, element, configmanager, inputdata):
    for prefix, kind in _TRANSFERS:
        if '/'.join(element).startswith(prefix):
            for ret in firmwaremanager.list_updates(nodes, configmanager.tenant, element, kind):
                yield ret
            return
    async for rsp in _per_node(nodes, element, configmanager,
                               lambda client, node: _retrieve_node(client, node, element)):
        yield rsp


async def _update_node(client, node, element, inputdata):
    if element == ['power', 'state']:
        newstate, oldstate = await client.set_vm_power(node, inputdata.powerstate(node))
        yield msg.PowerState(node, newstate, oldstate)
    elif element == ['boot', 'nextdevice']:
        applied_persistent = await client.set_vm_bootdev(
            node, inputdata.bootdevice(node), persistent=inputdata.persistent(node),
            bootmode=inputdata.bootmode(node))
        nextdev, bootmode, _ = await client.get_vm_bootdev(node)
        # Persistent if one-time was requested without the hookscript.
        yield msg.BootDevice(node, nextdev, bootmode=bootmode, persistent=applied_persistent)
    elif element == ['identify']:
        state = inputdata.inputbynode[node]
        await client.set_vm_identify(node, state)
        yield msg.IdentifyState(node, state)
    elif element == ['_enclosure', 'reseat_bay']:
        await client.reseat_vm(node)
        yield msg.ReseatResult(node, 'success')
    elif element == ['media', 'attach']:
        await client.attach_media(node, inputdata.nodefile(node))
    elif element == ['media', 'detach']:
        await client.detach_media(node)
    elif element[:2] == ['configuration', 'system'] and element[2:] in (['all'], ['advanced']):
        await client.set_vm_settings(node, inputdata.get_attributes(node))
    elif element == ['configuration', 'system', 'clear']:
        yield msg.ConfluentNodeError(node, 'A Proxmox VM has no firmware defaults to restore; set the '
                                           'settings to an empty value to return them to the PVE default')
    elif element[:2] == ['configuration', 'management_controller']:
        yield msg.ConfluentNodeError(node, 'A Proxmox VM has no management controller to configure; it is '
                                           'managed through Proxmox server {}'.format(client.server))
    else:
        yield _unsupported(node, element)


async def update(nodes, element, configmanager, inputdata):
    if element == ['console', 'ikvm']:
        clientsbynode = await prep_proxmox_clients(nodes, configmanager)
        for node in nodes:
            currclient = clientsbynode[node]
            if isinstance(currclient, Exception):
                yield msg.ConfluentNodeError(node, str(currclient))
                continue
            if currclient.token:
                # vinz forwards a cookie; a token needs a header.
                yield msg.ConfluentNodeError(node, 'VNC needs a Proxmox user with a password; '
                                                   'API tokens cannot be passed to the VNC proxy')
                return
            try:
                url = await vinzmanager.get_url(node, inputdata, nodeparmcallback=KvmConnHandler(currclient, node).connect)
            except Exception as e:
                print(repr(e))
                return
            yield msg.ChildCollection(url)
            return
        return
    async for rsp in _per_node(nodes, element, configmanager,
                               lambda client, node: _update_node(client, node, element, inputdata)):
        yield rsp


async def create(nodes, element, configmanager, inputdata):
    clientsbynode = await prep_proxmox_clients(nodes, configmanager)
    for node in nodes:
        if isinstance(clientsbynode[node], Exception):
            yield msg.ConfluentNodeError(node, str(clientsbynode[node]))
            continue
        try:
            await clientsbynode[node].get_vm(node)
        except Exception as e:
            yield msg.ConfluentNodeError(node, str(e))
            continue
        if element == ['media', 'uploads']:
            upload = firmwaremanager.Updater(
                node, functools.partial(clientsbynode[node].upload_media, node),
                inputdata.nodefile(node), configmanager.tenant, type='mediaupload',
                configmanager=configmanager)
            yield msg.CreatedResource('nodes/{0}/media/uploads/{1}'.format(node, upload.name))
            continue
        if element == ['support', 'servicedata']:
            download = firmwaremanager.Updater(
                node, functools.partial(clientsbynode[node].collect_servicedata, node),
                inputdata.nodefile(node), configmanager.tenant, type='ffdc',
                owner=getattr(configmanager, 'current_user', None))
            yield msg.CreatedResource('nodes/{0}/support/servicedata/{1}'.format(node, download.name))
            continue
        if element == ['console', 'ikvm']:
            currclient = clientsbynode[node]
            if currclient.token:
                # vinz forwards a cookie; a token needs a header.
                yield msg.ConfluentNodeError(node, 'VNC needs a Proxmox user with a password; '
                                                   'API tokens cannot be passed to the VNC proxy')
                return
            try:
                url = await vinzmanager.get_url(node, inputdata, nodeparmcallback=KvmConnHandler(currclient, node).connect)
            except Exception as e:
                print(repr(e))
                return
            yield msg.ChildCollection(url)
            return
        if element[:1] not in (['_console'], ['console']):
            yield _unsupported(node, element)
            continue
        serialdata = await clientsbynode[node].get_vm_serial(node)
        yield PmxConsole(serialdata, node, configmanager, clientsbynode[node])
        return


async def delete(nodes, element, configmanager, inputdata):
    for prefix, kind in _TRANSFERS:
        if '/'.join(element).startswith(prefix):
            for ret in firmwaremanager.remove_updates(nodes, configmanager.tenant, element, type=kind):
                yield ret
            return
    for node in nodes:
        if element == ['events', 'hardware', 'log']:
            yield msg.ConfluentNodeError(node, 'The event log of a Proxmox VM is its PVE task history, '
                                               'which cannot be cleared from confluent')
        else:
            yield _unsupported(node, element)


async def _selftest():
    import sys
    import os
    myuser = os.environ['PMXUSER']
    mypass = os.environ['PMXPASS']
    vc = PmxApiClient(sys.argv[1], myuser, mypass, None)
    vm = sys.argv[2]
    if sys.argv[3] == 'setboot':
        await vc.set_vm_bootdev(vm, sys.argv[4])
        await vc.get_vm_bootdev(vm)
    elif sys.argv[3] == 'power':
        await vc.set_vm_power(vm, sys.argv[4])
    elif sys.argv[3] == 'getinfo':
        print(repr([datum.kvpairs async for datum in vc.get_vm_inventory(vm)]))
        print("Bootdev: " + (await vc.get_vm_bootdev(vm))[0])
        print("Power: " + await vc.get_vm_power(vm))
        #print("Serial: " + repr(vc.get_vm_serial(vm)))


if __name__ == '__main__':
    asyncio.run(_selftest())
