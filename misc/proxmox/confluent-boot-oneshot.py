#!/usr/bin/python3
# Proxmox VE hookscript: makes a confluent `nodesetboot` without -p one-time.
# Opt-in per VM; without it a one-time request is applied persistently.
#
# Install on every PVE node and attach to the VMs that want it:
#
#   install -m 0755 confluent-boot-oneshot.py /var/lib/vz/snippets/
#   qm set <vmid> --hookscript local:snippets/confluent-boot-oneshot.py
#
# confluent records the order to restore as "confluent-boot-restore: <order|none>"
# in the VM description; after the next start this restores it and drops the line.
# The restored order applies from the next cold start.
import json
import os
import re
import socket
import subprocess
import sys
import time

CONF = '/etc/pve/qemu-server/{}.conf'
# In the conf, description lines are '#' comments with ':' percent-encoded.
PENDING = re.compile(r'^#confluent-boot-restore(?::|%3A) ', re.I | re.M)
MARKER = re.compile(r'^confluent-boot-restore: *(\S*).*(?:\n|$)', re.M)
TRIES = 30
DELAY = 2


def pending(vmid):
    try:
        with open(CONF.format(vmid)) as conf:
            return PENDING.search(conf.read()) is not None
    except OSError:
        return False


def config(vmid):
    node = socket.gethostname().split('.')[0]
    out = subprocess.run(['pvesh', 'get', '/nodes/{}/qemu/{}/config'.format(node, vmid),
                          '--output-format', 'json'], check=True, capture_output=True, text=True).stdout
    return json.loads(out)


def restore(vmid):
    for _ in range(TRIES):
        description = config(vmid).get('description') or ''
        marker = MARKER.search(description)
        if not marker:
            return
        cmd = ['qm', 'set', str(vmid), '--description', MARKER.sub('', description)]
        if marker.group(1) in ('', 'none'):
            cmd += ['--delete', 'boot']
        else:
            cmd += ['--boot', marker.group(1)]
        # Fails while another task holds the config lock.
        if subprocess.run(cmd).returncode == 0:
            return
        time.sleep(DELAY)
    sys.exit('confluent-boot-oneshot: could not restore the boot order of {}'.format(vmid))


def main(argv):
    if len(argv) < 3:
        return
    vmid, phase = argv[1], argv[2]
    if phase == 'post-start':
        # Runs inside the start task, which holds the config lock: only look,
        # and restore from a unit of its own. exec, not fork: a child would
        # inherit the task's lock and output pipe.
        if pending(vmid):
            os.execvp('systemd-run', ['systemd-run', '--no-block', '--collect', '--quiet',
                                      '--unit=confluent-boot-restore-{}-{}'.format(vmid, int(time.time())),
                                      sys.executable, os.path.abspath(argv[0]), vmid, 'confluent-restore'])
    elif phase == 'confluent-restore':
        restore(vmid)


if __name__ == '__main__':
    main(sys.argv)
