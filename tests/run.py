#!/usr/bin/env python3
"""Runs seacomb's tests for each supported Linux target under QEMU.

Usage: python3 tests/run.py [all|x86_64|i686|aarch64|armv7l]
"""

import argparse
import hashlib
import json
import os
import platform
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import NamedTuple

ROOT = Path(__file__).resolve().parent.parent
BUILD_DIR = ROOT / "target/cross-tests"
KERNEL_DIR = ROOT / "target/test-kernels"
KERNEL_URL = "https://dl-cdn.alpinelinux.org/alpine/v3.24/releases"


class Machine(NamedTuple):
    """A QEMU machine and the Alpine kernel it boots."""
    kernel: str
    sha256: str
    qemu: list
    console: str


# A replacement kernel needs SECCOMP_FILTER, BLK_DEV_INITRD, and a built-in serial console
# (plus IA32_EMULATION on x86_64); check the config- file next to it in the release.
MACHINES = {
    "x86_64": Machine(
        kernel="x86_64/netboot-3.24.2/vmlinuz-virt",
        sha256="40f620bc8c93d952e57dd8dfc0f94fca1759d192a4fc4a260705d50ca378559c",
        qemu=["qemu-system-x86_64", "-cpu", "max"],
        console="ttyS0",
    ),
    "aarch64": Machine(
        kernel="aarch64/netboot-3.24.2/vmlinuz-virt",
        sha256="e45e1f6083d1ed45db6647b422e32b6ae6dc54de7b8190b7b97744fb293412e3",
        qemu=["qemu-system-aarch64", "-M", "virt", "-cpu", "max"],
        console="ttyAMA0",
    ),
    "armv7l": Machine(
        kernel="armv7/netboot-3.24.2/vmlinuz-lts",
        sha256="79e56b07cbeb6d658e03be69985cac68e73d018248606505d49457cb59420e4d",
        qemu=["qemu-system-arm", "-M", "virt", "-cpu", "cortex-a15"],
        console="ttyAMA0",
    ),
}

# Each architecture's Rust target and the machine that runs it.
# musl targets link statically with the toolchain's rust-lld, so no cross linker is needed.
TARGETS = {
    "x86_64": ("x86_64-unknown-linux-musl", "x86_64"),
    "i686": ("i686-unknown-linux-musl", "x86_64"),
    "aarch64": ("aarch64-unknown-linux-musl", "aarch64"),
    "armv7l": ("armv7-unknown-linux-musleabihf", "armv7l"),
}

# `do_exit` in `kernel/exit.c` panics with this, then dumps registers, when /init exits.
INIT_EXIT = re.compile(r"Attempted to kill init! exitcode=0x([0-9a-f]+)")


def run(*args):
    """Runs a command from the repository root."""
    subprocess.run(args, cwd=ROOT, check=True)


def test(targets):
    """Runs every test for each of `targets` in one cargo run, which boots each binary through `--boot`."""
    flags = []
    for target, machine_arch in targets:
        runner = json.dumps([sys.executable, str(Path(__file__).resolve()), "--boot", machine_arch])
        flags += ["--target", target,
                  "--config", f'target.{target}.linker="rust-lld"',
                  "--config", f"target.{target}.runner={runner}"]
    run("cargo", "test", "--locked", *flags, "--target-dir", str(BUILD_DIR))


def fetch_kernel(machine):
    """Returns the cached kernel for `machine`, downloading and checking it first if needed."""
    path = KERNEL_DIR / machine.kernel
    if not path.exists():
        url = f"{KERNEL_URL}/{machine.kernel}"
        print(f"Downloading {url}", flush=True)
        path.parent.mkdir(parents=True, exist_ok=True)
        partial = path.with_name(path.name + ".part")
        run("curl", "-fsSL", "--retry", "3", "-o", str(partial), url)
        if hashlib.sha256(partial.read_bytes()).hexdigest() != machine.sha256:
            sys.exit(f"Checksum mismatch for {url}.")
        partial.rename(path)
    return path


def write_initramfs(binary, path):
    """Writes a cpio archive whose only file is `binary`, installed as /init."""
    # The newc format in `Documentation/driver-api/early-userspace/buffer-format.rst`:
    # per file, "070701", 13 fields as 8 hex digits, the NUL-terminated name, and the
    # data, with the name and the data each padded to 4 bytes. "TRAILER!!!" ends it.
    entries = [("init", 0o100755, Path(binary).read_bytes()), ("TRAILER!!!", 0, b"")]
    archive = bytearray()
    for ino, (name, mode, data) in enumerate(entries, start=1):
        # ino, mode, uid, gid, nlink, mtime, filesize, maj, min, rmaj, rmin, namesize, chksum
        fields = [ino, mode, 0, 0, 1, 0, len(data), 0, 0, 0, 0, len(name) + 1, 0]
        archive += b"070701" + b"".join(b"%08x" % f for f in fields)
        archive += name.encode() + b"\0"
        archive += b"\0" * (-len(archive) % 4) + data
        archive += b"\0" * (-len(archive) % 4)
    path.write_bytes(archive)


def accelerator(arch):
    """Returns QEMU's -accel flag, using the host hypervisor when `arch` is native and it has one."""
    host = {"arm64": "aarch64"}.get(platform.machine(), platform.machine())
    if arch == host and platform.system() == "Darwin":
        # QEMU aborts rather than trying the next -accel when HVF is missing, as on GitHub's
        # macOS runners, where this sysctl is 0 or absent.
        probe = subprocess.run(["sysctl", "-n", "kern.hv_support"], capture_output=True, text=True)
        if probe.stdout.strip() == "1":
            return ["-accel", "hvf"]
    if arch == host and platform.system() == "Linux" and os.access("/dev/kvm", os.R_OK | os.W_OK):
        return ["-accel", "kvm"]
    return ["-accel", "tcg"]


def boot(arch, binary, scratch):
    """Boots `binary` as /init, echoes its output, and returns its wait status or None."""
    machine = MACHINES[arch]
    initrd = scratch / f"{Path(binary).name}.cpio"
    write_initramfs(binary, initrd)
    command = [
        *machine.qemu, *accelerator(arch), "-smp", "1",
        "-nodefaults", "-display", "none", "-serial", "stdio",
        "-kernel", str(fetch_kernel(machine)), "-initrd", str(initrd),
        # Log only emergencies, and reboot at once on a panic, which
        # -no-reboot turns into QEMU exiting.
        "-append", f"console={machine.console} loglevel=1 panic=-1", "-no-reboot",
    ]
    status = None
    with subprocess.Popen(command, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                          text=True, errors="replace") as qemu:
        for line in qemu.stdout:
            if match := INIT_EXIT.search(line):
                status = int(match.group(1), 16)
            elif status is None:
                print(line, end="", flush=True)
    if qemu.returncode != 0:
        raise subprocess.CalledProcessError(qemu.returncode, command)
    return status


def exit_code(arch, binary, scratch):
    """Boots `binary` on `arch` and returns its exit code, exiting on a signal or a lost status."""
    status = boot(arch, binary, scratch)
    if status is None:
        sys.exit(f"The {arch} kernel stopped before {binary} exited.")
    code = os.waitstatus_to_exitcode(status)
    if code < 0:
        sys.exit(f"{binary} on {arch} was killed by signal {-code}.")
    return code


def main():
    parser = argparse.ArgumentParser(description="Build tests on the host and run them in QEMU.")
    parser.add_argument("arch", nargs="?", default="all", choices=["all", *TARGETS])
    parser.add_argument("--boot", nargs=2, metavar=("MACHINE", "BINARY"),
                        help="boot one binary and exit with its status, as cargo's target runner")
    args = parser.parse_args()

    if args.boot:
        machine_arch, binary = args.boot
        with tempfile.TemporaryDirectory() as scratch:
            sys.exit(exit_code(machine_arch, binary, Path(scratch)))

    test([TARGETS[arch] for arch in (TARGETS if args.arch == "all" else [args.arch])])


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        sys.exit(error.returncode)
