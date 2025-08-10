#!/bin/bash -eu
set -eu

# change to project root
cd "$(dirname "$0")/.."

# cargo run passes the path to EFI relative to project root
PATH_TO_EFI="$1"
rm -rf mnt
mkdir -p mnt/EFI/BOOT
cp "$PATH_TO_EFI" mnt/EFI/BOOT/BOOTX64.EFI

qemu-system-x86_64 \
    -m 4G \
    -bios third_party/ovmf/RELEASEX64_OVMF.fd \
    -drive format=raw,file=fat:rw:mnt \
    -device isa-debug-exit,iobase=0xf4,iosize=0x01
