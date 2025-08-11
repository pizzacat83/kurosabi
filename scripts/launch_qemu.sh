#!/bin/bash -eu
set -eu

# change to project root
cd "$(dirname "$0")/.."

# cargo run passes the path to EFI relative to project root
PATH_TO_EFI="$1"
rm -rf mnt
mkdir -p mnt/EFI/BOOT
mkdir -p log
cp "$PATH_TO_EFI" mnt/EFI/BOOT/BOOTX64.EFI

QEMU_OPTIONS=""
if rg -q '/debug/deps/[^/]+\.efi$' <<< "$PATH_TO_EFI"; then
    # seems like `cargo test`
    QEMU_OPTIONS="-display none"
fi

set +e

qemu-system-x86_64 \
    -m 4G \
    -bios third_party/ovmf/RELEASEX64_OVMF.fd \
    -drive format=raw,file=fat:rw:mnt \
    -chardev stdio,id=char_com1,mux=on,logfile=log/com1.txt \
    -serial chardev:char_com1 \
    -device isa-debug-exit,iobase=0xf4,iosize=0x01 \
    $QEMU_OPTIONS

RETCODE=$?

set -e

if [ "$RETCODE" -eq 0 ]; then
    exit 0
elif [ $RETCODE -eq 3 ]; then
    printf "\nPASS\n"
    exit 0
else
    printf "\nFAIL: QEMU returned $RETCODE\n"
    exit 1
fi
