use crate::x64::{hlt, write_io_port_u8};

/// Qemu's exit code will be `(val << 1) | 1` ([source](https://github.com/qemu/qemu/blob/a74434580e1051bff12ab5eee5586058295c497f/hw/misc/debugexit.c#L37))
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QemuExitCode {
    Success = 0x1, // Qemu will exit with status 3
    Fail = 0x2,    // Qemu will exit with status 5
}

pub fn exit_qemu(exit_code: QemuExitCode) -> ! {
    write_io_port_u8(0xf4, exit_code as u8);
    loop {
        hlt();
    }
}
