use crate::qemu::exit_qemu;
use crate::serial::SerialPort;
use core::fmt::Write;
use core::panic::PanicInfo;

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    let mut sw = SerialPort::new_for_com1();
    writeln!(sw, "PANIC: {info:?}").unwrap();
    exit_qemu(crate::qemu::QemuExitCode::Fail);
}
