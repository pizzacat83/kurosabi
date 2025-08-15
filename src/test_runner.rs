use core::{any::type_name, fmt::Write, panic::PanicInfo};

use crate::{
    qemu::{exit_qemu, QemuExitCode},
    serial::SerialPort,
};

pub fn test_runner(tests: &[&dyn Testable]) -> ! {
    let mut sw = SerialPort::new_for_com1();
    writeln!(sw, "Running {} tests...", tests.len()).unwrap();
    for test in tests {
        test.run(&mut sw);
    }
    writeln!(sw, "Completed {} tests!", tests.len()).unwrap();

    exit_qemu(QemuExitCode::Success);
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    let mut sw = SerialPort::new_for_com1();
    write!(sw, "PANIC during test: ").unwrap();
    if let Some(location) = info.location() {
        write!(
            sw,
            "{}:{}:{} ",
            location.file(),
            location.line(),
            location.column()
        )
        .unwrap();
    }
    writeln!(sw, "{info:?}").unwrap();
    exit_qemu(QemuExitCode::Fail);
}

pub trait Testable {
    fn run(&self, writer: &mut SerialPort);
}

impl<T> Testable for T
where
    T: Fn(),
{
    fn run(&self, writer: &mut SerialPort) {
        writeln!(writer, "[RUNNING] >>> {}", type_name::<T>()).unwrap();
        self();
        writeln!(writer, "[PASS   ] >>> {}", type_name::<T>()).unwrap();
    }
}
