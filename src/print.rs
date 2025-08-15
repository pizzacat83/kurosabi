use core::{fmt, mem::size_of_val, slice};

use crate::serial::SerialPort;

pub fn global_print(args: fmt::Arguments) {
    let mut writer = SerialPort::default();
    fmt::write(&mut writer, args).unwrap();
}

#[macro_export]
macro_rules! print {
    ($($arg:tt)*) => ($crate::print::global_print(format_args!($($arg)*)));
}

#[macro_export]
macro_rules! println {
    () => ($crate::print!("\n"));
    ($($arg:tt)*) => ($crate::print!("{}\n", format_args!($($arg)*)));
}

#[macro_export]
macro_rules! info {
    ($($arg:tt)*) => ($crate::print!("[INFO] {}:{:<3}: {}\n", file!(), line!(), format_args!($($arg)*)));
}

#[macro_export]
macro_rules! warn {
    ($($arg:tt)*) => ($crate::print!("[WARN] {}:{:<3}: {}\n", file!(), line!(), format_args!($($arg)*)));
}

#[macro_export]
macro_rules! error {
    ($($arg:tt)*) => ($crate::print!("[ERROR] {}:{:<3}: {}\n", file!(), line!(), format_args!($($arg)*)));
}

pub fn hexdump<T: Sized>(data: &T) {
    hexdump_bytes(unsafe {
        // TODO: safety?
        slice::from_raw_parts(data as *const T as *const u8, size_of_val(data))
    });
}

pub fn hexdump_bytes(bytes: &[u8]) {
    const LINE_WIDTH: usize = 16;
    for (line, chunk) in bytes.chunks(LINE_WIDTH).enumerate() {
        let offset = line * LINE_WIDTH;
        print!("{offset:08X}: ");
        for v in chunk {
            print!("{:02X} ", v);
        }

        print!("|");
        print!(" ascii coming soon ");
        println!("|");
    }
}
