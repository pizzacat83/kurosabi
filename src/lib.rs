#![no_std]
#![feature(offset_of)]
#![feature(custom_test_frameworks)]
#![test_runner(crate::test_runner::test_runner)]
#![reexport_test_harness_main = "run_unit_tests"]
#![no_main]

pub mod graphics;
pub mod print;
pub mod print_ruststd;
pub mod qemu;
pub mod result;
pub mod serial;
pub mod uefi;
pub mod x64;

#[cfg(not(test))]
pub mod panic;
#[cfg(test)]
pub mod test_runner;

#[cfg(test)]
#[no_mangle]
pub fn efi_main() {
    run_unit_tests()
}
