#![no_std]
#![feature(offset_of)]
#![feature(custom_test_frameworks)]
#![test_runner(crate::test_runner::test_runner)]
#![reexport_test_harness_main = "run_unit_tests"]
#![no_main]

pub mod allocator;
pub mod graphics;
pub mod init;
pub mod print;
pub mod print_ruststd;
pub mod qemu;
pub mod result;
pub mod serial;
pub mod uefi;
pub mod x86;

#[cfg(not(test))]
pub mod panic;
#[cfg(test)]
pub mod test_runner;

#[cfg(test)]
#[no_mangle]
pub fn efi_main(image_handle: uefi::EfiHandle, efi_system_table: &uefi::EfiSystemTable) {
    init::init_basic_runtime(image_handle, efi_system_table);

    run_unit_tests()
}
