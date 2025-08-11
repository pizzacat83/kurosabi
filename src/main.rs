#![no_std]
#![no_main]
#![feature(offset_of)]

use wasabi::graphics::{fill_rect, Bitmap};
use wasabi::println;
use wasabi::uefi::{
    exit_from_efi_boot_services, init_vram, EfiHandle, EfiMemoryType, EfiSystemTable,
    MemoryMapHolder,
};
use wasabi::x64::hlt;

#[no_mangle]
fn efi_main(image_handle: EfiHandle, efi_system_table: &EfiSystemTable) {
    let mut vram = init_vram(efi_system_table).expect("init_vram failed");

    let vw = vram.width();
    let vh = vram.height();

    fill_rect(&mut vram, 0x000000, 0, 0, vw, vh).expect("fill rect failed");

    let mut memory_map = MemoryMapHolder::default();

    efi_system_table
        .boot_services
        .get_memory_map(&mut memory_map)
        .expect("failed to get memory map");

    let mut total_memory_pages = 0;
    for e in memory_map.iter() {
        if e.memory_type() != EfiMemoryType::CONVENTIONAL_MEMORY {
            continue;
        }
        println!("{e:?}");
        total_memory_pages += e.number_of_pages();
    }

    let total_memory_size_mib = total_memory_pages * 4096 / 1024 / 1024;
    println!("Total: {total_memory_pages} pages = {total_memory_size_mib} MiB");

    exit_from_efi_boot_services(image_handle, efi_system_table, &mut memory_map)
        .expect("failed to exit boot services");

    println!("Hello from the world without boot service!");

    loop {
        hlt();
    }
}
