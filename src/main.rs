#![no_std]
#![no_main]
#![feature(offset_of)]

use wasabi::graphics::{fill_rect, Bitmap};
use wasabi::init::{init_basic_runtime, init_paging};
use wasabi::print::hexdump;
use wasabi::uefi::{
    exit_from_efi_boot_services, handle_loaded_image_protocol, init_vram, EfiHandle, EfiMemoryType,
    EfiSystemTable, MemoryMapHolder,
};
use wasabi::x86::{hlt, init_exceptions, trigger_debug_interrupt};
use wasabi::{executor, info, println};

#[no_mangle]
fn efi_main(image_handle: EfiHandle, efi_system_table: &EfiSystemTable) {
    let mut vram = init_vram(efi_system_table).expect("init_vram failed");

    let vw = vram.width();
    let vh = vram.height();

    fill_rect(&mut vram, 0x000000, 0, 0, vw, vh).expect("fill rect failed");

    let loaded_image = handle_loaded_image_protocol(image_handle, efi_system_table)
        .expect("failed to handle loaded image protocol");
    println!("image_base: {:#018x}", loaded_image.image_base);
    println!("image_size: {:#018x}", loaded_image.image_size);

    let memory_map = init_basic_runtime(image_handle, efi_system_table);

    // let mut total_memory_pages = 0;
    // for e in memory_map.iter() {
    //     if e.memory_type() != EfiMemoryType::CONVENTIONAL_MEMORY {
    //         continue;
    //     }
    //     println!("{e:?}");
    //     total_memory_pages += e.number_of_pages();
    // }

    // let total_memory_size_mib = total_memory_pages * 4096 / 1024 / 1024;
    // println!("Total: {total_memory_pages} pages = {total_memory_size_mib} MiB");

    println!("Hello from the world without boot service!");

    // let cr3 = wasabi::x86::read_cr3();
    // println!("{cr3:#p}");
    // hexdump(unsafe { &*cr3 });
    // let t = Some(unsafe { &*cr3 });
    // println!("{t:?}");
    // let t = t.and_then(|t| t.next_level(0));
    // println!("{t:?}");
    // let t = t.and_then(|t| t.next_level(0));
    // println!("{t:?}");
    // let t = t.and_then(|t| t.next_level(0));
    // println!("{t:?}");

    println!("Initializing IDT...");
    // TODO: Is the reason of unmeaningful assignment here to prevent drop?
    let (_gdt, _idt) = init_exceptions();

    println!("Triggering exception...");
    trigger_debug_interrupt();
    println!("Resuming after exception!");

    init_paging(&memory_map);

    executor::demo();

    loop {
        hlt();
    }
}
