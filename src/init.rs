extern crate alloc;

use alloc::boxed::Box;
use core::cmp::max;

use crate::{
    allocator, info,
    uefi::{exit_from_efi_boot_services, EfiHandle, EfiSystemTable, MemoryMapHolder},
    x86::{write_cr3, PageAttr, PAGE_SIZE, PML4},
};

pub fn init_basic_runtime(
    image_handle: EfiHandle,
    efi_system_table: &EfiSystemTable,
) -> MemoryMapHolder {
    let mut memory_map = MemoryMapHolder::default();

    exit_from_efi_boot_services(image_handle, efi_system_table, &mut memory_map)
        .expect("failed to exit boot services");

    allocator::init_with_mmap(&memory_map);

    memory_map
}

pub fn init_paging(memory_map: &MemoryMapHolder) {
    let mut end_of_mem = 0x1_0000_0000u64;
    for e in memory_map.iter() {
        use crate::uefi::EfiMemoryType::*;
        match e.memory_type() {
            CONVENTIONAL_MEMORY | LOADER_CODE | LOADER_DATA => {
                end_of_mem = max(
                    end_of_mem,
                    // TODO: refactor?
                    (usize::from(e.physical_start()) as u64)
                        + e.number_of_pages() * (PAGE_SIZE as u64),
                );
            }
            _ => (),
        }
    }

    info!(
        "Mapping virtual {:#018x}:{:#018x} to {:#018x}",
        0, end_of_mem, 0
    );

    // TODO: refactor into a single factory?
    let mut table = PML4::new();
    table
        .create_mapping(0, end_of_mem, 0, PageAttr::ReadWriteKernel)
        .expect("Failed to create initial page mapping");

    table
        .identity_mapping_sanity_check(0, end_of_mem, PageAttr::ReadWriteKernel)
        .expect("sanity check failed");
    unsafe { write_cr3(Box::into_raw(table)) }
}
