use crate::{
    allocator,
    uefi::{exit_from_efi_boot_services, EfiHandle, EfiSystemTable, MemoryMapHolder},
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
