#![no_std]
#![no_main]
#![feature(offset_of)]

use core::arch::asm;
use core::{
    mem::{offset_of, size_of},
    panic::PanicInfo,
    ptr::null_mut,
    slice,
};

#[no_mangle]
fn efi_main(_image_handle: EfiHandle, efi_system_table: &EfiSystemTable) {
    let efi_graphics_output_protocol = locate_graphic_protocol(efi_system_table).unwrap();
    let vram_addr = efi_graphics_output_protocol.mode.frame_buffer_base;
    let vram_byte_size = efi_graphics_output_protocol.mode.frame_buffer_size;
    let vram = unsafe {
        slice::from_raw_parts_mut(vram_addr as *mut u32, vram_byte_size / size_of::<u32>())
    };
    for e in vram {
        *e = 0xffffff;
    }

    // println!("Hello, world!");
    loop {
        hlt();
    }
}

fn locate_graphic_protocol<'a>(
    efi_system_table: &EfiSystemTable,
) -> Result<&'a EfiGraphicsOutputProtocol<'a>> {
    let mut graphic_output_protocol: *mut EfiGraphicsOutputProtocol = null_mut();
    let status = (efi_system_table.boot_services.locate_protocol)(
        &EFI_GRAPHICS_OUTPUT_PROTOCOL_GUID,
        null_mut(),
        &mut graphic_output_protocol as *mut *mut EfiGraphicsOutputProtocol as *mut *mut EfiVoid,
    );
    if status != EfiStatus::Success {
        return Err("Failed to locate graphics output protocol");
    }

    Ok(unsafe { &*graphic_output_protocol })
}

/// https://uefi.org/specs/UEFI/2.10/04_EFI_System_Table.html#id6
#[repr(C)]
struct EfiSystemTable {
    _reserved0: [u64; 12],
    pub boot_services: &'static EfiBootServicesTable,
}
const _: () = assert!(offset_of!(EfiSystemTable, boot_services) == 96);

/// https://uefi.org/specs/UEFI/2.10/04_EFI_System_Table.html#efi-boot-services-table
#[repr(C)]
struct EfiBootServicesTable {
    _reserved0: [u64; 40],
    // https://uefi.org/specs/UEFI/2.11/07_Services_Boot_Services.html#efi-boot-services-locateprotocol
    locate_protocol: extern "win64" fn(
        protocol: *const EfiGuid,
        registration: *const EfiVoid,
        interface: *mut *mut EfiVoid,
    ) -> EfiStatus,
}

const _: () = assert!(offset_of!(EfiBootServicesTable, locate_protocol) == 320);

/// https://uefi.org/specs/UEFI/2.11/12_Protocols_Console_Support.html#efi-graphics-output-protocol
const EFI_GRAPHICS_OUTPUT_PROTOCOL_GUID: EfiGuid = EfiGuid {
    data0: 0x9042a9de,
    data1: 0x23dc,
    data2: 0x4a38,
    data3: [0x96, 0xfb, 0x7a, 0xde, 0xd0, 0x80, 0x51, 0x6a],
};

/// https://uefi.org/specs/UEFI/2.11/12_Protocols_Console_Support.html#efi-graphics-output-protocol
#[repr(C)]
#[derive(Debug)]
struct EfiGraphicsOutputProtocol<'a> {
    reserved: [u64; 3],
    pub mode: &'a EfiGraphicsOutputProtocolMode<'a>,
}

/// https://uefi.org/specs/UEFI/2.11/12_Protocols_Console_Support.html#:~:text=FrameBufferSize%3B%0A%7D-,EFI_GRAPHICS_OUTPUT_PROTOCOL_MODE,-%3B
#[repr(C)]
#[derive(Debug)]
struct EfiGraphicsOutputProtocolMode<'a> {
    pub max_mode: u32,
    pub mode: u32,
    pub info: &'a EfiGraphicsOutputProtocolPixelInfo,
    pub size_of_info: u64,
    pub frame_buffer_base: usize,
    pub frame_buffer_size: usize,
}

/// https://uefi.org/specs/UEFI/2.11/12_Protocols_Console_Support.html#:~:text=PixelsPerScanLine%3B%0A%7D-,EFI_GRAPHICS_OUTPUT_MODE_INFORMATION,-%3B
#[repr(C)]
#[derive(Debug)]
struct EfiGraphicsOutputProtocolPixelInfo {
    version: u32,
    pub horizontal_resolution: u32,
    pub vertical_resolution: u32,
    _padding0: [u32; 5],
    pub pixels_per_scan_line: u32,
}

const _: () = assert!(size_of::<EfiGraphicsOutputProtocolPixelInfo>() == 36);

/// https://uefi.org/specs/UEFI/2.11/Apx_A_GUID_and_Time_Formats.html#efi-guid-format-apxa-guid-and-time-formats
#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct EfiGuid {
    pub data0: u32,
    pub data1: u16,
    pub data2: u16,
    pub data3: [u8; 8],
}

/// https://uefi.org/specs/UEFI/2.10/Apx_D_Status_Codes.html
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
#[must_use]
#[repr(u64)]
enum EfiStatus {
    Success = 0,
}

/// https://uefi.org/specs/UEFI/2.10/02_Overview.html#:~:text=code.%20Type%20UINTN.-,EFI_HANDLE,-A%20collection%20of
struct EfiHandle(usize);

/// https://uefi.org/specs/UEFI/2.11/02_Overview.html
struct EfiVoid();

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}

type Result<T> = core::result::Result<T, &'static str>;

pub fn hlt() {
    unsafe { asm!("hlt") }
}
