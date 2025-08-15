use core::{
    mem::{offset_of, size_of},
    ptr::null_mut,
};

use crate::{graphics::Bitmap, info, result::Result, warn};

pub fn init_vram(efi_system_table: &EfiSystemTable) -> Result<VramBufferInfo> {
    let gp = locate_graphic_protocol(efi_system_table)?;

    Ok(VramBufferInfo {
        buf: gp.mode.frame_buffer_base as *mut u8,
        width: gp.mode.info.horizontal_resolution as i64,
        height: gp.mode.info.vertical_resolution as i64,
        pixels_per_line: gp.mode.info.pixels_per_scan_line as i64,
    })
}

#[derive(Clone, Copy)]
pub struct VramBufferInfo {
    buf: *mut u8,
    width: i64,
    height: i64,
    pixels_per_line: i64,
}

impl Bitmap for VramBufferInfo {
    fn bytes_per_pixel(&self) -> i64 {
        4
    }

    fn pixels_per_line(&self) -> i64 {
        self.pixels_per_line
    }

    fn width(&self) -> i64 {
        self.width
    }

    fn height(&self) -> i64 {
        self.height
    }

    fn buf_mut(&mut self) -> *mut u8 {
        self.buf
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
pub struct EfiSystemTable {
    _reserved0: [u64; 12],
    pub boot_services: &'static EfiBootServicesTable,
}
const _: () = assert!(offset_of!(EfiSystemTable, boot_services) == 96);

/// https://uefi.org/specs/UEFI/2.10/04_EFI_System_Table.html#efi-boot-services-table
#[repr(C)]
pub struct EfiBootServicesTable {
    _reserved0: [u64; 7],
    get_memory_map: extern "win64" fn(
        memory_map_size: *mut usize,
        memory_map: *mut u8,
        map_key: *mut usize,
        descriptor_size: *mut usize,
        descriptor_version: *mut u32,
    ) -> EfiStatus,
    _reserved1: [u64; 21],
    exit_boot_services: extern "win64" fn(image_handle: EfiHandle, map_key: usize) -> EfiStatus,
    _reserved2: [u64; 10],
    // https://uefi.org/specs/UEFI/2.11/07_Services_Boot_Services.html#efi-boot-services-locateprotocol
    locate_protocol: extern "win64" fn(
        protocol: *const EfiGuid,
        registration: *const EfiVoid,
        interface: *mut *mut EfiVoid,
    ) -> EfiStatus,
}

const _: () = assert!(offset_of!(EfiBootServicesTable, get_memory_map) == 56);
const _: () = assert!(offset_of!(EfiBootServicesTable, exit_boot_services) == 232);
const _: () = assert!(offset_of!(EfiBootServicesTable, locate_protocol) == 320);

pub fn exit_from_efi_boot_services(
    image_handle: EfiHandle,
    efi_system_table: &EfiSystemTable,
    memory_map: &mut MemoryMapHolder,
) -> Result<()> {
    loop {
        efi_system_table.boot_services.get_memory_map(memory_map)?;

        let result = efi_system_table
            .boot_services
            .exit_boot_services(image_handle, memory_map.map_key);
        match result {
            Ok(_) => {
                break;
            }
            Err(error) => {
                // Ideally we should check if the error is EFI_INVALID_PARAMETER,
                // but I'm too lazy to do this.
                info!("Retrying exit_boot_services after refreshing memory map; error: {error}");
            }
        }
    }

    Ok(())
}

impl EfiBootServicesTable {
    pub fn get_memory_map(&self, holder: &mut MemoryMapHolder) -> Result<()> {
        let status = (self.get_memory_map)(
            &mut holder.memory_map_size,
            holder.memory_map_buffer.as_mut_ptr(),
            &mut holder.map_key,
            &mut holder.descriptor_size,
            &mut holder.descriptor_version,
        );
        if status != EfiStatus::Success {
            // Since we don't have access to alloc yet, we just print the error to the log
            warn!("get_memory_map failed: {status:?}");
            return Err("failed to get memory map");
        }

        Ok(())
    }

    fn exit_boot_services(&self, image_handle: EfiHandle, memory_map_key: usize) -> Result<()> {
        let status = (self.exit_boot_services)(image_handle, memory_map_key);
        if status != EfiStatus::Success {
            // Since we don't have access to alloc yet, we just print the error to the log
            warn!("exit_boot_services failed: {status:?}");
            return Err("failed to exit boot services");
        }
        Ok(())
    }
}

pub struct MemoryMapHolder {
    memory_map_buffer: [u8; MEMORY_MAP_BUFFER_SIZE],
    memory_map_size: usize,
    map_key: usize,
    descriptor_size: usize,
    descriptor_version: u32,
}
impl MemoryMapHolder {
    pub fn iter(&self) -> MemoryMapIterator {
        MemoryMapIterator {
            map: self,
            offset: 0,
        }
    }
}

const MEMORY_MAP_BUFFER_SIZE: usize = 0x8000;

impl Default for MemoryMapHolder {
    fn default() -> Self {
        Self {
            memory_map_buffer: [0; MEMORY_MAP_BUFFER_SIZE],
            memory_map_size: MEMORY_MAP_BUFFER_SIZE,
            map_key: 0,
            descriptor_size: 0,
            descriptor_version: 0,
        }
    }
}

pub struct MemoryMapIterator<'a> {
    map: &'a MemoryMapHolder,
    offset: usize,
}

impl<'a> Iterator for MemoryMapIterator<'a> {
    type Item = &'a EfiMemoryDescriptor;

    fn next(&mut self) -> Option<Self::Item> {
        if self.offset >= self.map.memory_map_size {
            None
        } else {
            let e: &EfiMemoryDescriptor = unsafe {
                &*(self.map.memory_map_buffer.as_ptr().add(self.offset)
                    as *const EfiMemoryDescriptor)
            };
            self.offset += self.map.descriptor_size;
            Some(e)
        }
    }
}

/// https://uefi.org/specs/UEFI/2.10/07_Services_Boot_Services.html#:~:text=Attribute%3B%0A%20%20%7D-,EFI_MEMORY_DESCRIPTOR,-%3B
#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct EfiMemoryDescriptor {
    memory_type: EfiMemoryType,
    physical_start: EfiPhysicalAddress,
    virtual_start: EfiVirtualAddress,
    number_of_pages: u64,
    attribute: u64,
}

impl EfiMemoryDescriptor {
    pub fn memory_type(&self) -> EfiMemoryType {
        self.memory_type
    }

    pub fn number_of_pages(&self) -> u64 {
        self.number_of_pages
    }

    pub fn physical_start(&self) -> EfiPhysicalAddress {
        self.physical_start
    }
}

#[repr(i64)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(non_camel_case_types)]
pub enum EfiMemoryType {
    RESERVED = 0,
    LOADER_CODE,
    LOADER_DATA,
    BOOT_SERVICES_CODE,
    BOOT_SERVICES_DATA,
    RUNTIME_SERVICES_CODE,
    RUNTIME_SERVICES_DATA,
    CONVENTIONAL_MEMORY,
    UNUSABLE_MEMORY,
    ACPI_RECLAIM_MEMORY,
    ACPI_MEMORY_NVS,
    MEMORY_MAPPED_IO,
    MEMORY_MAPPED_IO_PORT_SPACE,
    PAL_CODE,
    PERSISTENT_MEMORY,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EfiPhysicalAddress(u64);

impl From<EfiPhysicalAddress> for usize {
    fn from(value: EfiPhysicalAddress) -> Self {
        value.0 as usize
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct EfiVirtualAddress(u64);

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

// TODO: I think this does not model the error code well.
/// https://uefi.org/specs/UEFI/2.10/Apx_D_Status_Codes.html
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
#[must_use]
#[repr(u64)]
enum EfiStatus {
    Success = 0,
}

/// https://uefi.org/specs/UEFI/2.10/02_Overview.html#:~:text=code.%20Type%20UINTN.-,EFI_HANDLE,-A%20collection%20of
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct EfiHandle(usize);

/// https://uefi.org/specs/UEFI/2.11/02_Overview.html
struct EfiVoid();
