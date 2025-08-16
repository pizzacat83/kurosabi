extern crate alloc;

use alloc::boxed::Box;
use core::{
    arch::asm,
    fmt,
    marker::PhantomData,
    mem::{offset_of, size_of, size_of_val},
    panic,
    pin::Pin,
};

pub fn write_io_port_u8(port: u16, data: u8) {
    unsafe {
        asm!("out dx, al",
        in("al") data,
        in("dx") port)
    }
}

pub fn read_io_port_u8(port: u16) -> u8 {
    let mut data: u8;
    unsafe {
        asm!("in al, dx",
            out("al") data,
            in("dx") port)
    }

    data
}

pub fn busy_loop_hint() {
    unsafe { asm!("pause") }
}

pub fn hlt() {
    unsafe { asm!("hlt") }
}

/// <https://wiki.osdev.org/CPU_Registers_x86-64#CR3>
pub fn read_cr3() -> *mut PML4 {
    let mut cr3: *mut PML4;
    unsafe { asm!("mov rax, cr3", out("rax") cr3) }

    cr3
}

pub fn trigger_debug_interrupt() {
    unsafe { asm!("int3") }
}

// <https://cdrdv2-public.intel.com/825758/253668-sdm-vol-3a.pdf>

// TODO: what's SHIFT?

#[repr(align(0x1000))]
pub struct Table<const LEVEL: usize, const SHIFT: usize, NEXT> {
    entries: [Entry<LEVEL, SHIFT, NEXT>; 0x200],
}

impl<const LEVEL: usize, const SHIFT: usize, NEXT> Table<LEVEL, SHIFT, NEXT> {
    pub fn next_level(&self, index: usize) -> Option<&NEXT> {
        self.entries.get(index)?.table()
    }
}

#[repr(transparent)]
pub struct Entry<const LEVEL: usize, const SHIFT: usize, NEXT> {
    value: usize,
    next_type: PhantomData<NEXT>, // TODO: what's this?
}

impl<const LEVEL: usize, const SHIFT: usize, NEXT> Entry<LEVEL, SHIFT, NEXT> {
    // Present; if 1, self.table() is present.
    fn is_present(&self) -> bool {
        (self.value & ATTR_PRESENT) != 0
    }

    // Read/write
    fn is_writable(&self) -> bool {
        (self.value & ATTR_WRITABLE) != 0
    }

    // User/supervisor
    fn is_user(&self) -> bool {
        (self.value & ATTR_USER) != 0
    }

    fn table(&self) -> Option<&NEXT> {
        if !self.is_present() {
            return None;
        }

        Some(unsafe { &*((self.value & !ATTR_MASK) as *const NEXT) })
    }
}

impl<const LEVEL: usize, const SHIFT: usize, NEXT> fmt::Debug for Entry<LEVEL, SHIFT, NEXT> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "L{}Entry @ {:#p} {{ {:#018x} {}{}{} }}",
            LEVEL,
            self,
            self.value,
            if self.is_present() { "P" } else { "N" },
            if self.is_writable() { "W" } else { "R" },
            if self.is_user() { "U" } else { "S" },
        )
    }
}

impl<const LEVEL: usize, const SHIFT: usize, NEXT> fmt::Debug for Table<LEVEL, SHIFT, NEXT> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "L{}Table @ {:#p} {{", LEVEL, self)?;

        for (i, e) in self.entries.iter().enumerate() {
            if e.is_present() {
                writeln!(f, "  entry[{:3}] = {:?}", i, e)?;
            }
        }

        writeln!(f, "}}")
    }
}

const PAGE_SIZE: usize = 4096;

pub type PT = Table<1, 12, [u8; PAGE_SIZE]>;
pub type PD = Table<2, 21, PT>;
pub type PDPT = Table<3, 30, PD>;
pub type PML4 = Table<4, 39, PDPT>;

const ATTR_MASK: usize = 0xfff;
const ATTR_PRESENT: usize = 1 << 0;
const ATTR_WRITABLE: usize = 1 << 1;
const ATTR_USER: usize = 1 << 2;
const ATTR_WRITE_THROUGH: usize = 1 << 3;
const ATTR_CACHE_DISABLE: usize = 1 << 4;

pub fn init_exceptions() -> (GdtWrapper, Idt) {
    // TODO: init GDT

    let idt = Idt::new(KERNEL_CS);
    ((), idt)
}

/// Interrupt Descriptor Table
pub struct Idt {
    entries: Pin<Box<[IdtDescriptor; 0x100]>>,
}
impl Idt {
    fn new(segment_selector: u16) -> Self {
        let mut entries = [IdtDescriptor::new(
            segment_selector,
            1,
            IdtAttr::IntGateDPL0,
            int_handler_unimplemented,
        ); 0x100];

        // TODO: customize handlers

        let entries = Box::pin(entries);

        let params = IdtrParameters {
            limit: size_of_val(&entries) as u16,
            base: entries.as_ptr(),
        };
        unsafe {
            asm!("lidt [rcx]", in("rcx") &params);
        }

        Self { entries }
    }
}

/// The parameter of LIDT and LGDT instruction.
#[repr(C, packed)]
#[derive(Debug)]
struct IdtrParameters {
    limit: u16,
    base: *const IdtDescriptor,
}
const _: () = assert!(size_of::<IdtrParameters>() == 10);
const _: () = assert!(offset_of!(IdtrParameters, base) == 2);

/// (offset_low, offset_mid, offset_high) is the address of the interruption handler.
#[repr(C, packed)]
#[derive(Clone, Copy)]
pub struct IdtDescriptor {
    offset_low: u16,
    segment_selector: u16,
    ist_index: u8,
    attr: IdtAttr,
    offset_mid: u16,
    offset_high: u32,
    _reserved: u32,
}
impl IdtDescriptor {
    fn new(
        segment_selector: u16,
        ist_index: u8,
        attr: IdtAttr,
        handler: unsafe extern "sysv64" fn(),
    ) -> Self {
        let handler_addr = handler as *const unsafe extern "sysv64" fn() as usize;

        Self {
            offset_low: handler_addr as u16,
            segment_selector,
            ist_index,
            attr,
            offset_mid: (handler_addr >> 16) as u16,
            offset_high: (handler_addr >> 32) as u32,
            _reserved: 0,
        }
    }
}

// TODO: no_mangle needed?
#[no_mangle]
extern "sysv64" fn int_handler_unimplemented() {
    panic!("unexpected interrupt!");
}

// PDDRTTTT (TTTT: type, R: reserved, D: DPL, P: present)
// DPL: Descriptor Privilege Level
// TODO: understand DPL
#[repr(u8)]
#[derive(Copy, Clone)]
enum IdtAttr {
    // Without _NotPresent value, MaybeUninit::zeroed() on this struct will be undefined behavior.
    _NotPresent = 0,

    IntGateDPL0 = BIT_FLAGS_INTGATE | BIT_FLAGS_PRESENT | BIT_FLAGS_DPL0,
    IntGateDPL3 = BIT_FLAGS_INTGATE | BIT_FLAGS_PRESENT | BIT_FLAGS_DPL3,
}

pub const BIT_FLAGS_INTGATE: u8 = 0b0000_1110u8;
pub const BIT_FLAGS_PRESENT: u8 = 0b1000_0000u8;
pub const BIT_FLAGS_DPL0: u8 = 0 << 5; // system
pub const BIT_FLAGS_DPL3: u8 = 3 << 5; // user

// TODO
type GdtWrapper = ();

// TODO: what's this?
const KERNEL_CS: u16 = 1 << 3;

#[cfg(test)]
mod tests {
    use super::*;

    #[test_case]
    fn test_entry_is_present() {
        // Yeah I even misimplement this simple function so I test this

        {
            let present: Entry<1, 0, ()> = Entry {
                value: 0x1,
                next_type: PhantomData,
            };
            assert!(present.is_present());
        }
        {
            let not_present: Entry<1, 0, ()> = Entry {
                value: 0x0,
                next_type: PhantomData,
            };
            assert!(!not_present.is_present());
        }
    }

    #[test_case]
    fn test_entry_is_writable() {
        {
            let writable: Entry<1, 0, ()> = Entry {
                value: 0x2,
                next_type: PhantomData,
            };
            assert!(writable.is_writable());
        }
        {
            let not_writable: Entry<1, 0, ()> = Entry {
                value: 0x0,
                next_type: PhantomData,
            };
            assert!(!not_writable.is_writable());
        }
    }

    #[test_case]
    fn test_entry_is_user() {
        {
            let user: Entry<1, 0, ()> = Entry {
                value: 0x4,
                next_type: PhantomData,
            };
            assert!(user.is_user());
        }
        {
            let not_user: Entry<1, 0, ()> = Entry {
                value: 0x0,
                next_type: PhantomData,
            };
            assert!(!not_user.is_user());
        }
    }
}
