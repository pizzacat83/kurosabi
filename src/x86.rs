use core::{arch::asm, fmt, marker::PhantomData};

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
