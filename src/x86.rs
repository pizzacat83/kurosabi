extern crate alloc;

use alloc::boxed::Box;
use core::{
    arch::{asm, global_asm},
    fmt,
    marker::PhantomData,
    mem::{offset_of, size_of, size_of_val, MaybeUninit},
    panic,
    pin::Pin,
};

use crate::{error, info, print, println, result::Result};

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

/// # Safety
/// Writing to CR3 can causes any exceptions so it is programmer's responsibility to setup correct page tables.
#[no_mangle]
pub unsafe fn write_cr3(table: *const PML4) {
    info!("write_cr3: {:#018x}", table as usize);
    asm!("mov cr3, rax", in("rax") table)
}

// ES: Extra Segment
/// # Safety
/// Anything can happen if the given selector is invalid.
pub unsafe fn write_es(selector: u16) {
    asm!(
	"mov es, ax",
                in("ax") selector)
}

/// CS: Code Segment
/// # Safety
/// Anything can happen if the CS given is invalid.
pub unsafe fn write_cs(selector: u16) {
    // The MOV instruction CANNOT be used to load the CS register.
    // Use far-jump(ljmp) instead.
    // TODO: what's this hack?
    asm!(
	"lea rax, [rip + 2f]", // Target address (label 1 below)
	"push cx", // Construct a far pointer on the stack
	"push rax",
	"ljmp [rsp]",
        "2:",
        "add rsp, 8 + 2", // Cleanup the far pointer on the stack
                in("cx") selector)
}

/// SS: Stack Segment
///
/// # Safety
/// Anything can happen if the given selector is invalid.
pub unsafe fn write_ss(selector: u16) {
    asm!(
	"mov ss, ax",
                in("ax") selector)
}

/// Data Segment
///
/// # Safety
/// Anything can happen if the given selector is invalid.
pub unsafe fn write_ds(selector: u16) {
    asm!(
	"mov ds, ax",
                in("ax") selector)
}

/// FS: General Purpose Segment
///
/// # Safety
/// Anything can happen if the given selector is invalid.
pub unsafe fn write_fs(selector: u16) {
    asm!(
	"mov fs, ax",
                in("ax") selector)
}

/// GS: General Purpose Segment
///
/// # Safety
/// Anything can happen if the given selector is invalid.
pub unsafe fn write_gs(selector: u16) {
    asm!(
	"mov gs, ax",
                in("ax") selector)
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

    /// It is caller's responsibility to ensure addr relates to this entry.
    fn entry_mut(&mut self, addr: usize) -> &mut Entry<LEVEL, SHIFT, NEXT> {
        let index = (addr >> SHIFT) & 0x1ff;
        &mut self.entries[index]
    }

    /// It is caller's responsibility to ensure addr relates to this entry.
    fn entry(&self, addr: usize) -> &Entry<LEVEL, SHIFT, NEXT> {
        let index = (addr >> SHIFT) & 0x1ff;
        &self.entries[index]
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

    fn next_addr(&self) -> *mut NEXT {
        (self.value & !ATTR_MASK) as *mut NEXT
    }

    fn table(&self) -> Option<&NEXT> {
        if !self.is_present() {
            return None;
        }

        Some(unsafe { &*self.next_addr() })
    }

    fn table_mut(&self) -> Option<&mut NEXT> {
        if !self.is_present() {
            return None;
        }

        Some(unsafe { &mut *self.next_addr() })
    }
    // TODO: Why return &mut Self?
    fn ensure_populated(&mut self) -> Result<&mut Self> {
        if self.is_present() {
            Ok(self)
        } else {
            self.populate()
        }
    }

    fn populate(&mut self) -> Result<&mut Self> {
        if self.is_present() {
            return Err("Page is already populated");
        }
        // TODO: DRY?
        // TODO: why MaybeUninit is needed? Why can't we just create a zero value safely?
        let next: Box<NEXT> = Box::new(unsafe { MaybeUninit::zeroed().assume_init() });
        self.value = (Box::into_raw(next) as usize) | (PageAttr::ReadWriteKernel as usize);
        Ok(self)
    }
}

#[derive(Debug, Copy, Clone)]
#[repr(u64)]
pub enum PageAttr {
    NotPresent = 0,
    ReadWriteKernel = (ATTR_PRESENT | ATTR_WRITABLE) as u64,
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

pub const PAGE_SIZE: usize = 4096;

/// The address of the physical page!
pub type PTEntry = Entry<1, 12, [u8; PAGE_SIZE]>;

pub type PT = Table<1, 12, [u8; PAGE_SIZE]>;
pub type PD = Table<2, 21, PT>;
pub type PDPT = Table<3, 30, PD>;
pub type PML4 = Table<4, 39, PDPT>;

impl PML4 {
    pub fn new() -> Box<Self> {
        let this = unsafe { MaybeUninit::zeroed().assume_init() };
        Box::new(this)
    }

    // Maps [virt_start:virt_end] to [phys:phys+size].
    pub fn create_mapping(
        &mut self,
        virt_start: u64,
        virt_end: u64,
        phys_start: u64,
        attr: PageAttr,
    ) -> Result<()> {
        if virt_start & (ATTR_MASK as u64) != 0 {
            return Err("virt_start is not aligned");
        }
        if virt_end & (ATTR_MASK as u64) != 0 {
            return Err("virt_end is not aligned");
        }
        if phys_start & (ATTR_MASK as u64) != 0 {
            return Err("phys_start is not aligned");
        }

        for virt_addr in (virt_start..virt_end).step_by(PAGE_SIZE) {
            let pdpt = self
                .entry_mut(virt_addr as usize)
                .ensure_populated()?
                .table_mut()
                .expect("table_mut failed although already populated");
            let pd = pdpt
                .entry_mut(virt_addr as usize)
                .ensure_populated()?
                .table_mut()
                .expect("table_mut failed although already populated");
            let pt = pd
                .entry_mut(virt_addr as usize)
                .ensure_populated()?
                .table_mut()
                .expect("table_mut failed although already populated");
            let page_table_entry = pt.entry_mut(virt_addr as usize);

            page_table_entry.set_page((virt_addr - virt_start + phys_start) as usize, attr)?;
        }

        Ok(())
    }

    pub fn identity_mapping_sanity_check(
        &self,
        virt_start: u64,
        virt_end: u64,
        attr: PageAttr,
    ) -> Result<()> {
        if virt_start & (ATTR_MASK as u64) != 0 {
            return Err("virt_start is not aligned");
        }
        if virt_end & (ATTR_MASK as u64) != 0 {
            return Err("virt_end is not aligned");
        }

        for virt_addr in (virt_start..virt_end).step_by(PAGE_SIZE) {
            let page_table_entry = self
                .get_page_table_entry(virt_addr)
                .unwrap_or_else(|error| panic!("entry of {virt_addr:#018x} not found: {error}"));

            let expected = virt_addr as usize | attr as usize;
            let actual = page_table_entry.value;

            assert_eq!(
                expected, actual,
                "unexpected value for page {:#018x}! Expected: {:#018x}, Actual: {:#018x}",
                virt_addr, expected, actual
            );
        }

        Ok(())
    }

    fn get_page_table_entry(&self, virt_addr: u64) -> Result<&PTEntry> {
        let pdpt: &Table<3, 30, Table<2, 21, Table<1, 12, [u8; 4096]>>> = self
            .entry(virt_addr as usize)
            .table()
            .ok_or("Not found in PDPT")?;
        let pd = pdpt
            .entry(virt_addr as usize)
            .table()
            .ok_or("not found in PD")?;
        let pt = pd
            .entry(virt_addr as usize)
            .table()
            .ok_or("Not found in PT")?;
        let page_table_entry = pt.entry(virt_addr as usize);
        Ok(page_table_entry)
    }

    fn print_entry(&self, virt_addr: u64) {
        let pml4index = (virt_addr >> 39) & 0x1ff;
        let pdptindex = (virt_addr >> 30) & 0x1ff;
        let pdindex = (virt_addr >> 21) & 0x1ff;
        let ptindex = (virt_addr >> 12) & 0x1ff;
        let ptentry = self.get_page_table_entry(virt_addr);

        print!(
            "[{:#05x}, {:#05x}, {:#05x}, {:#05x}] -> ",
            pml4index, pdptindex, pdindex, ptindex
        );
        match ptentry {
            Ok(entry) => {
                println!("Ok({:#018x})", entry.value);
            }
            Err(error) => {
                println!("Err(\"{error}\")");
            }
        }
    }
}

impl PTEntry {
    fn set_page(&mut self, phys_addr: usize, attr: PageAttr) -> Result<()> {
        if phys_addr & ATTR_MASK != 0 {
            return Err("phys_addr is not aligned");
        }
        self.value = phys_addr | attr as usize;
        Ok(())
    }
}

const ATTR_MASK: usize = 0xfff;
const ATTR_PRESENT: usize = 1 << 0;
const ATTR_WRITABLE: usize = 1 << 1;
const ATTR_USER: usize = 1 << 2;
const ATTR_WRITE_THROUGH: usize = 1 << 3;
const ATTR_CACHE_DISABLE: usize = 1 << 4;

pub fn init_exceptions() -> (GdtWrapper, Idt) {
    let gdt = GdtWrapper::new();
    gdt.load();

    unsafe {
        write_cs(SEGMENT_SELECTOR_KERNEL_CODE);
        write_ss(SEGMENT_SELECTOR_KERNEL_DATA);
        write_es(SEGMENT_SELECTOR_KERNEL_DATA);
        write_ds(SEGMENT_SELECTOR_KERNEL_DATA);
        write_fs(SEGMENT_SELECTOR_KERNEL_DATA);
        write_gs(SEGMENT_SELECTOR_KERNEL_DATA);
    }

    let idt = Idt::new(SEGMENT_SELECTOR_KERNEL_CODE);
    (gdt, idt)
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

        entries[3] = IdtDescriptor::new(
            segment_selector,
            1,
            // Set DPL=3 to allow user land to make this interrupt (e.g. via
            // int3 op)
            IdtAttr::IntGateDPL3,
            interrupt_entrypoint3,
        );

        // TODO: customize handlers

        let limit = size_of_val(&entries) as u16;

        let entries = Box::pin(entries);

        let params = IdtrParameters {
            limit,
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

/// The common interrupt handler.
///
/// When an interrupt happens, following happens:
/// 1. interrupt_entrypointN, the handler registered in IDT, is called
///    This will set rcx=#INT and jump to inthandler_common
/// 2. inthandler_common is called by interrupt_entrypointN
///    This stashes registers to stack, calls the Rust fn inthandler,
///    restores the registers, and returns from interrupt handling.
///    
#[no_mangle]
extern "sysv64" fn inthandler(info: &InterruptInfo, interrupt_number: usize) {
    error!("Interrupt Info: {:?}", info);
    error!("Exception {interrupt_number:#04x}: ");
    match interrupt_number {
        3 => {
            error!("Breakpoint");
            return;
        }
        _ => {
            error!("Not handled");
        }
    }
    panic!("fatal exception");
}

#[repr(C)]
#[derive(Clone, Copy)]
struct InterruptInfo {
    /// Should be aligned on 16-byte boundaries to pass the
    /// alignment checks done by FXSAVE / FXRSTOR
    fpu_context: FPUContext,

    _dummy: u64,

    greg: GeneralRegisterContext,
    error_code: u64,

    /// CPU stashes this info
    ctx: InterruptContext,
}

const _: () = assert!(size_of::<InterruptInfo>() == (16 + 4 + 1) * 8 + 8 + 512);

impl fmt::Debug for InterruptInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "
        {{
            rip: {:#018x}, CS: {:#06x},
            rsp: {:#018x}, SS: {:#06x},
            rbp: {:#018x},

            rflags:     {:#018x},
            error_code: {:#018x},

            rax: {:#018x}, rcx: {:#018x},
            rdx: {:#018x}, rbx: {:#018x},
            rsi: {:#018x}, rdi: {:#018x},
            r8:  {:#018x}, r9:  {:#018x},
            r10: {:#018x}, r11: {:#018x},
            r12: {:#018x}, r13: {:#018x},
            r14: {:#018x}, r15: {:#018x},
        }}",
            self.ctx.rip,
            self.ctx.cs,
            self.ctx.rsp,
            self.ctx.ss,
            self.greg.rbp,
            self.ctx.rflags,
            self.error_code,
            self.greg.rax,
            self.greg.rcx,
            self.greg.rdx,
            self.greg.rbx,
            self.greg.rsi,
            self.greg.rdi,
            self.greg.r8,
            self.greg.r9,
            self.greg.r10,
            self.greg.r11,
            self.greg.r12,
            self.greg.r13,
            self.greg.r14,
            self.greg.r15,
        )
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
struct FPUContext {
    data: [u8; 512],
}

#[allow(dead_code)]
#[repr(C)]
#[derive(Clone, Copy)]
struct GeneralRegisterContext {
    rax: u64,
    rdx: u64,
    rbx: u64,
    rbp: u64,
    rsi: u64,
    rdi: u64,
    r8: u64,
    r9: u64,
    r10: u64,
    r11: u64,
    r12: u64,
    r13: u64,
    r14: u64,
    r15: u64,
    rcx: u64,
}
const _: () = assert!(size_of::<GeneralRegisterContext>() == (16 - 1) * 8);

#[allow(dead_code)]
#[repr(C)]
#[derive(Clone, Copy)]
struct InterruptContext {
    rip: u64,
    cs: u64,
    rflags: u64,
    rsp: u64,
    ss: u64,
}
const _: () = assert!(size_of::<InterruptContext>() == 8 * 5);

/// This generates interrupt_entrypointN()
/// Generated asm will be looks like this:
/// ```
/// .global interrupt_entrypointN
///    interrupt_entrypointN:
///    push 0 // No error code
///    push rcx // Save rcx first to reuse
///    mov rcx, N // INT#
///    jmp inthandler_common
/// ```
macro_rules! interrupt_entrypoint {
    ($index:literal) => {
        global_asm!(concat!(
            ".global interrupt_entrypoint",
            stringify!($index),
            "\n",
            "interrupt_entrypoint",
            stringify!($index),
            ":\n",
            "push 0 // No error code\n",
            "push rcx // Save rcx first to reuse\n",
            "mov rcx, ",
            stringify!($index),
            "\n",
            "jmp inthandler_common"
        ));
    };
}
macro_rules! interrupt_entrypoint_with_ecode {
    ($index:literal) => {
        global_asm!(concat!(
            ".global interrupt_entrypoint",
            stringify!($index),
            "\n",
            "interrupt_entrypoint",
            stringify!($index),
            ":\n",
            "push rcx // Save rcx first to reuse\n",
            "mov rcx, ",
            stringify!($index),
            "\n",
            "jmp inthandler_common"
        ));
    };
}

interrupt_entrypoint!(3);
interrupt_entrypoint!(6);
interrupt_entrypoint_with_ecode!(8);
interrupt_entrypoint_with_ecode!(13);
interrupt_entrypoint_with_ecode!(14);
interrupt_entrypoint!(32);

extern "sysv64" {
    fn interrupt_entrypoint3();
    fn interrupt_entrypoint6();
    fn interrupt_entrypoint8();
    fn interrupt_entrypoint13();
    fn interrupt_entrypoint14();
    fn interrupt_entrypoint32();
}

// inthandler_common
// Stash registers, call inthandler, restore registers, iretq
global_asm!(
    r#"
.global inthandler_common
inthandler_common:
    // Stash general purpose registers (except rsp and rcx)
    // In reverse order of GeneralRegisterContext
    push r15
    push r14
    push r13
    push r12
    push r11
    push r10
    push r9
    push r8
    push rdi
    push rsi
    push rbp
    push rbx
    push rdx
    push rax
    // Stash FPU State
    sub rsp, 512 + 8
    fxsave64[rsp]

    // Prepare to call inithandler
    // 1st parameter: info: &InterruptInfo (pointer to the saved CPU state)
    mov rdi, rsp
    // Align the stack to 16-bytes boundary
    mov rbp, rsp
    and rsp, -16
    // 2nd parameter: interrupt_number: usize
    mov rsi, rcx

    call inthandler

    mov rsp, rbp
    //
    fxrstor64[rsp]
    add rsp, 512 + 8
    //
    pop rax
    pop rdx
    pop rbx
    pop rbp
    pop rsi
    pop rdi
    pop r8
    pop r9
    pop r10
    pop r11
    pop r12
    pop r13
    pop r14
    pop r15
    //
    pop rcx
    add rsp, 8 // for Error Code
    iretq
"#
);

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

pub struct GdtWrapper {
    inner: Pin<Box<Gdt>>,
    tss64: TaskStateSegment64,
}
impl GdtWrapper {
    fn new() -> Self {
        let tss64 = TaskStateSegment64::new();

        let gdt = Gdt {
            null_segment: GdtSegmentDescriptor::null(),
            kernel_code_segment: GdtSegmentDescriptor::new(GdtAttr::KernelCode),
            kernel_data_segment: GdtSegmentDescriptor::new(GdtAttr::KernelData),
            task_state_segment: TaskStateSegment64Descriptor::new(tss64.phys_addr()),
        };

        let gdt = Box::pin(gdt);

        Self { inner: gdt, tss64 }
    }

    fn load(&self) {
        let params = GdtrParameters {
            limit: (size_of::<Gdt>() - 1) as u16, // TODO: why -1?
            base: self.inner.as_ref().get_ref() as *const Gdt,
        };
        info!("Loading GDT @ {:#018x}", params.base as u64);

        // SAFETY: This is safe since it is loading a valid GDT just constructed above
        unsafe {
            asm!("lgdt [rcx]", in("rcx") &params);
        }

        info!("Loading TSS ( selector = {:#x} )", SEGMENT_SELECTOR_TSS64);
        unsafe {
            // ltr: Load Task Register
            asm!("ltr cx", in("cx") SEGMENT_SELECTOR_TSS64);
        }
    }
}

#[repr(C, packed)]
struct GdtrParameters {
    limit: u16,
    base: *const Gdt,
}
const _: () = assert!(size_of::<GdtrParameters>() == 10);
const _: () = assert!(offset_of!(GdtrParameters, base) == 2);

/// Global Descriptor Table
///
/// <https://wiki.osdev.org/GDT_Tutorial>
#[repr(C, packed)]
struct Gdt {
    null_segment: GdtSegmentDescriptor,
    kernel_code_segment: GdtSegmentDescriptor,
    kernel_data_segment: GdtSegmentDescriptor,
    task_state_segment: TaskStateSegment64Descriptor,
}
const _: () = assert!(size_of::<Gdt>() == 40);

// Segment selectors
const SEGMENT_SELECTOR_KERNEL_CODE: u16 = 1 << 3;
const SEGMENT_SELECTOR_KERNEL_DATA: u16 = 2 << 3;
const SEGMENT_SELECTOR_TSS64: u16 = 3 << 3;
// The selector is (index << 3) because the LSB 3 bit is used for other info.

pub struct GdtSegmentDescriptor {
    value: u64,
}
impl GdtSegmentDescriptor {
    const fn null() -> GdtSegmentDescriptor {
        Self { value: 0 }
    }

    fn new(attr: GdtAttr) -> Self {
        Self { value: attr as u64 }
    }
}

// Segment descriptor:
// 63-56: Base[31:24]
// 55-52: Flags
// 51-48: Limit[19:16]
// 47-40: Access Byte
// 39-32: Base[23:16]
// 31-16: Base[15:00]
// 15-00: Limit[15:00]
//
// Note: Base and Limit is ignored in 64-bit mode.
// <https://wiki.osdev.org/Global_Descriptor_Table#Segment_Descriptor>

// Access Byte: PDDSECRA
// P: Present bit.
// D: DPL (Descriptor Privilege Level)
// S: Descriptor type (0: system, 1: code, data)
// E: Executable bit.
// C: Direction bit/Confirming bit.
// R: Readable bit for code segments. Writable bit for data segments.
// A: Accessed bit (set by CPU).

//                               PDDSECRA
pub const BIT_TYPE_DATA: u64 = 0b00010000u64 << 40;
pub const BIT_TYPE_CODE: u64 = 0b00011000u64 << 40;
pub const BIT_DS_WRITABLE: u64 = 0b00000010u64 << 40;
pub const BIT_PRESENT: u64 = 1u64 << 47;

// Flags: GDL_
// G: Granularity flag.
// D: Size flag.
// L: Log-mode code flag.
pub const BIT_CS_LONG_MODE: u64 = 0b10u64 << 52;
pub const BIT_CS_READABLE: u64 = 0b10u64 << 52; // TODO: why same as BIT_CS_LONG_MODE? Maybe this was meant to be  0b00000010u64 << 40?

#[repr(u64)]
enum GdtAttr {
    KernelCode = BIT_TYPE_CODE | BIT_PRESENT | BIT_CS_LONG_MODE | BIT_CS_READABLE,
    KernelData = BIT_TYPE_DATA | BIT_PRESENT | BIT_DS_WRITABLE,
}

/// <https://wiki.osdev.org/Global_Descriptor_Table#Long_Mode_System_Segment_Descriptor>
#[repr(C, packed)]
pub struct TaskStateSegment64Descriptor {
    limit_low: u16,
    base_low: u16,
    base_mid_low: u8,
    attr: u16,
    base_mid_high: u8,
    base_high: u32,
    reserved: u32,
}
impl TaskStateSegment64Descriptor {
    fn new(base_addr: usize) -> Self {
        Self {
            limit_low: size_of::<TaskStateSegment64Inner>() as u16,
            base_low: (base_addr & 0xffff) as u16,
            base_mid_low: ((base_addr >> 16) & 0xff) as u8,
            //      GDL_      PDDS ECRA
            attr: 0b1000_0000_1000_1001,
            base_mid_high: ((base_addr >> 24) & 0xff) as u8,
            base_high: ((base_addr >> 32) & 0xffffffff) as u32,
            reserved: 0,
        }
    }
}
const _: () = assert!(size_of::<TaskStateSegment64Descriptor>() == 16);

pub struct TaskStateSegment64 {
    inner: Pin<Box<TaskStateSegment64Inner>>,
}
impl TaskStateSegment64 {
    fn new() -> Self {
        let rsp0 = unsafe { Self::alloc_interrupt_stack() };
        let mut ist = [0u64; 8];
        for ist in ist[1..=7].iter_mut() {
            *ist = unsafe { Self::alloc_interrupt_stack() };
        }
        let tss64 = TaskStateSegment64Inner {
            _reserved0: 0,
            _rsp: [rsp0, 0, 0], // what's this?
            _ist: ist,
            _reserved1: [0; 5],
            _io_map_base_addr: 0,
        };

        let this = Self {
            inner: Box::pin(tss64),
        };

        info!("TSS64 created @ {:#x}", this.phys_addr());

        this
    }

    fn phys_addr(&self) -> usize {
        self.inner.as_ref().get_ref() as *const TaskStateSegment64Inner as usize
    }

    // TODO: how unsafe?
    unsafe fn alloc_interrupt_stack() -> u64 {
        const HANDLER_STACK_SIZE: usize = 64 * 1024;
        let stack = Box::new([0u8; HANDLER_STACK_SIZE]);
        let rsp = unsafe { stack.as_ptr().add(HANDLER_STACK_SIZE) as u64 };

        // Make sure the stack won't be deallocated
        core::mem::forget(stack);

        rsp
    }
}

#[repr(C, packed)]
pub struct TaskStateSegment64Inner {
    _reserved0: u32,
    _rsp: [u64; 3],
    _ist: [u64; 8],
    _reserved1: [u16; 5],
    _io_map_base_addr: u16,
}
const _: () = assert!(size_of::<TaskStateSegment64Inner>() == 104);

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
