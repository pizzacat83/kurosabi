extern crate alloc;

use alloc::boxed::Box;
use core::{
    alloc::GlobalAlloc, borrow::BorrowMut, cell::RefCell, cmp::max, mem::size_of, ops::DerefMut,
    ptr::null_mut,
};

use crate::result::Result;
use crate::uefi::{EfiMemoryDescriptor, EfiMemoryType, MemoryMapHolder};
use crate::{dbg, println};

pub struct FirstFitAllocator {
    // Oh, can we use Box in the allocator itself!?
    first_header: RefCell<Option<Box<Header>>>,
}

// Needed to hold ALLOCATOR as global var.
// SAFETY: this program is single-threaded.
// TODO: fix this
unsafe impl Sync for FirstFitAllocator {}

#[global_allocator]
static ALLOCATOR: FirstFitAllocator = FirstFitAllocator {
    first_header: RefCell::new(None),
};

unsafe impl GlobalAlloc for FirstFitAllocator {
    unsafe fn alloc(&self, layout: core::alloc::Layout) -> *mut u8 {
        self.alloc_with_options(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: core::alloc::Layout) {
        // TODO
    }
}

impl FirstFitAllocator {
    pub fn init_with_mmap(&self, memory_map: &MemoryMapHolder) {
        for e in memory_map.iter() {
            if e.memory_type() != EfiMemoryType::CONVENTIONAL_MEMORY {
                continue;
            }
            self.add_free_from_descriptor(e);
        }
    }

    fn add_free_from_descriptor(&self, desc: &EfiMemoryDescriptor) {
        let mut start_addr: usize = desc.physical_start().into();
        let mut size = desc.number_of_pages() as usize * 4096;

        // Make sure the allocator does not include the address 0 as a free area
        // TODO: why? because it is for null pointer?
        if start_addr == 0 {
            // TODO: why 4096?
            start_addr = 4096;
            size = size.saturating_sub(4096);
        }
        if size <= 4096 {
            return;
        }

        let mut header = unsafe { Header::new_from_addr(start_addr) };

        header.next_header = None;
        header.is_allocated = false;
        header.size = size;

        // Make `header` the first header.
        // header.next_header should point to the current first header.

        let prev_last = self.first_header.borrow_mut().replace(header);

        self.first_header.borrow_mut().as_mut().unwrap().next_header = prev_last;
    }

    fn alloc_with_options(&self, layout: core::alloc::Layout) -> *mut u8 {
        let mut header = self.first_header.borrow_mut();
        let mut header = header.deref_mut();

        loop {
            if let Some(h) = header {
                if let Some(p) = h.provide(layout.size(), layout.align()) {
                    break p;
                } else {
                    header = h.next_header.borrow_mut();
                }
            } else {
                break null_mut::<u8>();
            }
        }
    }
}

#[derive(Debug)]
pub struct Header {
    next_header: Option<Box<Header>>,
    size: usize,
    is_allocated: bool,
    _reserved: usize,
}
impl Header {
    /// # Safety
    /// ???
    /// TODO: fill here
    unsafe fn new_from_addr(addr: usize) -> Box<Self> {
        let header = addr as *mut Header;
        header.write(Header {
            next_header: None,
            size: 0,
            is_allocated: false,
            _reserved: 0,
        });
        Box::from_raw(header)
    }

    // util for testing
    fn new_from_slice(slice: &mut [u8]) -> Result<Box<Self>> {
        let header = slice.as_mut_ptr() as *mut Header;

        // TODO: is this check enough for safety?
        if slice.len() < HEADER_SIZE {
            return Err("slice too small");
        }

        unsafe {
            header.write(Header {
                next_header: None,
                size: slice.len(),
                is_allocated: false,
                _reserved: 0,
            });
            Ok(Box::from_raw(header))
        }
    }

    fn provide(&mut self, size: usize, align: usize) -> Option<*mut u8> {
        let size = max(round_up_to_nearest_pow2(size).ok()?, HEADER_SIZE);
        let align = max(align, HEADER_SIZE);

        if self.is_allocated || !self.can_provide(size, align) {
            return None;
        }

        // |-----|----------------- self ---------|----------
        // |-----|----------------------          |----------
        //                                        ^ self.end_addr()
        //                              |-------|-
        //                               ^ allocated_addr
        //                              ^ header_for_allocated
        //                                      ^ header_for_padding
        //                                      ^ header_for_allocated.end_addr()
        // self has enough space to allocate the requested object.

        let mut size_used = 0;
        let allocated_addr = (self.end_addr() - size) & !(align - 1);
        let mut header_for_allocated = unsafe { Self::new_from_addr(allocated_addr - HEADER_SIZE) };
        header_for_allocated.is_allocated = true;
        header_for_allocated.size = size + HEADER_SIZE;
        size_used += header_for_allocated.size;
        header_for_allocated.next_header = self.next_header.take();

        if header_for_allocated.end_addr() != self.end_addr() {
            // Make a header for padding
            let mut header_for_padding =
                unsafe { Self::new_from_addr(header_for_allocated.end_addr()) };
            header_for_padding.is_allocated = false;
            header_for_padding.size = self.end_addr() - header_for_allocated.end_addr();
            size_used += header_for_padding.size;
            header_for_padding.next_header = header_for_allocated.next_header.take();
            header_for_allocated.next_header = Some(header_for_padding);
        }

        // Shrink self
        assert!(self.size >= size_used + HEADER_SIZE);
        self.size -= size_used;
        self.next_header = Some(header_for_allocated);
        Some(allocated_addr as *mut u8)
    }

    fn can_provide(&self, size: usize, align: usize) -> bool {
        // This check is rough - actual size needed may be smaller.
        // HEADER_SIZE * 2 => one for allocated region, another for padding.
        self.size >= size + HEADER_SIZE * 2 + align
    }

    fn start_addr(&self) -> usize {
        self as *const Header as usize
    }

    fn end_addr(&self) -> usize {
        self as *const Header as usize + self.size
    }
}

#[test_case]
fn test_provide() {
    let mut buf = [0u8; 2 << 16]; // 131kb
    let mut header = Header::new_from_slice(&mut buf).expect("failed to create header");
    {
        println!(
            "Test header: start={:?}, end={:?}",
            header.start_addr() as *const Header,
            header.end_addr() as *const Header
        );
    }
    dbg!(&header);

    let requested_size = 32;
    let requested_align = 32;

    let res = header.provide(requested_size, requested_align);

    dbg!(&header);

    dbg!(&res);
}

fn round_up_to_nearest_pow2(v: usize) -> Result<usize> {
    1usize
        .checked_shl(usize::BITS - v.wrapping_sub(1).leading_zeros())
        .ok_or("Out of range")
}

#[test_case]
fn round_up_to_nearest_pow2_tests() {
    assert_eq!(round_up_to_nearest_pow2(0), Err("Out of range")); // TODO: is this expected?
    assert_eq!(round_up_to_nearest_pow2(1), Ok(1));
    assert_eq!(round_up_to_nearest_pow2(2), Ok(2));
    assert_eq!(round_up_to_nearest_pow2(3), Ok(4));
    assert_eq!(round_up_to_nearest_pow2(4), Ok(4));
    assert_eq!(round_up_to_nearest_pow2(5), Ok(8));

    assert_eq!(
        round_up_to_nearest_pow2((1 << (usize::BITS as usize - 1)) - 1),
        Ok(1 << (usize::BITS - 1))
    );
    assert_eq!(
        round_up_to_nearest_pow2(1 << (usize::BITS as usize - 1)),
        Ok(1 << (usize::BITS - 1))
    );
    assert_eq!(
        round_up_to_nearest_pow2((1 << (usize::BITS - 1)) + 1),
        Err("Out of range")
    );
    assert_eq!(
        round_up_to_nearest_pow2(usize::MAX - 1),
        Err("Out of range")
    );
    assert_eq!(round_up_to_nearest_pow2(usize::MAX), Err("Out of range"));
}

const HEADER_SIZE: usize = size_of::<Header>();
const _: () = assert!(HEADER_SIZE == 32);
// Size of Header must be power of 2
const _: () = assert!(HEADER_SIZE.count_ones() == 1);
