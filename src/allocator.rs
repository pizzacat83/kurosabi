extern crate alloc;

use alloc::boxed::Box;
use core::mem::size_of_val;
use core::{
    alloc::GlobalAlloc, borrow::BorrowMut, cell::RefCell, cmp::max, mem::size_of, ops::DerefMut,
    ptr::null_mut,
};
use core::{fmt, slice};

use crate::print::hexdump_bytes;
use crate::result::Result;
use crate::uefi::{EfiMemoryDescriptor, EfiMemoryType, MemoryMapHolder};
use crate::{dbg, info, println};

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

pub fn init_with_mmap(memory_map: &MemoryMapHolder) {
    ALLOCATOR.init_with_mmap(memory_map);
}

unsafe impl GlobalAlloc for FirstFitAllocator {
    unsafe fn alloc(&self, layout: core::alloc::Layout) -> *mut u8 {
        self.alloc_with_options(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: core::alloc::Layout) {
        let mut region = Header::from_allocated_region(ptr);
        region.is_allocated = false;

        // Intentionally leak the box, since Box<Header> must not be dropped
        Box::leak(region);
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

pub struct Header {
    next_header: Option<Box<Header>>,
    size: usize,
    is_allocated: bool,
    _reserved: usize,
}
impl Header {
    /// Initializes a Header at the given address.
    ///
    /// # Safety
    /// ???
    /// TODO: fill here
    unsafe fn new_from_addr(addr: usize) -> Box<Self> {
        let header = addr as *mut Header;
        header.write(Header {
            next_header: None,
            size: 0, // This is invalid. The size must be bigger than HEADER_SIZE.
            is_allocated: false,
            _reserved: 0,
        });
        Box::from_raw(header)
    }

    /// The box must not be dropped; use Box::leak.
    unsafe fn from_allocated_region(payload_start_addr: *mut u8) -> Box<Header> {
        let header = payload_start_addr.sub(HEADER_SIZE) as *mut Header;

        // TODO: this makes aliasing, right? the global allocator owns the header list (as a linked list of Boxes)
        // but this function makes another box of the same pointer.
        // Can we make it less unsafe? Like using a different return type
        Box::from_raw(header)
    }

    // util for testing
    // the chunk will be aligned for test reproducibility.
    fn new_from_slice_aligned(slice: &mut [u8], align: usize, size: usize) -> Result<Box<Self>> {
        let unaligned_start = slice.as_mut_ptr() as usize;
        let aligned_start = (unaligned_start + align) & !(align - 1);
        let aligned_end = aligned_start + size;

        let start_offset = aligned_start - unaligned_start;

        // TODO: is this check enough for safety?
        if size_of_val(slice) < start_offset + size {
            return Err("slice too small");
        }

        if size < HEADER_SIZE {
            return Err("chunk size too small");
        }

        info!(
            "shifted from {:#x}:{:#x} to {:#x}:{:#x}",
            unaligned_start, aligned_start, aligned_start, aligned_end
        );

        let header = aligned_start as *mut Header;

        unsafe {
            header.write(Header {
                next_header: None,
                size,
                is_allocated: false,
                _reserved: 0,
            });
            Ok(Box::from_raw(header))
        }
    }

    fn provide(&mut self, size: usize, align: usize) -> Option<*mut u8> {
        // TODO: why pow2? of the size excluding the header?
        let size_excluding_header = max(round_up_to_nearest_pow2(size).ok()?, HEADER_SIZE);
        let align = max(align, HEADER_SIZE);

        if self.is_allocated || !self.can_provide(size_excluding_header, align) {
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

        // The payload start address must be aligned as requested.
        let allocated_payload_addr = (self.end_addr() - size_excluding_header) & !(align - 1);
        let allocated_header_start = allocated_payload_addr - HEADER_SIZE;

        let mut header_for_allocated = unsafe { Self::new_from_addr(allocated_header_start) };
        header_for_allocated.is_allocated = true;
        header_for_allocated.set_size_including_header(size_excluding_header + HEADER_SIZE);
        header_for_allocated.next_header = self.next_header.take();

        if header_for_allocated.end_addr() != self.end_addr() {
            // Due to alignment, there is a free space after header_for_allocated until the end of self.
            // Before: self -> self_original_next
            // After: self -> allocated -> padding -> self_original_next

            // TODO: no need to check if the size is too small?

            let mut header_for_padding =
                unsafe { Self::new_from_addr(header_for_allocated.end_addr()) };
            header_for_padding.is_allocated = false;
            header_for_padding
                .set_size_including_header(self.end_addr() - header_for_allocated.end_addr());

            {
                // Before:
                // header_for_allocated.next_header == self_original_next
                // header_for_padding.next_header == None
                // After:
                // header_for_allocated.next_header == Some(header_for_padding)
                // header_for_padding.next_header == self_original_next
                header_for_padding.next_header = header_for_allocated.next_header.take();
                header_for_allocated.next_header = Some(header_for_padding);
            }
        } else {
            // The new chunk is allocated in the exact end of self!
            // So the original self is chunked into self -> allocated

            // Before: self -> self_original_next
            // After: self -> allocated -> self_original_next
        }

        // Shrink self
        // The following assertion should be guaranteed by can_provide()
        assert!(self.start_addr() <= allocated_header_start);
        // TODO: this should be refactored as "set_end_addr()"?
        self.set_size_including_header(allocated_header_start - self.start_addr());

        self.next_header = Some(header_for_allocated);

        Some(allocated_payload_addr as *mut u8)
    }

    fn can_provide(&self, size_excluding_header: usize, align: usize) -> bool {
        // This check is rough - actual size needed may be smaller.
        // HEADER_SIZE * 2 => one for allocated region, another for padding.
        // TODO: this is inappropriate in the case that an allocation requests the full area of this chunk.
        // In this case, we don't need 2 headers, and we can just return the chunk itself.
        self.size >= size_excluding_header + HEADER_SIZE * 2 + align
    }

    fn size_including_header(&self) -> usize {
        self.size
    }

    fn set_size_including_header(&mut self, size: usize) {
        assert!(size >= HEADER_SIZE);
        self.size = size
    }

    fn size_excluding_header(&self) -> usize {
        self.size - HEADER_SIZE
    }

    fn start_addr(&self) -> usize {
        self as *const Header as usize
    }

    fn payload_start_addr(&self) -> usize {
        self as *const Header as usize + HEADER_SIZE
    }

    fn end_addr(&self) -> usize {
        self as *const Header as usize + self.size_including_header()
    }

    fn iter(&self) -> ChunkIterator {
        ChunkIterator {
            current: Some(self),
        }
    }

    fn hexdump(&self) {
        hexdump_bytes(unsafe {
            // TODO: safety?
            slice::from_raw_parts(
                self as *const Header as *const u8,
                self.size_including_header(),
            )
        });
    }
}

impl Drop for Header {
    fn drop(&mut self) {
        // Header prohibits being dropped, because self.next_header: Option<Box<Header>> must not be dropped.
        // Dropping Box<Header> would try to call GlobalAlloc's dealloc, but the Box for header is not allocated by GlobalAlloc.
        // TODO: should we use a different type than Box for the header list?
        // [Writing an OS in Rust](https://os.phil-opp.com/allocator-designs/#linked-list-allocator) uses &'static mut T
        // TODO: comment out this line and see what happens

        panic!("Header must not be dropped");
    }
}

impl fmt::Debug for Header {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Header @ {:#018x} {{ size_including_header: {:#018x}, is_allocated: {} }}",
            self as *const Header as usize,
            self.size_including_header(),
            self.is_allocated,
        )
    }
}

#[test_case]
/// Test the internal behavior of provide().
fn test_provide_internal() {
    let mut buf = [0u8; 1 << 16]; // 131kb
    let header = Header::new_from_slice_aligned(&mut buf, 1 << 10, 1 << 10)
        .expect("failed to create header");

    // The start of the aligned area.
    let heap_start = header.start_addr();

    println!(
        "Test header: start={:?}, end={:?}",
        header.start_addr() as *const Header,
        header.end_addr() as *const Header
    );

    dbg!(&header);

    // for h in header.iter() {
    //     println!(
    //         "{:?}:{:?} ({:#06x}:{:#06x}) (size: {:#06x}) is_allocated={}",
    //         h.start_addr() as *const Header,
    //         h.end_addr() as *const Header,
    //         h.start_addr() - heap_start,
    //         h.end_addr() - heap_start,
    //         h.size,
    //         h.is_allocated
    //     );
    // }
    // for h in header.iter() {
    //     println!("Header size={:#06x}:", h.size);
    //     h.hexdump();
    // }

    let mut header = header;

    let original_header_start = header.start_addr();
    let original_header_end = header.end_addr();
    let original_size_including_header = header.size_including_header();

    // 1. No padding

    let requested_size = 32;
    let requested_align = 32;
    let res = header.provide(requested_size, requested_align);

    let allocated1_addr = res.unwrap();

    // for h in header.iter() {
    //     println!(
    //         "{:?}:{:?} ({:#06x}:{:#06x}) (size: {:#06x}) is_allocated={}",
    //         h.start_addr() as *const Header,
    //         h.end_addr() as *const Header,
    //         h.start_addr() - heap_start,
    //         h.end_addr() - heap_start,
    //         h.size,
    //         h.is_allocated
    //     );
    // }
    // for h in header.iter() {
    //     println!("Header size={:#06x}:", h.size);
    //     h.hexdump();
    // }

    {
        let mut it = header.iter();

        let remaining = it.next().unwrap();
        let allocated = it.next().unwrap();
        assert!(it.next().is_none());

        // The original header is separated into (remaining, allocated).

        assert!(allocated.is_allocated);
        assert!(!remaining.is_allocated);

        assert_eq!(allocated1_addr as usize, allocated.payload_start_addr());
        assert_eq!(original_header_end, allocated.end_addr());
        assert_eq!(original_header_start, remaining.start_addr());
        assert_eq!(remaining.end_addr(), allocated.start_addr());

        // The header for the allocated chunk has the request size
        assert_eq!(requested_size, allocated.size_excluding_header());
        assert_eq!(
            requested_size + HEADER_SIZE,
            allocated.size_including_header()
        );

        // The header for the remaining chunk has the remaining size
        assert_eq!(
            original_size_including_header,
            allocated.size_including_header() + remaining.size_including_header()
        );
    }

    // 2. Allocation leaves padding

    // We will allocate memory of size 128(+header) with align=128.
    // Since we allocated a chunk of total size 64 in Step 1,
    // we cannot allocate the tail of the remaining chunk.

    let requested_size = 128;
    let requested_align = 128;

    let res = header.provide(requested_size, requested_align);

    let allocated2_addr = res.unwrap();

    // for h in header.iter() {
    //     println!(
    //         "{:?}:{:?} ({:#06x}:{:#06x}) (size: {:#06x}) is_allocated={}",
    //         h.start_addr() as *const Header,
    //         h.end_addr() as *const Header,
    //         h.start_addr() - heap_start,
    //         h.end_addr() - heap_start,
    //         h.size,
    //         h.is_allocated
    //     );
    // }
    // for h in header.iter() {
    //     println!("Header size={:#06x}:", h.size);
    //     h.hexdump();
    // }

    {
        let mut it = header.iter();

        let remaining = it.next().unwrap();
        let allocated2 = it.next().unwrap();
        let padding = it.next().unwrap();
        let allocated1 = it.next().unwrap();
        assert!(it.next().is_none());

        // The last chunk is the one we allocated in Step 1.
        assert_eq!(allocated1_addr as usize, allocated1.payload_start_addr());

        // The original header is separated into (remaining, allocated2, padding).
        assert!(!remaining.is_allocated);
        assert!(allocated2.is_allocated);
        assert!(!padding.is_allocated);

        assert_eq!(original_header_start, remaining.start_addr());
        assert_eq!(remaining.end_addr(), allocated2.start_addr());
        assert_eq!(allocated2.end_addr(), padding.start_addr());
        assert_eq!(padding.end_addr(), allocated1.start_addr());

        assert_eq!(allocated2_addr as usize, allocated2.payload_start_addr());

        // The header for the allocated chunk has the request size
        assert_eq!(requested_size, allocated2.size_excluding_header());

        // The header for the remaining chunk has the remaining size
        assert_eq!(
            original_size_including_header,
            remaining.size_including_header()
                + allocated2.size_including_header()
                + padding.size_including_header()
                + allocated1.size_including_header(),
        );
    }

    // Follow the requirement that header must not be dropped
    Box::leak(header);
}

struct ChunkIterator<'a> {
    current: Option<&'a Header>,
}

impl<'a> Iterator for ChunkIterator<'a> {
    type Item = &'a Header;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(next) = self.current.and_then(|h| h.next_header.as_ref()) {
            self.current.replace(next.as_ref())
        } else {
            self.current.take()
        }
    }
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

#[cfg(test)]
mod tests {
    use core::{alloc::Layout, ptr::null};

    use super::*;
    use alloc::vec;

    // Currently this test fails, because can_provide() is too conservative.
    // #[test_case]
    fn _malloc_max() {
        const HEAP_SIZE: usize = 1 << 8;

        let mut buf = [0u8; HEAP_SIZE << 1];
        let mut header = Header::new_from_slice_aligned(&mut buf, HEAP_SIZE, HEAP_SIZE)
            .expect("failed to create header");

        // The start of the aligned area.
        let heap_start = header.start_addr();

        let requested_size = HEAP_SIZE - HEADER_SIZE;
        let requested_align = 1;
        let res = header.provide(requested_size, requested_align).unwrap();
        dbg!(&res);
    }

    /// Repeatedly alloc and free, and check if something bad happens
    #[test_case]
    fn malloc_iterate_free_and_alloc() {
        use alloc::vec::Vec;
        let mut vec = Vec::new();
        for i in 0..1000 {
            vec.resize(i, 10);
        }
    }

    /// Test if the allocated area is aligned as requested
    #[test_case]
    fn malloc_align() {
        // TODO: why does this test store the pointers?
        let mut pointers = [null_mut(); 1];
        for align in [1, 2, 4, 8, 16, 32, 4096] {
            for e in pointers.iter_mut() {
                *e = ALLOCATOR.alloc_with_options(Layout::from_size_align(1234, align).unwrap());
                assert_ne!(0, *e as usize);
                assert_eq!(0, (*e as usize) % align);
            }
        }
    }

    /// Test if the allocated area is aligned as requested
    /// (using an align randomly ordered)
    #[test_case]
    fn malloc_align_random_order() {
        for align in [32, 4096, 8, 4, 16, 2, 1] {
            let mut pointers = [null_mut(); 1];
            for e in pointers.iter_mut() {
                *e = ALLOCATOR.alloc_with_options(Layout::from_size_align(1234, align).unwrap());
                assert_ne!(0, *e as usize);
                assert_eq!(0, (*e as usize) % align);
            }
        }
    }

    #[test_case]
    fn allocated_objects_have_no_overlap() {
        let allocations = [
            Layout::from_size_align(128, 128).unwrap(),
            Layout::from_size_align(32, 32).unwrap(),
            Layout::from_size_align(8, 8).unwrap(),
            Layout::from_size_align(16, 16).unwrap(),
            Layout::from_size_align(6000, 64).unwrap(),
            Layout::from_size_align(4, 4).unwrap(),
            Layout::from_size_align(2, 2).unwrap(),
            Layout::from_size_align(600000, 64).unwrap(),
            Layout::from_size_align(64, 64).unwrap(),
            Layout::from_size_align(1, 1).unwrap(),
            Layout::from_size_align(6000, 64).unwrap(),
            Layout::from_size_align(6000, 64).unwrap(),
            Layout::from_size_align(6000, 64).unwrap(),
            Layout::from_size_align(6000, 64).unwrap(),
            Layout::from_size_align(6000, 64).unwrap(),
            Layout::from_size_align(6000, 64).unwrap(),
            Layout::from_size_align(3, 64).unwrap(),
            Layout::from_size_align(3, 64).unwrap(),
            Layout::from_size_align(3, 64).unwrap(),
            Layout::from_size_align(3, 64).unwrap(),
            Layout::from_size_align(3, 64).unwrap(),
            Layout::from_size_align(3, 64).unwrap(),
            Layout::from_size_align(3, 64).unwrap(),
            Layout::from_size_align(3, 64).unwrap(),
            Layout::from_size_align(3, 64).unwrap(),
            Layout::from_size_align(3, 64).unwrap(),
            Layout::from_size_align(6000, 64).unwrap(),
            Layout::from_size_align(6000, 64).unwrap(),
            Layout::from_size_align(600000, 64).unwrap(),
            Layout::from_size_align(6000, 64).unwrap(),
            Layout::from_size_align(60000, 64).unwrap(),
            Layout::from_size_align(60000, 64).unwrap(),
            Layout::from_size_align(60000, 64).unwrap(),
            Layout::from_size_align(60000, 64).unwrap(),
        ];
        let mut pointers = vec![null_mut(); allocations.len()];
        for (i, (layout, pointer)) in allocations.iter().zip(pointers.iter_mut()).enumerate() {
            *pointer = ALLOCATOR.alloc_with_options(*layout);
            for k in 0..layout.size() {
                // Mark the allocated area to be granted to this entry
                unsafe { *pointer.add(k) = i as u8 }
            }
        }
        for (i, (layout, pointer)) in allocations.iter().zip(pointers.iter()).enumerate() {
            for k in 0..layout.size() {
                // Check if nobody overwrote the "granted area"
                assert_eq!(i as u8, unsafe { *pointer.add(k) });
            }
        }

        // Deallocate entries of even index
        for (i, (layout, pointer)) in allocations
            .iter()
            .zip(pointers.iter())
            .enumerate()
            .step_by(2)
        {
            unsafe {
                ALLOCATOR.dealloc(*pointer, *layout);
            }
        }

        // Check integrity of entries of odd index
        for (i, (layout, pointer)) in allocations
            .iter()
            .zip(pointers.iter())
            .enumerate()
            .skip(1)
            .step_by(2)
        {
            for k in 0..layout.size() {
                // Check if nobody overwrote the "granted area"
                assert_eq!(i as u8, unsafe { *pointer.add(k) });
            }
        }

        // Reallocate entries of even index
        for (i, (layout, pointer)) in allocations
            .iter()
            .zip(pointers.iter_mut())
            .enumerate()
            .step_by(2)
        {
            *pointer = ALLOCATOR.alloc_with_options(*layout);
            for k in 0..layout.size() {
                // Mark the allocated area to be granted to this entry
                unsafe { *pointer.add(k) = i as u8 }
            }
        }

        // Check integrity again
        for (i, (layout, pointer)) in allocations.iter().zip(pointers.iter()).enumerate() {
            for k in 0..layout.size() {
                // Check if nobody overwrote the "granted area"
                assert_eq!(i as u8, unsafe { *pointer.add(k) });
            }
        }
    }
}
