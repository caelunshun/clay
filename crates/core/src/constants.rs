pub mod runtime {
    /// Number of upper bits reserved in reference addresses
    /// to store the byte offset of the pointer from the start
    /// of its owning GC allocation.
    /// (All ones in the upper bits indicates the offset needs
    /// to be computed by checking the GC card tables instead.)
    /// This leaves 44 bits for the address
    /// so can address 16 TiB of memory... probably enough.
    pub const TAGGED_REFERENCE_RESERVED_BITS: u32 = 20;
}
