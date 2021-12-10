mod compressor;
mod decompress;
mod sys;

pub use compressor::*;
pub use decompress::*;

use std::num::{NonZeroU32, NonZeroU64};

/// Calculates the number of blocks (and size thereof) an `uncompressed_size` length buffer needs to be split into
/// in order for each one to be smaller than the max input size of the LZ4 block compression algorithm (~1.9 Gb).
///
/// Returns the tuple `(num_blocks, block_size)`.
/// If `num_blocks == 1`, `block_size == uncompressed_size`.
/// Otherwise if `num_blocks > 1`, `block_size` is the size of all blocks except the last one, which might be smaller
/// (`uncompressed_size - block_size * (num_blocks - 1)`).
fn calc_num_blocks_and_block_size(uncompressed_size: NonZeroU64) -> (NonZeroU32, NonZeroU32) {
    debug_assert!(sys::LZ4_MAX_INPUT_SIZE > 0);
    let max_block_size = unsafe { NonZeroU32::new_unchecked(sys::LZ4_MAX_INPUT_SIZE as _) };

    // Align the block size up to max LZ4 history size value (64 Kb).
    let block_alignment = unsafe { NonZeroU32::new_unchecked(64 * 1024) };

    calc_num_blocks_and_block_size_impl(uncompressed_size, max_block_size, block_alignment)
}

/// The caller gurarantees `max_block_size` is less or equal to `LZ4_MAX_INPUT_SIZE`.
/// The caller guarantees `max_block_size` is not too small and the calculated number of blocks fits into a `u32` (usually `max_block_size` == ~1.9 Gb).
/// The caller guarantees `block_alignment` is less or equal to `max_block_size` (usually `block_alignment` == 64 Kb).
fn calc_num_blocks_and_block_size_impl(
    uncompressed_size: NonZeroU64,
    max_block_size: NonZeroU32,
    block_alignment: NonZeroU32,
) -> (NonZeroU32, NonZeroU32) {
    let max_block_size = max_block_size.get();
    debug_assert!(
        max_block_size <= sys::LZ4_MAX_INPUT_SIZE as _,
        "maximum size of LZ4 input exceeded"
    );

    let num_blocks = divide_round_up(uncompressed_size.get(), max_block_size as _);

    debug_assert!(num_blocks > 0);
    debug_assert!(
        num_blocks <= u32::MAX as _,
        "number of blocks overflow - `max_uncompressed_size` too small?"
    );

    // Guaranteed to be less or equal to `max_block_size`.
    let block_size = divide_round_up(uncompressed_size.get(), num_blocks);
    debug_assert!(block_size > 0);
    debug_assert!(block_size <= max_block_size as _);
    let mut block_size = block_size as u32;

    // Align up if we have more than one block.
    // Guaranteed to be less or equal to `max_block_size`.
    if num_blocks > 1 {
        let block_alignment = block_alignment.get();
        debug_assert!(
            block_alignment <= max_block_size,
            "block alignment must be less or equal to max block size"
        );

        block_size = divide_round_up_u32(block_size, block_alignment) * block_alignment;

        debug_assert!(block_size > 0);
        debug_assert!(block_size <= max_block_size);
    }

    unsafe {
        (
            NonZeroU32::new_unchecked(num_blocks as _),
            NonZeroU32::new_unchecked(block_size),
        )
    }
}

fn divide_round_up(a: u64, b: u64) -> u64 {
    (a + b - 1) / b
}

fn divide_round_up_u32(a: u32, b: u32) -> u32 {
    (a + b - 1) / b
}
