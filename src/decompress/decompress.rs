use {
    crate::{sys::*, *},
    std::{
        mem::size_of,
        num::{NonZeroU32, NonZeroU64},
    },
};

/// A single byte is compressed to two bytes by LZ4
/// (1 byte for the op ("a run of a single literal") + 1 byte for the literal itself).
const MIN_COMPRESSED_BLOCK_SIZE: u64 = 2;

/// Tries to decompress the (non-empty) `src` buffer, filled by the [`Compressor`],
/// into the pre-allocated `dst` buffer, which must be exactly equal to the original, uncompressed size of the `src` data.
///
/// On success fills the `dst` buffer with the decompressed data.
///
/// # Errors
///
/// Returns [`EmptyInput`] if the `src` buffer is empty.
/// Returns [`EmptyOutput`] if the `dst` buffer is empty.
/// Returns [`DecompressionError`] if the LZ4 decompression failed for some reason - e.g.
/// if `src` buffer is not a valid LZ4-compressed buffer returned by [`Compressor::compress()`],
/// or if `dst` buffer size is not exactly equal to the original, uncompressed size of the `src` data.
///
/// # Safety
///
/// The function effectively relies entirely on the C LZ4 library to gracefully handle garbage/malicious inputs.
///
/// [`EmptyInput`]: enum.DecompressionError.html#variant.EmptyInput
/// [`EmptyOutput`]: enum.DecompressionError.html#variant.EmptyOutput
/// [`DecompressionError`]: enum.DecompressionError.html#variant.DecompressionError
pub fn decompress(src: &[u8], dst: &mut [u8]) -> Result<(), DecompressionError> {
    // Output must be non-empty.
    let dst_size = NonZeroU64::new(dst.len() as _).ok_or(DecompressionError::EmptyOutput)?;
    decompess_impl(src, dst, dst_size)
}

/// Tries to decompress the (non-empty) `src` buffer, filled by the [`Compressor`] into a `Vec<u8>`.
/// `uncompressed_size` must be exactly equal to the original, uncompressed size of the `src` data.
///
/// On success the returned vector is guaranteed to be exactly `uncompressed_size` bytes long.
///
/// # Errors
///
/// Returns [`EmptyInput`] if the `src` buffer is empty.
/// Returns [`DecompressionError`] if the LZ4 decompression failed for some reason - e.g.
/// if `src` buffer is not a valid LZ4-compressed buffer returned by [`Compressor::compress()`],
/// or if `uncompressed_size` is not exactly equal to the original, uncompressed size of the `src` data.
///
/// # Safety
///
/// The function effectively relies entirely on the C LZ4 library to gracefully handle garbage/malicious inputs.
///
/// [`EmptyInput`]: enum.DecompressionError.html#variant.EmptyInput
/// [`EmptyOutput`]: enum.DecompressionError.html#variant.EmptyOutput
/// [`DecompressionError`]: enum.DecompressionError.html#variant.DecompressionError
pub fn decompress_to_vec(
    src: &[u8],
    uncompressed_size: NonZeroU64,
) -> Result<Vec<u8>, DecompressionError> {
    let mut dst = Vec::with_capacity(uncompressed_size.get() as _);
    unsafe { dst.set_len(uncompressed_size.get() as _) };
    decompess_impl(src, &mut dst, uncompressed_size)?;
    Ok(dst)
}

/// The caller guarantees `dst.len() as u64 == dst_size.get()`.
fn decompess_impl(
    src: &[u8],
    dst: &mut [u8],
    dst_size: NonZeroU64,
) -> Result<(), DecompressionError> {
    debug_assert_eq!(dst.len() as u64, dst_size.get());

    // Input must be non-empty.
    if src.is_empty() {
        return Err(DecompressionError::EmptyInput);
    }

    // Subdivide the decompressed output into sub-blocks.
    let (num_blocks, block_size) = calc_num_blocks_and_block_size(dst_size);

    // Usual case - decompressed output is smaller than max LZ4 input size (~1.9 Gb).
    if num_blocks.get() == 1 {
        // We consider the decompression succesful if we decompressed exactly `dst_size` bytes.
        if decompress_block(src, dst)
            .ok_or(DecompressionError::DecompressionError)?
            .get() as u64
            == dst_size.get()
        {
            Ok(())
        } else {
            Err(DecompressionError::DecompressionError)
        }

    // Rare case - decompressed output is large and must be subdivided into sub-blocks.
    } else {
        decompress_blocks(src, dst, num_blocks, block_size)
    }
}

/// Tries to decompress the `src` buffer as a single block into the `dst` buffer.
/// On success returns the (non-zero) number of bytes written to `dst`.
///
/// The call can fail if `dst` buffer is not large enough, or if the LZ4 decompression itself fails
/// (e.g. the `src` buffer does not contain valid LZ4-compressed data).
///
/// The caller guarantees the `src` and `dst` buffers are not empty.
pub(crate) fn decompress_block(src: &[u8], dst: &mut [u8]) -> Option<NonZeroU32> {
    debug_assert!(!src.is_empty());
    debug_assert!(!dst.is_empty());

    let decompressed_size = unsafe {
        LZ4_decompress_safe(
            src.as_ptr() as _,
            dst.as_mut_ptr() as _,
            src.len() as _,
            dst.len() as _,
        )
    };

    // Decompression failed.
    if decompressed_size <= 0 {
        None

    // Otherwise decompression succeeded. `decompressed_size` might or might not be larger than `compressed` size.
    } else {
        debug_assert!(decompressed_size > 0);
        debug_assert!(decompressed_size as usize <= dst.len());
        Some(unsafe { NonZeroU32::new_unchecked(decompressed_size as u32) })
    }
}

/// Pops four bytes off `src` and reads them as a (little-endian) `u32`.
/// Returns the read `u32` and the rest of `src`.
///
/// Must match with `write_u32()`.
///
/// The caller guarantees that `src > std::mem::size_of::<u32>()`.
fn read_u32(src: &[u8]) -> (u32, &[u8]) {
    debug_assert!(src.len() > std::mem::size_of::<u32>());
    if let [b0, b1, b2, b3, src @ ..] = src {
        (u32::from_le_bytes([*b0, *b1, *b2, *b3]), src)
    } else {
        unsafe { std::hint::unreachable_unchecked() }
    }
}

/// Tries to decompress the `src` buffer as `num_blocks` blocks (of `block_size` uncompressed size) into the `dst` buffer,
/// reading each sub-block's compressed size as a (little-endian) `u32` right before it.
///
/// The call can fail if `dst` buffer is not large enough, or if the LZ4 decompression itself fails
/// (e.g. the `src` buffer does not contain valid LZ4-compressed data).
///
/// The caller guarantees the `src` and `dst` buffers are not empty.
/// The caller guarantees that `num_blocks > 1`.
#[cold]
pub(crate) fn decompress_blocks(
    mut src: &[u8],
    mut dst: &mut [u8],
    num_blocks: NonZeroU32,
    block_size: NonZeroU32,
) -> Result<(), DecompressionError> {
    debug_assert!(!src.is_empty());
    debug_assert!(!dst.is_empty());

    let mut num_blocks = num_blocks.get();
    debug_assert!(num_blocks > 1);

    // Calculates the minimum possible size in bytes of a valid compressed source buffer with `num_blocks` sub-blocks.
    let calc_min_size_for_blocks = |num_blocks: u32| -> u64 {
        num_blocks as u64 * (size_of::<u32>() as u64 + MIN_COMPRESSED_BLOCK_SIZE)
    };

    let compressed_size = src.len() as u64;

    // Error out if the `src` buffer is not large enough to contain `num_blocks` valid compressed blocks.
    if compressed_size < calc_min_size_for_blocks(num_blocks) {
        return Err(DecompressionError::DecompressionError);
    }

    let dst_len = dst.len() as u64;

    let mut actual_decompressed_size: u64 = 0;

    while num_blocks > 0 {
        let last = num_blocks == 1;
        num_blocks -= 1;

        // Read and pop off the compressed block size.
        // We've ensured there's enough data in the `src` buffer.
        let (compressed_block_size, src_) = read_u32(src);
        src = src_;

        // Compressed block size must be non-zero.
        if compressed_block_size == 0 {
            return Err(DecompressionError::DecompressionError);
        }

        // Error out if the read compressed block size does not leave the minimum required space in the source buffer
        // for the remaining blocks, if there are any.
        let remaining = src.len() as u64;
        if num_blocks > 0 {
            let min_size_for_remaining_blocks = calc_min_size_for_blocks(num_blocks);
            debug_assert!(remaining >= min_size_for_remaining_blocks);
            let max_compressed_block_size = remaining - min_size_for_remaining_blocks;

            if compressed_block_size as u64 > max_compressed_block_size {
                return Err(DecompressionError::DecompressionError);
            }
        // Otherwise, if it's the last block, error out if the read compressed block size
        // does not equal the actual remaining source buffer size.
        } else if compressed_block_size as u64 != remaining {
            return Err(DecompressionError::DecompressionError);
        }

        // Try to decompress the block.
        // Rely on LZ4 to error out safely in case it's passed garbage.
        let decompressed_block_size = decompress_block(
            unsafe { src.get_unchecked(..compressed_block_size as usize) },
            dst,
        )
        .ok_or(DecompressionError::DecompressionError)?;

        // Error out if the decompressed block size does not equal the `block_size` value calculated from `dst` size ...
        if !last {
            if decompressed_block_size != block_size {
                return Err(DecompressionError::DecompressionError);
            }
        // ... (unless it's the last block, which may be smaller).
        } else {
            if decompressed_block_size > block_size {
                return Err(DecompressionError::DecompressionError);
            }
        }

        // Accumulate the decompressed size, step to the next source and setination blocks.
        actual_decompressed_size += decompressed_block_size.get() as u64;

        src = unsafe { src.get_unchecked(compressed_block_size as usize..) };
        dst = unsafe { dst.get_unchecked_mut(decompressed_block_size.get() as usize..) };
    }

    // Error out if we somehow decompressed a different number of bytes
    // then the destination buffer size / expected uncompressed size.
    if actual_decompressed_size == dst_len {
        Ok(())
    } else {
        Err(DecompressionError::DecompressionError)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn min_compressed_block_size() {
        let src: &[u8] = &[7];
        let src_compressed = Compressor::new().unwrap().compress_to_vec(src).unwrap();
        assert!(src_compressed.len() as u64 >= MIN_COMPRESSED_BLOCK_SIZE);
    }

    #[test]
    #[allow(non_snake_case)]
    fn EmptyInput() {
        let mut dst = [0];
        assert_eq!(
            decompress(&[], &mut dst).err().unwrap(),
            DecompressionError::EmptyInput
        )
    }

    #[test]
    #[allow(non_snake_case)]
    fn EmptyOutput() {
        let mut dst = [];
        assert_eq!(
            decompress(&[0], &mut dst).err().unwrap(),
            DecompressionError::EmptyOutput
        )
    }

    #[test]
    #[allow(non_snake_case)]
    fn DecompressionError() {
        let src = [
            b'0', 1, 2, 3, 4, 5, 6, 7, 8, 9, b'a', b'b', b'c', b'd', b'e', b'f',
        ];
        let mut dst = [0];
        assert_eq!(
            decompress(&src, &mut dst).err().unwrap(),
            DecompressionError::DecompressionError
        )
    }
}
