use {
    crate::{sys::*, *},
    libc::c_int,
    std::{
        mem::size_of,
        num::{NonZeroU32, NonZeroU64},
        ptr::NonNull,
    },
};

/// Configures the hardcoded LZ4 compression level we use.
/// Using the max level for now.
const COMPRESSION_LEVEL: c_int = LZ4HC_CLEVEL_MAX;

/// Provides an API to compress byte slices into a preallocated buffer
/// and to report the minimum output buffer size required to successfully compress the given input.
///
/// A compressor instance may be reused to compress multiple inputs.
///
/// Compressed data does not keep track of its original uncompressed size, or its compressed size;
/// this data needs to be kept track of separately.
///
/// NOTE: the produced compressed data is meant to be decompressed only with [`decompress()`] / [`decompress_to_vec`]
/// and is not meant to be passed to any other LZ4 decompression implementations.
///
/// # Implementation details
///
/// Internally this uses the LZ4 HC block compression API, with maximum compression level (12).
/// Supports compressing input byte slices larger than maximum LZ4 block compression input size (`LZ4_MAX_INPUT_SIZE`, ~1.9 Gb) by
/// subdividing the input block into sub-blocks and prepending the compressed block sizes, if necessary.
pub struct Compressor {
    state: NonNull<LZ4_streamHC_t>,
}

impl Drop for Compressor {
    fn drop(&mut self) {
        unsafe { LZ4_freeStreamHC(self.state.as_ptr()) }
    }
}

impl Compressor {
    /// Creates a new compressor instance.
    /// A compressor instance may be reused to compress multiple inputs.
    ///
    /// # Errors
    ///
    /// May fail with an [`out of memory`](CompressorError::OutOfMemory) error if failed to allocate the compression context.
    pub fn new() -> Result<Self, CompressorError> {
        Ok(Self {
            state: NonNull::new(unsafe { LZ4_createStreamHC() })
                .ok_or(CompressorError::OutOfMemory)?,
        })
    }

    /// Given the non-empty input buffer of `uncompressed_size`, returns the minimum output buffer size
    /// required to successfully compress the input.
    pub fn compressed_size_bound(uncompressed_size: NonZeroU64) -> NonZeroU64 {
        let (num_blocks, block_size) = calc_num_blocks_and_block_size(uncompressed_size);
        Self::compressed_size_bound_impl(uncompressed_size, num_blocks, block_size)
    }

    /// Tries to compress the (non-empty) `src` buffer into the pre-allocated `dst` buffer,
    /// which must be at least as large as the return value of [`Self::compressed_size_bound()`] given the `src` buffer's size.
    ///
    /// On success returns the number of bytes written to the `dst` buffer.
    ///
    /// Created compressed buffer does not keep track of its original uncompressed size, so that information must be stored separately.
    ///
    /// NOTE: the produced compressed data is meant to be decompressed only with [`decompress()`] / [`decompress_to_vec`]
    /// and is not meant to be passed to any other LZ4 decompression implementations.
    ///
    /// # Errors
    ///
    /// - Returns [`EmptyInput`](CompressorError::EmptyInput) if the `src` buffer is empty.
    /// - Returns [`InsufficientSpace`](CompressorError::InsufficientSpace) if the `dst` buffer is not large enough
    /// (i.e. it is smaller than the return value of [`Self::compressed_size_bound()`] for `src` size).
    /// - Returns [`CompressionError`](CompressorError::CompressionError) if the LZ4 compression failed for some reason.
    pub fn compress(&mut self, src: &[u8], dst: &mut [u8]) -> Result<NonZeroU64, CompressorError> {
        // Input must be non-empty.
        let uncompressed_size =
            NonZeroU64::new(src.len() as _).ok_or_else(|| CompressorError::EmptyInput)?;
        let (num_blocks, block_size) = calc_num_blocks_and_block_size(uncompressed_size);
        self.compress_impl(src, uncompressed_size, dst, num_blocks, block_size)
    }

    /// Tries to compress the (non-empty) `src` buffer into a `Vec<u8>`.
    ///
    /// Created compressed buffer does not keep track of its original uncompressed size, so that information must be stored separately.
    ///
    /// NOTE: the produced compressed data is meant to be decompressed only with [`decompress()`] / [`decompress_to_vec`]
    /// and is not meant to be passed to any other LZ4 decompression implementations.
    ///
    /// # Errors
    ///
    /// - Returns [`EmptyInput`](CompressorError::EmptyInput) if the `src` buffer is empty.
    /// - Returns [`CompressionError`](CompressorError::CompressionError) if the LZ4 compression failed for some reason.
    pub fn compress_to_vec(&mut self, src: &[u8]) -> Result<Vec<u8>, CompressorError> {
        // Input must be non-empty.
        let mut dst = vec![
            0;
            Self::compressed_size_bound(
                NonZeroU64::new(src.len() as _).ok_or(CompressorError::EmptyInput)?
            )
            .get() as _
        ];
        let compressed_size = self.compress(src, &mut dst)?;
        unsafe {
            dst.set_len(compressed_size.get() as _);
        }
        dst.shrink_to_fit();
        Ok(dst)
    }

    /// Compresses the `src` buffer as a single block into the `dst` buffer.
    ///
    /// The caller guarantees the `src` buffer is not empty and its size is less than or equal to `LZ4_MAX_INPUT_SIZE`.
    /// The caller guarantees the `dst` output buffer is large enough.
    /// The call can only fail if the LZ4 compression itself fails for some reason.
    fn compress_block(&mut self, src: &[u8], dst: &mut [u8]) -> Option<NonZeroU32> {
        debug_assert!(src.len() > 0);
        debug_assert!(src.len() <= LZ4_MAX_INPUT_SIZE as _);
        debug_assert!(
            dst.len()
                >= Self::compressed_size_bound(unsafe { NonZeroU64::new_unchecked(src.len() as _) })
                    .get() as _
        );

        let compressed_size = unsafe {
            LZ4_compress_HC_extStateHC_fastReset(
                self.state.as_ptr() as _,
                src.as_ptr() as _,
                dst.as_mut_ptr() as _,
                src.len() as _,
                dst.len() as _,
                COMPRESSION_LEVEL,
            )
        };

        // Compression failed for some reason.
        if compressed_size <= 0 {
            // Must reset the LZ4 state in case of error so that the compressor instance could be reused.
            unsafe { LZ4_resetStreamHC_fast(self.state.as_ptr() as _, COMPRESSION_LEVEL) };

            None

        // Otherwise compression succeeded. `compressed_size` might or might not be smaller than `uncompressed` size.
        } else {
            debug_assert!(compressed_size > 0);
            debug_assert!(compressed_size as usize <= dst.len());

            Some(unsafe { NonZeroU32::new_unchecked(compressed_size as _) })
        }
    }

    /// Compresses the `src` buffer as `num_blocks > 1` `block_size`-sized blocks into the `dst` buffer,
    /// prepending each block's compressed size as a little-endian `u32` right before it.
    ///
    /// The caller guarantees that the `src` buffer is not empty.
    /// The caller guarantees that `num_blocks > 1`.
    /// The caller guarantees that `num_blocks` and `block_size` are calculated for `src` size.
    /// The caller guarantees the `dst` buffer is large enough.
    /// The call can only fail if the LZ4 compression itself fails for some reason.
    #[cold]
    fn compress_blocks(
        &mut self,
        mut src: &[u8],
        num_blocks: NonZeroU32,
        block_size: NonZeroU32,
        mut dst: &mut [u8],
    ) -> Option<NonZeroU64> {
        debug_assert!(src.len() > 0);
        debug_assert!(num_blocks.get() > 1);
        debug_assert!(num_blocks.get() as usize * block_size.get() as usize >= src.len());
        debug_assert!(
            dst.len()
                >= Self::compressed_size_bound_impl(
                    unsafe { NonZeroU64::new_unchecked(src.len() as _) },
                    num_blocks,
                    block_size
                )
                .get() as _
        );

        let uncompressed_size = src.len() as u64;
        let num_blocks = num_blocks.get();
        let block_size = block_size.get() as u64;

        let mut remaining = uncompressed_size;
        // Total compressed size, including the prepended blocks' compressed size.
        let mut compressed_size: u64 = 0;

        for _ in 0..num_blocks {
            // Last block may be smaller than `block_size`.
            let block_size = (block_size as u64).min(remaining);
            debug_assert!(remaining >= block_size);
            remaining -= block_size;

            // Pop off the source block.
            // Safe because the caller guarantees that `num_blocks` and `block_size` correspond to the `src` buffer.
            let (src_block, src_) = split(src, block_size as _);
            src = src_;

            // We'll write the block's compressed size here, the block's compressed data follows.
            let (block_size_dst, dst_) = split_mut(dst, std::mem::size_of::<u32>());
            dst = dst_;

            // Compress the block.
            let compressed_block_size = self.compress_block(src_block, dst)?;
            compressed_size += compressed_block_size.get() as u64;

            debug_assert!(compressed_block_size.get() as usize <= dst.len());

            // Prepend the compressed block size.
            write_u32(block_size_dst, compressed_block_size);
            compressed_size += size_of::<u32>() as u64;

            // Pop off the compressed block.
            // Safe because the caller guarantees the `dst` buffer is large enough to compress all the blocks,
            // and LZ4 guarantees it will not use more memory than the calculated bound.
            let (_, dst_) = split_mut(dst, compressed_block_size.get() as _);
            dst = dst_;
        }

        debug_assert_eq!(remaining, 0);

        debug_assert!(compressed_size > 0);
        Some(unsafe { NonZeroU64::new_unchecked(compressed_size) })
    }

    /// If `num_blocks > 1`, additionally reserves space for little-endian `u32` compressed block sizes, prepended before each compressed block.
    ///
    /// The caller guarantees `num_blocks * block_size >= src_size`.
    fn compressed_size_bound_impl(
        src_size: NonZeroU64,
        num_blocks: NonZeroU32,
        block_size: NonZeroU32,
    ) -> NonZeroU64 {
        let num_blocks = num_blocks.get();
        let block_size = block_size.get() as u64;
        let mut remaining = src_size.get();

        debug_assert!(num_blocks as u64 * block_size >= remaining);

        let mut bound = 0;

        for _ in 0..num_blocks {
            let cur_block_size = block_size.min(remaining);
            let cur_block_bound = LZ4_COMPRESSBOUND(cur_block_size as _);
            debug_assert!(cur_block_bound > 0);
            bound += cur_block_bound as u64;
            debug_assert!(remaining >= cur_block_size);
            remaining -= cur_block_size;
        }

        debug_assert_eq!(remaining, 0);

        if num_blocks > 1 {
            bound += num_blocks as u64 * size_of::<u32>() as u64;
        }

        debug_assert!(bound > 0);
        unsafe { NonZeroU64::new_unchecked(bound) }
    }

    /// The caller guarantees the `src` buffer is not empty and that `src_size == src.len()`.
    fn compress_impl(
        &mut self,
        src: &[u8],
        src_size: NonZeroU64,
        dst: &mut [u8],
        num_blocks: NonZeroU32,
        block_size: NonZeroU32,
    ) -> Result<NonZeroU64, CompressorError> {
        debug_assert!(src.len() > 0);
        debug_assert!(src_size.get() == src.len() as _);

        if (dst.len() as u64)
            < Self::compressed_size_bound_impl(src_size, num_blocks, block_size).get()
        {
            return Err(CompressorError::InsufficientSpace);
        }

        {
            // Usual case - input is smaller than max block size (max LZ4 input size (~1.9 Gb)) and will be compressed as a single block.
            if num_blocks.get() == 1 {
                self.compress_block(src, dst).map(|compressed_size| unsafe {
                    NonZeroU64::new_unchecked(compressed_size.get() as u64)
                })

            // Rare case - input is larger than max block size and must be subdivided into sub-blocks, compressed individually.
            } else {
                self.compress_blocks(src, num_blocks, block_size, dst)
            }
        }
        .ok_or(CompressorError::CompressionError)
    }
}

/// Must match with `read_u32()`.
///
/// The caller guarantees `dst` is at least large enough for a `u32`.
fn write_u32(dst: &mut [u8], val: NonZeroU32) {
    debug_assert!(dst.len() >= size_of::<u32>());

    for (i, &byte) in val.get().to_le_bytes().iter().enumerate() {
        unsafe { *dst.get_unchecked_mut(i) = byte };
    }
}

/// Returns the left and right subslices of `src` split at `mid`, left exclusive, right inclusive.
///
/// The caller guarantees that `mid <= src.len()`.
fn split(src: &[u8], mid: usize) -> (&[u8], &[u8]) {
    debug_assert!(mid <= src.len());
    unsafe { (src.get_unchecked(..mid), src.get_unchecked(mid..)) }
}

/// Returns the left and right mutable subslices of `src` split at `mid`, left exclusive, right inclusive.
///
/// The caller guarantees that `mid <= src.len()`.
fn split_mut(src: &mut [u8], mid: usize) -> (&mut [u8], &mut [u8]) {
    debug_assert!(mid <= src.len());
    let ptr = src.as_mut_ptr();
    unsafe {
        (
            std::slice::from_raw_parts_mut(ptr, mid),
            std::slice::from_raw_parts_mut(ptr.add(mid), src.len() - mid),
        )
    }
}

#[cfg(test)]
mod tests {
    use {super::*, crate::decompress::decompress_blocks};

    #[test]
    #[allow(non_snake_case)]
    fn EmptyInput() {
        let mut compressor = Compressor::new().unwrap();
        let mut dst = Vec::new();
        assert_eq!(
            compressor.compress(&[], &mut dst).err().unwrap(),
            CompressorError::EmptyInput
        );
    }

    #[test]
    #[allow(non_snake_case)]
    fn InsufficientSpace() {
        let mut compressor = Compressor::new().unwrap();
        let mut dst = vec![0; 8];
        assert_eq!(
            compressor.compress(&[0; 8], &mut dst).err().unwrap(),
            CompressorError::InsufficientSpace
        );
    }

    fn read_file_to_vec(file_name: &str) -> Vec<u8> {
        use std::io::Read;

        let root_path = std::env::current_dir().unwrap();
        let file_path = root_path.join(file_name);

        let mut file =
            std::fs::File::open(&file_path).expect(&format!("failed to open \"{}\"", file_name));
        let mut file_data = Vec::new();
        let original_size = file
            .read_to_end(&mut file_data)
            .expect(&format!("failed to read \"{}\"", file_name));
        assert_eq!(original_size, file_data.len());
        assert!(original_size > 0, "failed to read \"{}\"", file_name);

        file_data
    }

    /*
    fn write_slice_to_file(file_name: &str, data: &[u8]) {
        use std::io::Write;

        let root_path = std::env::current_dir().unwrap();
        let file_path = root_path.join(file_name);

        let mut file =
            std::fs::File::create(&file_path).expect(&format!("failed to open \"{}\"", file_name));
        file.write_all(&data)
            .expect(&format!("failed to write \"{}\"", file_name));
    }
    */

    #[test]
    fn single_block() {
        let single_block_impl = |file_name: &str| {
            // Read the data from file.
            let original_data = read_file_to_vec(file_name);
            let original_size = original_data.len();
            assert!(original_size < LZ4_MAX_INPUT_SIZE as _);

            // Compress as a singe block.
            let mut compressor = Compressor::new().unwrap();

            let compressed_data = compressor
                .compress_to_vec(&original_data)
                .expect(&format!("failed to compress {}", file_name));
            /*
            let compressed_size = compressed_data.len();

            // Write the compressed data to file.
            let compressed_suffix = ".compressed";
            let mut compressed_file_name = file_name.to_string();
            compressed_file_name.push_str(compressed_suffix);
            write_slice_to_file(&compressed_file_name, &compressed_data);

            // Read the compressed data back from the file.
            let compressed_data = read_file_to_vec(&compressed_file_name);
            assert_eq!(compressed_data.len(), compressed_size as _);
            */

            // Uncompress the data and compare to the original.
            let decompressed_data = decompress_to_vec(
                &compressed_data,
                NonZeroU64::new(original_size as _).unwrap(),
            )
            .unwrap();

            assert_eq!(decompressed_data, original_data);
        };

        for file_name in ["goldhill.bmp", "sails.bmp"] {
            single_block_impl(file_name);
        }
    }

    #[test]
    fn multiple_blocks() {
        let multiple_blocks_impl = |file_name: &str| {
            // Read the data from file.
            let original_data = read_file_to_vec(file_name);
            let original_size = original_data.len();
            assert!(original_size < LZ4_MAX_INPUT_SIZE as _);

            // Compress as multiple blocks.
            let mut compressor = Compressor::new().unwrap();

            let uncompressed_size = NonZeroU64::new(original_size as u64).unwrap();

            let max_block_size = unsafe { NonZeroU32::new_unchecked(64 * 1024) };
            let block_alignment = unsafe { NonZeroU32::new_unchecked(4 * 1024) };

            let (num_blocks, block_size) = calc_num_blocks_and_block_size_impl(
                uncompressed_size,
                max_block_size,
                block_alignment,
            );

            let compressed_bound =
                Compressor::compressed_size_bound_impl(uncompressed_size, num_blocks, block_size);

            let mut compressed_data = vec![0; compressed_bound.get() as _];
            let compressed_size = compressor
                .compress_impl(
                    &original_data,
                    uncompressed_size,
                    &mut compressed_data,
                    num_blocks,
                    block_size,
                )
                .expect("failed to compress");
            unsafe { compressed_data.set_len(compressed_size.get() as _) };

            // Uncompress the data and compare to the original.
            let mut decompressed_data = vec![0; original_size];
            decompress_blocks(
                &compressed_data,
                &mut decompressed_data,
                num_blocks,
                block_size,
            )
            .expect("failed to decompress");

            assert_eq!(decompressed_data, original_data);
        };

        for file_name in ["goldhill.bmp", "sails.bmp"] {
            multiple_blocks_impl(file_name);
        }
    }
}
