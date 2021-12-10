use {
    minilz4::*,
    std::num::{NonZeroU32, NonZeroU64},
};

const LZ4_MAX_INPUT_SIZE: i32 = 0x7E000000;

// Calculates the number of sub-blocks an `uncompressed_size` length block needs to be split into
// in order for each one to be smaller than the max input size of the LZ4 block compression algorithm.
fn calc_num_blocks(uncompressed_size: NonZeroU64) -> NonZeroU32 {
    debug_assert!(LZ4_MAX_INPUT_SIZE > 0);
    let max_uncompressed_size = unsafe { NonZeroU64::new_unchecked(LZ4_MAX_INPUT_SIZE as _) };

    calc_num_blocks_impl(uncompressed_size, max_uncompressed_size)
}

fn calc_num_blocks_impl(
    uncompressed_size: NonZeroU64,
    max_uncompressed_size: NonZeroU64,
) -> NonZeroU32 {
    debug_assert!(
        max_uncompressed_size.get() <= LZ4_MAX_INPUT_SIZE as _,
        "maximum size of LZ4 input exceeded"
    );

    // Divide and round up.
    let num_blocks = ((uncompressed_size.get() + max_uncompressed_size.get() - 1)
        / max_uncompressed_size.get()) as u32;
    debug_assert!(num_blocks > 0);
    unsafe { NonZeroU32::new_unchecked(num_blocks) }
}

// Given the `uncompressed_size` block and the number of sub-blocks `num_blocks`, calculated by `calc_num_blocks()`,
// calculates the maximum size in bytes of a sub-block (last sub-block will usually be smaller).
fn calc_block_size(uncompressed_size: NonZeroU64, num_blocks: NonZeroU32) -> NonZeroU32 {
    // Align the block size up to max LZ4 history size value.
    calc_block_size_impl(uncompressed_size, num_blocks, unsafe {
        NonZeroU32::new_unchecked(64 * 1024)
    })
}

fn calc_block_size_impl(
    uncompressed_size: NonZeroU64,
    num_blocks: NonZeroU32,
    block_alignment: NonZeroU32,
) -> NonZeroU32 {
    let num_blocks = num_blocks.get() as u64;
    let block_size = ((uncompressed_size.get() + num_blocks - 1) / num_blocks) as u32;

    let aligned_block_size = if num_blocks > 1 {
        (block_size + (block_alignment.get() - 1)) / block_alignment.get() * block_alignment.get()
    } else {
        block_size
    };

    debug_assert!(aligned_block_size > 0);
    unsafe { NonZeroU32::new_unchecked(aligned_block_size) }
}

// fn single_block() {
//     use std::io::Read;

//     let image_name = "goldhill.bmp";

//     let mut compressor = Compressor::new().unwrap();

//     let root_path = std::env::current_dir().unwrap();
//     let image_path = root_path.clone().join(image_name);

//     let mut image = std::fs::File::open(&image_path).unwrap();
//     let mut image_data = Vec::new();
//     let original_size = image.read_to_end(&mut image_data).unwrap();
//     assert_eq!(original_size, image_data.len());

//     assert!(original_size < LZ4_MAX_INPUT_SIZE as _);

//     let uncompressed_size = NonZeroU64::new(original_size as u64).unwrap();
//     let num_blocks = calc_num_blocks(uncompressed_size);
//     assert_eq!(num_blocks.get(), 1);
//     let block_size = calc_block_size(uncompressed_size, num_blocks);
//     assert_eq!(block_size.get() as u64, uncompressed_size.get());
//     let compressed_bound = Compressor::compressed_size_bound_impl(uncompressed_size, num_blocks, block_size);

//     let mut compressed_data = vec![0; compressed_bound.get() as _];
//     compressor.compress(&image_data, &mut compressed_data).unwrap();
// }

// fn multiple_blocks() {
//     use std::io::Read;

//     let image_name = "goldhill.bmp";

//     let mut compressor = Compressor::new().unwrap();

//     let root_path = std::env::current_dir().unwrap();
//     let image_path = root_path.clone().join(image_name);

//     let mut image = std::fs::File::open(&image_path).unwrap();
//     let mut image_data = Vec::new();
//     let original_size = image.read_to_end(&mut image_data).unwrap();
//     assert_eq!(original_size, image_data.len());

//     assert!(original_size < LZ4_MAX_INPUT_SIZE as _);

//     let uncompressed_size = NonZeroU64::new(original_size as u64).unwrap();

//     let max_uncompressed_size = unsafe { NonZeroU64::new_unchecked(64 * 1024) };
//     let block_alignment = unsafe { NonZeroU32::new_unchecked(4 * 1024) };

//     let num_blocks = calc_num_blocks_impl(uncompressed_size, max_uncompressed_size);
//     assert!(num_blocks.get() > 1);
//     let block_size = calc_block_size_impl(uncompressed_size, num_blocks, block_alignment);
//     let compressed_bound = Compressor::compressed_size_bound_impl(uncompressed_size, num_blocks, block_size);

//     let mut compressed_data = vec![0; compressed_bound.get() as _];
//     compressor.compress_impl(&image_data, &mut compressed_data, max_uncompressed_size, block_alignment).unwrap();
// }

fn compress_decompress() {
    use std::io::{Read, Write};

    let image_names = ["goldhill.bmp", "sails.bmp"];
    let mut compressed_image_name = String::new();

    let mut compressor = Compressor::new().unwrap();

    for image_name in image_names.iter() {
        let root_path = std::env::current_dir().unwrap();
        let image_path = root_path.clone().join(image_name);

        let mut image = std::fs::File::open(&image_path).unwrap();
        let mut image_data = Vec::new();
        let original_size = image.read_to_end(&mut image_data).unwrap();
        assert_eq!(original_size, image_data.len());

        let compressed_bound =
            Compressor::compressed_size_bound(NonZeroU64::new(original_size as u64).unwrap());
        let mut compressed_data = Vec::<u8>::with_capacity(compressed_bound.get() as _);
        unsafe { compressed_data.set_len(compressed_bound.get() as _) };

        let original_compressed_size = compressor
            .compress(&image_data, &mut compressed_data)
            .unwrap();

        unsafe { compressed_data.set_len(original_compressed_size.get() as _) };

        compressed_image_name.clear();
        compressed_image_name.push_str(image_name);
        compressed_image_name.push_str(".lz4");

        let compressed_image_path = root_path.join(&compressed_image_name);
        let mut compressed_image = std::fs::File::create(&compressed_image_path).unwrap();
        compressed_image.write_all(&compressed_data).unwrap();
        compressed_data.clear();

        let mut compressed_image = std::fs::File::open(&compressed_image_path).unwrap();
        let compressed_size = compressed_image.read_to_end(&mut compressed_data).unwrap();
        assert_eq!(compressed_size, compressed_data.len());
        assert_eq!(compressed_size as u64, original_compressed_size.get());

        let mut uncompressed_image_data = Vec::<u8>::with_capacity(original_size);
        unsafe { uncompressed_image_data.set_len(original_size as _) };

        decompress(&compressed_data, &mut uncompressed_image_data).unwrap();

        assert_eq!(uncompressed_image_data, image_data);
    }
}

fn main() {
    // multiple_blocks();

    //single_block();

    compress_decompress();
}
