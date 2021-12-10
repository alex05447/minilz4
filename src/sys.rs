#![allow(non_snake_case)]
#![allow(non_camel_case_types)]

use libc::{c_char, c_int, c_uint, c_void};

pub(crate) const LZ4_MAX_INPUT_SIZE: c_int = 0x7E000000;

// pub(crate) const LZ4HC_CLEVEL_MIN: c_int = 3;
// pub(crate) const LZ4HC_CLEVEL_DEFAULT: c_int = 9;
// pub(crate) const LZ4HC_CLEVEL_OPT_MIN: c_int = 10;
pub(crate) const LZ4HC_CLEVEL_MAX: c_int = 12;

pub(crate) const fn LZ4_COMPRESSBOUND(isize: c_int) -> c_int {
    //((unsigned)(isize) > (unsigned)LZ4_MAX_INPUT_SIZE ? 0 : (isize) + ((isize)/255) + 16)
    if (isize as c_uint) > (LZ4_MAX_INPUT_SIZE as c_uint) {
        0
    } else {
        isize + isize / 255 + 16
    }
}

#[repr(C)]
pub(crate) struct LZ4_streamHC_t {
    _private: [u8; 0],
}

extern "C" {
    ///  These functions create and release memory for LZ4 HC streaming state.
    ///  Newly created states are automatically initialized.
    ///  A same state can be used multiple times consecutively,
    ///  starting with LZ4_resetStreamHC_fast() to start a new stream of blocks.
    pub(crate) fn LZ4_createStreamHC() -> *mut LZ4_streamHC_t;
    pub(crate) fn LZ4_freeStreamHC(streamHCPtr: *mut LZ4_streamHC_t);
    //LZ4LIB_API LZ4_streamHC_t* LZ4_createStreamHC(void);
    //LZ4LIB_API int             LZ4_freeStreamHC(LZ4_streamHC_t* streamHCPtr);

    /// ...
    ///
    /// Selecting the compression level can be done with LZ4_resetStreamHC_fast() (starts a new stream)
    /// or LZ4_setCompressionLevel() (anytime, between blocks in the same stream) (experimental).
    /// LZ4_resetStreamHC_fast() only works on states which have been properly initialized at least once,
    /// which is automatically the case when state is created using LZ4_createStreamHC().
    ///
    /// ...
    ///
    /// After completing a streaming compression,
    /// it's possible to start a new stream of blocks, using the same LZ4_streamHC_t state,
    /// just by resetting it, using LZ4_resetStreamHC_fast().
    pub(crate) fn LZ4_resetStreamHC_fast(streamHCPtr: *mut LZ4_streamHC_t, compressionLevel: c_int);
    // LZ4LIB_API void LZ4_resetStreamHC_fast(LZ4_streamHC_t* streamHCPtr, int compressionLevel);   /* v1.9.0+ */
    ///  A variant of LZ4_compress_HC_extStateHC().
    ///
    ///  Using this variant avoids an expensive initialization step. It is only safe
    ///  to call if the state buffer is known to be correctly initialized already
    ///  (see above comment on LZ4_resetStreamHC_fast() for a definition of
    ///  "correctly initialized"). From a high level, the difference is that this
    ///  function initializes the provided state with a call to
    ///  LZ4_resetStreamHC_fast() while LZ4_compress_HC_extStateHC() starts with a
    ///  call to LZ4_resetStreamHC().
    pub(crate) fn LZ4_compress_HC_extStateHC_fastReset(
        state: *mut c_void,
        src: *const c_char,
        dst: *mut c_char,
        srcSize: c_int,
        dstCapacity: c_int,
        compressionLevel: c_int,
    ) -> c_int;
    // LZ4LIB_STATIC_API int LZ4_compress_HC_extStateHC_fastReset (
    //     void* state,
    //     const char* src, char* dst,
    //     int srcSize, int dstCapacity,
    //     int compressionLevel);

    /// compressedSize : is the exact complete size of the compressed block.
    /// dstCapacity : is the size of destination buffer (which must be already allocated), presumed an upper bound of decompressed size.
    /// return : the number of bytes decompressed into destination buffer (necessarily <= dstCapacity)
    ///           If destination buffer is not large enough, decoding will stop and output an error code (negative value).
    ///           If the source stream is detected malformed, the function will stop decoding and return a negative result.
    /// Note 1 : This function is protected against malicious data packets :
    ///          it will never writes outside 'dst' buffer, nor read outside 'source' buffer,
    ///          even if the compressed block is maliciously modified to order the decoder to do these actions.
    ///          In such case, the decoder stops immediately, and considers the compressed block malformed.
    /// Note 2 : compressedSize and dstCapacity must be provided to the function, the compressed block does not contain them.
    ///          The implementation is free to send / store / derive this information in whichever way is most beneficial.
    ///          If there is a need for a different format which bundles together both compressed data and its metadata, consider looking at lz4frame.h instead.
    ///
    pub(crate) fn LZ4_decompress_safe(
        source: *const c_char,
        dest: *mut c_char,
        compressedSize: c_int,
        maxDecompressedSize: c_int,
    ) -> c_int;
    //LZ4LIB_API int LZ4_decompress_safe(const char* src, char* dst, int compressedSize, int dstCapacity);
}

#[cfg(test)]
mod tests {
    use super::*;

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
    fn compress_decompress() {
        let compress_decompress_impl = |file_name: &str| {
            // Read the data from file.
            let original_data = read_file_to_vec(file_name);
            let original_size = original_data.len();
            assert!(original_size < LZ4_MAX_INPUT_SIZE as _);

            // Calculate the bounds and allocate the destination buffer for compression.
            let compressed_bound = LZ4_COMPRESSBOUND(original_size as _);
            let mut compressed_data = Vec::<u8>::with_capacity(compressed_bound as _);

            // Allocate the compression state, compress as a singe block, free the compression state.
            let compression_state = unsafe { LZ4_createStreamHC() };
            let compressed_size = unsafe {
                LZ4_compress_HC_extStateHC_fastReset(
                    compression_state as _,
                    original_data.as_ptr() as _,
                    compressed_data.as_mut_ptr() as _,
                    original_size as _,
                    compressed_bound,
                    LZ4HC_CLEVEL_MAX,
                )
            };
            assert!(compressed_size > 0);
            assert!(compressed_size < compressed_bound);
            unsafe { compressed_data.set_len(compressed_size as _) };
            unsafe { LZ4_freeStreamHC(compression_state) };

            /*
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
            let mut uncompressed_data = Vec::<u8>::with_capacity(original_size);
            let uncompressed_size = unsafe {
                LZ4_decompress_safe(
                    compressed_data.as_ptr() as _,
                    uncompressed_data.as_mut_ptr() as _,
                    compressed_data.len() as _,
                    original_size as _,
                )
            };
            assert!(uncompressed_size > 0);
            assert_eq!(uncompressed_size as usize, original_size);
            unsafe { uncompressed_data.set_len(uncompressed_size as _) };

            assert_eq!(uncompressed_data, original_data);
        };

        for file_name in ["goldhill.bmp", "sails.bmp"] {
            compress_decompress_impl(file_name);
        }
    }
}
