use std::{
    error::Error,
    fmt::{Display, Formatter},
};

/// An error type returned by [`crate::Compressor`] methods.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CompressorError {
    /// Out of memory when allocating the [`crate::Compressor`] internal state.
    OutOfMemory,
    /// The input buffer is empty.
    EmptyInput,
    /// The output buffer has insufficient space to compress the input.
    InsufficientSpace,
    /// Failed to compress the input.
    CompressionError,
}

impl Display for CompressorError {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        use CompressorError::*;

        match self {
            OutOfMemory => "out of memory when allocating the compressor internal state".fmt(f),
            EmptyInput => "the input buffer is empty".fmt(f),
            InsufficientSpace => {
                "the output buffer has insufficient space to compress the input".fmt(f)
            }
            CompressionError => "failed to compress the input".fmt(f),
        }
    }
}

impl Error for CompressorError {}
