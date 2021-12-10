use std::{
    error::Error,
    fmt::{Display, Formatter},
};

/// An error type returned by [`crate::decompress()`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DecompressionError {
    /// The input buffer is empty.
    EmptyInput,
    /// The output buffer is empty.
    EmptyOutput,
    /// Failed to decompress the input - either it is not a valid compressed buffer
    /// returned by the [`crate::Compressor`], or the method was passed an incorrectly sized output buffer.
    DecompressionError,
}

impl Display for DecompressionError {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        use self::DecompressionError::*;

        match self {
            EmptyInput => "the input buffer is empty".fmt(f),
            EmptyOutput => "the output buffer is empty".fmt(f),
            DecompressionError => "failed to decompress the input - either it is not a valid compressed buffer returned by the compressor, or the method was passed an incorrectly sized output buffer".fmt(f),
        }
    }
}

impl Error for DecompressionError {}
