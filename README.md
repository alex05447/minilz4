An extremely minimalistic Rust wrapper around the [`LZ4`](https://github.com/lz4/lz4) compression library.

Implements only the `LZ4` "block" compression format, not the "frame" (a.k.a. streaming) format, but without the input size restriction.

Compression level is not configurable.

Produced data is not supposed to be compatible with other `LZ4` tools / libraries.