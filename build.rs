use cc;

fn main() {
    cc::Build::new()
        .file("external/lib/lz4.c")
        .file("external/lib/lz4hc.c")
        .opt_level(get_opt_level())
        .compile("liblz4.a");
}

// "release" (`3`) by default, unless "debug" (`0`) is specified.
fn get_opt_level() -> u32 {
    std::env::var("PROFILE")
        .map(|profile| match profile.as_str() {
            "debug" => 0,
            "release" => 3,
            _ => 3,
        })
        .unwrap_or(3)
}
