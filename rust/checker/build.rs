fn link_z3(dir: &str) {
    println!("cargo:rustc-link-search=native={dir}");
    println!("cargo:rustc-link-arg=-Wl,-rpath,{dir}");
}

fn has_libz3(dir: &std::path::Path) -> bool {
    dir.join("libz3.so").exists()
        || dir.join("libz3.a").exists()
        || dir.join("libz3.dylib").exists()
}

fn main() {
    if let Ok(dir) = std::env::var("Z3_LIB_DIR") {
        link_z3(&dir);
        return;
    }
    if let Ok(home) = std::env::var("HOME") {
        for subpath in ["lib/z3-4.16.0/bin", "stuff/z3/build"] {
            let local = format!("{home}/{subpath}");
            if has_libz3(std::path::Path::new(&local)) {
                link_z3(&local);
                return;
            }
        }
    }
}
