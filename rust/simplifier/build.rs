fn main() {
    if let Ok(dir) = std::env::var("Z3_LIB_DIR") {
        println!("cargo:rustc-link-search=native={dir}");
        return;
    }
    if let Ok(home) = std::env::var("HOME") {
        let local = format!("{home}/stuff/z3/build");
        if std::path::Path::new(&local).join("libz3.a").exists()
            || std::path::Path::new(&local).join("libz3.so").exists()
        {
            println!("cargo:rustc-link-search=native={local}");
        }
    }
}
