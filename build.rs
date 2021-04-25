use std::env;
use std::fs::read_dir;
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};

fn handle_command_output(cmd: &str, output: Output) {
    if !output.status.success() {
        let out_contents = String::from_utf8_lossy(&output.stdout);
        let err_contents = String::from_utf8_lossy(&output.stderr);
        panic!(
            "Build error while executing stage{}:\nSTDERR:{}\nSTDOUT:{}",
            cmd, err_contents, out_contents
        );
    }
}

fn main() {
    let current_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let kissat_dir = current_dir.join("kissat");
    let kissat_build_dir = kissat_dir.join("build");

    // Check for the submodule
    if !kissat_dir.exists() {
        println!("No directory at {:?}!", kissat_dir);
        panic!();
    }
    if read_dir(&kissat_dir).unwrap().count() == 0 {
        println!("Empty directory {:?}!", kissat_dir);
        panic!();
    }

    // Configure the kissat build system
    let configure = "./configure";
    let configure_args = vec!["-fPIC"];
    let configure_output = Command::new(configure)
        .args(configure_args)
        .current_dir(&kissat_dir)
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .output()
        .expect("configure script failed!");
    handle_command_output(configure, configure_output);

    // Build kissat
    let make = "make";
    let make_output = Command::new(make)
        .current_dir(&kissat_dir)
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .output()
        .expect("make failed");
    handle_command_output(make, make_output);

    // Make libkissat linkable
    println!(
        "cargo:rustc-link-search=native={}",
        kissat_build_dir.display()
    );
    println!("cargo:rerun-if-changed=wrapper.h");

    // Generate bindings
    let bindings = bindgen::Builder::default()
        .header("wrapper.h")
        .parse_callbacks(Box::new(bindgen::CargoCallbacks))
        .blocklist_type("_Float64x")
        .blocklist_function("strtold")
        .blocklist_function("qecvt")
        .blocklist_function("qfcvt")
        .blocklist_function("qgcvt")
        .blocklist_function("qecvt_r")
        .blocklist_function("qfcvt_r")
        .generate()
        .expect("Unable to generate bindings!");

    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_dir.join("bindings.rs"))
        .expect("Couldn't write bindings!");
}
