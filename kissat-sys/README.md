![GitHub](https://img.shields.io/github/license/firefighterduck/kissat-rs)

# Kissat-sys: Low-level Rust bindings to the Kissat SAT solver
This crate provides low-level access to the [Kissat SAT solver](http://fmv.jku.at/kissat/) via declarations and linkage to the `kissat` C library.
Following the `*-sys` package conventions, the `kissat-sys` crate does not define higher-level abstractions over the native `kissat` library functions.
Due to the work-in-progress state of Kissat and the resulting lack of system packages, the crate includes the [Kissat  repository](https://github.com/arminbiere/kissat) as a Git submodule and builds the library from source when being built.

For a higher-level abstraction see the [kissat-rs](https://github.com/firefighterduck/kissat-rs) crate.

# Usage
Add the folling lines to your Cargo.toml:
```toml
[dependencies]
kissat-sys = { git = "https://github.com/firefighterduck/kissat-rs", branch = "main", version = "0.1" }
```

Due to the build-on-demand mechanism used to provide a correctly compiled Kissat library for all systems, it is not possible to provide this crate over crates.io without recreating the whole Kissat build system in `build.rs`.
This restriction might change in the future but is out of scope for now.

# License
Kissat-sys is licensed under the [MIT license](https://github.com/firefighterduck/kissat-rs/blob/main/LICENSE) in the same way as Kissat is.
