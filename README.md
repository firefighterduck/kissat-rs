![GitHub](https://img.shields.io/github/license/firefighterduck/kissat-rs)

# Kissat-rs: High-level Rust bindings to the Kissat SAT solver
This crate provides high-level access to the [Kissat SAT solver](http://fmv.jku.at/kissat/).
It builds directly on the lower-level crate [kissat-sys](https://github.com/firefighterduck/kissat-rs/tree/main/kissat-sys).

# Usage
Add the folling lines to your Cargo.toml:
```toml
[dependencies]
kissat-rs = { git = "https://github.com/firefighterduck/kissat-rs", branch = "main", version = "1.0" }
```

## API Usage
Kissat-rs provides convenience methods to solve whole formulas without dealing with the solver state.
Thereby it implements a subset of the provided functionalities of Kissat through safe Rust functions on a `Solver` type that wraps the actual Kissat solver.
`Solver` encodes the internal Kissat solver state in accordance to the IPASIR interface as type-checked state objects that are passed between function calls and guarantee that no function call can lead to undefined states.
For example, it is not possible to access the assigned value of a literal when the solver hasn't found a satisfying assignment for a call to solve.

## Example
```rust
// Define three literals used in both formulae.
let x = 1;
let y = 2;
let z = 3;

// Construct a formula from clauses (i.e. an iterator over literals).
// (~x || y) && (~y || z) && (x || ~z) && (x || y || z)
let formula1 = vec![vec![-x, y], vec![-y, z], vec![x, -z], vec![x, y, z]];
let satisfying_assignment = solve_formula(formula1).unwrap();

if let Some(assignments) = satisfying_assignment {
    assert_eq!(assignments.get(&x).unwrap(), &Some(Assignment::True));
    assert_eq!(assignments.get(&y).unwrap(), &Some(Assignment::True));
    assert_eq!(assignments.get(&z).unwrap(), &Some(Assignment::True));
}

// (x || y || ~z) && ~x && (x || y || z) && (x || ~y)
let formula2 = vec![vec![x, y, -z], vec![-x], vec![x, y, z], vec![x, -y]];
let unsat_result = solve_formula(formula2).unwrap();

// The second formula is unsatisfiable.
// This can for example be proven by resolution.
assert_eq!(unsat_result, None);
```

# Scope and Development
This crate is supposed to be a simple example of how a Rust interface for Kissat could be implemented.
It doesn't aim at covering all of Kissats API for now.

# Known Problems
Kissat does not build with mold.
If you use mold to build your rust projects you have to disable it for building kissat-rs and any crates using it.
Unfortunately, a crate local rustflag that would set a different linker does not help.

# License
Kissat-rs is licensed under the [MIT license](./LICENSE) in the same way as Kissat is.
