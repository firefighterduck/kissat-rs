mod bindings;

pub use bindings::*;

#[cfg(test)]
mod test {
    use super::bindings::{kissat_add, kissat_init, kissat_solve, kissat_value};
    /// Test case based on the first CaDiCaL example
    #[test]
    fn tie_shirt_example() {
        let kissat = unsafe { kissat_init() };
        let tie = 1;
        let shirt = 2;

        unsafe {
            kissat_add(kissat, -tie);
            kissat_add(kissat, shirt);
            kissat_add(kissat, 0);
            kissat_add(kissat, tie);
            kissat_add(kissat, shirt);
            kissat_add(kissat, 0);
            kissat_add(kissat, -tie);
            kissat_add(kissat, -shirt);
            kissat_add(kissat, 0);

            let result = kissat_solve(kissat);
            assert_eq!(result, 10);

            let tie_result = kissat_value(kissat, tie);
            assert!(tie_result < 0);
            let shirt_result = kissat_value(kissat, shirt);
            assert!(shirt_result > 0);
        }
    }
}
