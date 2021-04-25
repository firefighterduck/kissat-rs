use derive_try_from_primitive::TryFromPrimitive;
use kissat_sys::{kissat, kissat_add, kissat_init, kissat_solve, kissat_value};
use std::{convert::TryFrom, os::raw::c_int};

type Literal = c_int;

#[derive(TryFromPrimitive, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(i32)]
pub enum SolverResult {
    Interrupted,
    Satisfiable = 10,
    Unsatisfiable = 20,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Assignment {
    True,
    False,
    Both,
}

pub struct Solver {
    solver: *mut kissat,
}

impl Solver {
    pub fn init() -> Self {
        let solver_pt;
        unsafe {
            solver_pt = kissat_init();
        }
        Solver { solver: solver_pt }
    }

    pub fn add(&mut self, literal: Literal) {
        unsafe {
            kissat_add(self.solver, literal);
        }
    }

    pub fn solve(&mut self) -> Option<SolverResult> {
        let result;
        unsafe {
            result = kissat_solve(self.solver);
        }
        let solver_result = SolverResult::try_from(result);
        solver_result.ok()
    }

    pub fn value(&self, literal: Literal) -> Option<Assignment> {
        use Assignment::*;

        let value;
        unsafe {
            value = kissat_value(self.solver, literal);
        }

        match value {
            0 => Some(Both),
            n if n == literal => Some(True),
            n if n == -literal => Some(False),
            _ => None,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    // This is the same test as in kissat-sys but with the safe API.
    #[test]
    fn test_tie_shirt() {
        let tie = 1;
        let shirt = 2;

        let mut solver = Solver::init();
        solver.add(-tie);
        solver.add(shirt);
        solver.add(0);
        solver.add(tie);
        solver.add(shirt);
        solver.add(0);
        solver.add(-tie);
        solver.add(-shirt);
        solver.add(0);

        let result = solver.solve();
        assert_eq!(result, Some(SolverResult::Satisfiable));

        let tie_result = solver.value(tie);
        assert_eq!(tie_result, Some(Assignment::False));
        let shirt_result = solver.value(shirt);
        assert_eq!(shirt_result, Some(Assignment::True));
    }
}
