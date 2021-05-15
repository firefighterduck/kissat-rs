mod state;

use derive_try_from_primitive::TryFromPrimitive;
use kissat_sys::{kissat, kissat_add, kissat_init, kissat_release, kissat_solve, kissat_value};
use std::{collections::HashMap, convert::TryFrom, os::raw::c_int};

pub type Literal = c_int;
const CLAUSE_END: Literal = 0;

pub use state::*;

/// The solver result as defined for IPASIR interfaces.
#[derive(TryFromPrimitive, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(i32)]
enum SolverResult {
    Interrupted, // implicitly 0
    Satisfiable = 10,
    Unsatisfiable = 20,
}

/// Satisfying assignment of a single literal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Assignment {
    True,
    False,
    Both,
}

/// A simple wrapper struct for the Kissat solver.
/// Exposes a safe subset of the partial IPASIR interface that
/// Kissat exposes. Uses a type-checked state system to disallow
/// access to these functions (e.g. calling `value` before `solve`).
pub struct Solver {
    solver: *mut kissat,
}

impl Solver {
    /// Initialize a new solver in INPUT state
    pub fn init() -> (Self, INPUTState) {
        let solver_pt;
        unsafe {
            solver_pt = kissat_init();
        }
        (Solver { solver: solver_pt }, INPUTState::new())
    }

    /// Add a new literal to the current clause or end the clause with value 0.
    /// Switches from any state to INPUT (e.g. for incremental solving, which Kissat
    /// currently doesn't support).
    pub fn add<S: State>(&mut self, literal: Literal, _state: S) -> INPUTState {
        unsafe {
            kissat_add(self.solver, literal);
        }
        INPUTState::new()
    }

    /// Add multiple literals at once.
    pub fn add_multiple<I, S>(&mut self, literals: I, _state: S) -> INPUTState
    where
        I: IntoIterator<Item = Literal>,
        S: State,
    {
        for literal in literals {
            let _ = self.add(literal, INPUTState::new());
        }
        INPUTState::new()
    }

    /// Add multiple literals as a single clause.
    /// Adds the delimiting 0 to the end of the clause automatically.
    pub fn add_clause<I, S>(&mut self, clause: I, _state: S) -> INPUTState
    where
        I: IntoIterator<Item = Literal>,
        S: State,
    {
        let _ = self.add_multiple(clause, INPUTState::new());
        self.add(CLAUSE_END, INPUTState::new())
    }

    /// Solve the formula input sofar.
    /// Returns the state after solving. This can be any of INPUT, SAT or UNSAT
    /// and can be dynamically translated to their counterpart states.
    pub fn solve<S: State>(&mut self, _state: S) -> Result<AnyState, Error> {
        let result;
        unsafe {
            result = kissat_solve(self.solver);
        }
        let solver_result = SolverResult::try_from(result);
        solver_result
            .map(|result| AnyState::from(result))
            .map_err(|_| Error::UnknownSolverResult)
    }

    /// Solves a formula and returns a satisfying assignment.
    /// Abstracts all state details away and constructs a new solver for each invocation.
    ///
    /// In contrast to [`Solver::decide_formula`] this does construct a satisfying assignment.
    pub fn solve_formula<F, C>(
        formula: F,
    ) -> Result<Option<HashMap<Literal, Option<Assignment>>>, Error>
    where
        F: IntoIterator<Item = C>,
        C: IntoIterator<Item = Literal>,
    {
        let mut assignments = HashMap::new();
        let (mut solver, init_state) = Solver::init();

        let mut add_state = init_state;
        for clause in formula {
            for literal in clause {
                assignments.insert(literal.abs(), None);
                add_state = solver.add(literal, add_state);
            }
            add_state = solver.add(CLAUSE_END, add_state);
        }

        let solved_state = solver.solve(add_state)?;

        if let AnyState::SAT(mut sat_state) = solved_state {
            for (literal, assignment) in assignments.iter_mut() {
                let (value, value_state) = solver.value(*literal, sat_state)?;
                sat_state = value_state;
                assignment.replace(value);
            }

            return Ok(Some(assignments));
        }
        Ok(None)
    }

    /// Decides whether a given formula is satisfiable or not.
    /// Abstracts all state details away and constructs a new solver for each invocation.
    ///
    /// In contrast to [`Solver::solve_formula`] this does not construct a satisfying assignment.
    pub fn decide_formula<F, C>(formula: F) -> Result<bool, Error>
    where
        F: IntoIterator<Item = C>,
        C: IntoIterator<Item = Literal>,
    {
        let (mut solver, init_state) = Solver::init();

        let mut add_state = init_state;
        for clause in formula {
            for literal in clause {
                add_state = solver.add(literal, add_state);
            }
            add_state = solver.add(CLAUSE_END, add_state);
        }

        let solved_state = solver.solve(add_state)?;
        Ok(matches!(solved_state, AnyState::SAT(_)))
    }

    /// Evaluates the given literal for the found satisfying assignment.
    /// A literal might be set to True, False or any of these two (Both).
    pub fn value<S: SAT>(&self, literal: Literal, state: S) -> Result<(Assignment, S), Error> {
        use Assignment::*;

        let value;
        unsafe {
            value = kissat_value(self.solver, literal);
        }

        match value {
            0 => Ok((Both, state)),
            n if n == literal => Ok((True, state)),
            n if n == -literal => Ok((False, state)),
            n => Err(Error::UnassignedLiteral(n)),
        }
    }
}

impl Drop for Solver {
    fn drop(&mut self) {
        unsafe {
            kissat_release(self.solver);
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    // This is the same test as in kissat-sys but with the safe API.
    #[test]
    fn test_tie_shirt() -> Result<(), Error> {
        let tie = 1;
        let shirt = 2;

        let (mut solver, mut state) = Solver::init();
        state = solver.add_clause(vec![-tie, shirt], state);
        state = solver.add_clause(vec![tie, shirt], state);
        state = solver.add_clause(vec![-tie, -shirt], state);

        let solver_result_state = solver.solve(state)?;
        let sat_state = SATState::try_from(solver_result_state)?;

        let (tie_result, sat_state) = solver.value(tie, sat_state)?;
        assert_eq!(tie_result, Assignment::False);
        let (shirt_result, _) = solver.value(shirt, sat_state)?;
        assert_eq!(shirt_result, Assignment::True);
        Ok(())
    }

    #[test]
    fn test_solve_formula() -> Result<(), Error> {
        let x = 1;
        let y = 2;
        let z = 3;

        // (~x || y) && (~y || z) && (x || ~z) && (x || y || z) - satisfied by x -> True, y -> True, z -> True
        let formula1 = vec![vec![-x, y], vec![-y, z], vec![x, -z], vec![x, y, z]];

        let satisfying_assignment = Solver::solve_formula(formula1)?;
        if let Some(assignments) = satisfying_assignment {
            assert_eq!(assignments.get(&x).unwrap(), &Some(Assignment::True));
            assert_eq!(assignments.get(&y).unwrap(), &Some(Assignment::True));
            assert_eq!(assignments.get(&z).unwrap(), &Some(Assignment::True));
        }

        // (x || y || ~z) && ~x && (x || y || z) && (x || ~y) - unsatisfiable (e.g. by resolution)
        let formula2 = vec![vec![x, y, -z], vec![-x], vec![x, y, z], vec![x, -y]];
        let unsat_result = Solver::solve_formula(formula2)?;
        assert_eq!(unsat_result, None);

        Ok(())
    }

    #[test]
    fn test_decide_formula() -> Result<(), Error> {
        let x = 1;
        let y = 2;
        let z = 3;

        // (~x || y) && (~y || z) && (x || ~z) && (x || y || z) - satisfied by x -> True, y -> True, z -> True
        let formula1 = vec![vec![-x, y], vec![-y, z], vec![x, -z], vec![x, y, z]];

        let is_sat1 = Solver::decide_formula(formula1)?;
        assert!(is_sat1);

        // (x || y || ~z) && ~x && (x || y || z) && (x || ~y) - unsatisfiable (e.g. by resolution)
        let formula2 = vec![vec![x, y, -z], vec![-x], vec![x, y, z], vec![x, -y]];
        let is_sat2 = Solver::decide_formula(formula2)?;
        assert!(!is_sat2);

        Ok(())
    }
}
