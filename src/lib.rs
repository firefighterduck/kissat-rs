//! Crate that provides a high-level API utilizing the kissat SAT solver.

use derive_more::Debug;
use derive_try_from_primitive::TryFromPrimitive;
use kissat_sys::{kissat, kissat_add, kissat_init, kissat_release, kissat_solve, kissat_value};
use std::{collections::HashMap, convert::TryFrom, num::NonZeroI32, ops::Neg, ptr::NonNull};

mod state;
use state::*;
pub use state::{Error, Error2};

mod literal;
pub use literal::*;

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

pub(crate) struct RawSolver {
    pub(crate) solver_pt: NonNull<kissat>,
}

/// Wrapper for the Kissat solver that tracks the solver's state.
///
/// Exposes a safe subset of the partial IPASIR interface that
/// Kissat exposes. Uses a type-level state machine to disallow
/// access to these functions (e.g. calling `value` before `solve`).
/// The API will often take the solver by value to guarantee that the
/// state is always correct and that the underlying kissat allocation
/// will be allocated on unrecoverable errors.
#[derive(Debug)]
pub struct Solver<S: State> {
    #[debug(skip)]
    solver: RawSolver,
    state: S,
}

impl Solver<INPUTState> {
    /// Initialize a new solver in INPUT state
    pub fn init() -> Self {
        let solver_pt;
        unsafe {
            // SAFETY:
            // kissat_init will abort if the allocation fails/returns NULL.
            // The pointer will always be non-null.
            solver_pt = NonNull::new_unchecked(kissat_init());
        }
        Solver {
            solver: RawSolver { solver_pt },
            state: INPUTState::InputFinished,
        }
    }

    /// Finishes a clause by adding the correct 0 literal to the solver's stack.
    ///
    /// Should be preferred over calling [`Solver::add`] or [`Solver::add_raw`]
    /// with the corresponding clause end literal since it requires less runtime checks.
    fn finish_clause(self) -> Self {
        unsafe {
            // SAFETY:
            // The pointer is non-null and points to a kissat solver.
            kissat_add(self.solver.solver_pt.as_ptr(), CLAUSE_END.into());
        }

        self.change_to_state(INPUTState::InputFinished)
    }

    /// Finishes a clause by adding the correct 0 literal to the solver's stack.
    ///
    /// Should be preferred over calling [`Solver::add`] or [`Solver::add_raw`]
    /// with the corresponding clause end literal since it requires less runtime checks.
    fn finish_clause_check(self) -> Self {
        if let INPUTState::OpenClause = self.state {
            unsafe {
                // SAFETY:
                // The pointer is non-null and points to a kissat solver.
                kissat_add(self.solver.solver_pt.as_ptr(), CLAUSE_END.into());
            }

            self.change_to_state(INPUTState::InputFinished)
        } else {
            self
        }
    }

    /// Solve the formula input so far.
    /// Sets the solver's state to one of INPUT, SAT or UNSAT.
    ///
    /// This requires that all clauses are closed or it will fail with [`Error2::RecoverableOpenClauseWhenSolving`].
    /// That error contains the solver to allow to simply reuse it and call solve later again
    /// (then hopefully with all clauses closed).
    pub fn solve(self) -> Result<Solver<AnyState>, Error2> {
        if let INPUTState::OpenClause = self.state {
            return Err(Error2::RecoverableOpenClauseWhenSolving(self));
        }

        // Small hack to stay DRY. This state will never matter.
        self.change_state::<UNSATState>()
            .solve()
            .map_err(Into::into)
    }
}

impl<S: State> Solver<S> {
    fn change_state<T: State>(self) -> Solver<T> {
        Solver {
            solver: self.solver,
            state: T::default(),
        }
    }

    fn change_to_state<T: State>(self, new_state: T) -> Solver<T> {
        Solver {
            solver: self.solver,
            state: new_state,
        }
    }

    /// Add a new literal to the current clause or end the clause with value 0.
    /// Switches from any state to INPUT (e.g. for incremental solving, which Kissat
    /// currently doesn't support).
    fn add_literal(self, literal: Literal) -> Solver<INPUTState> {
        unsafe {
            // SAFETY:
            // The pointer is non-null and points to a kissat solver.
            kissat_add(self.solver.solver_pt.as_ptr(), literal.into());
        }

        if literal == CLAUSE_END {
            self.change_to_state(INPUTState::InputFinished)
        } else {
            self.change_to_state(INPUTState::OpenClause)
        }
    }

    /// Add a new literal to the current clause or end the clause with value 0.
    /// Switches from any state to INPUT (e.g. for incremental solving, which Kissat
    /// currently doesn't support).
    ///
    /// Accepts raw i32 and the like but will fail if they don't adhere to
    /// the requirements of [`Literal`].
    fn add_literal_raw(self, literal: i32) -> Result<Solver<INPUTState>, Error> {
        let literal = Literal::try_from(literal)?;

        unsafe {
            // SAFETY:
            // The pointer is non-null and points to a kissat solver.
            kissat_add(self.solver.solver_pt.as_ptr(), literal.into());
        }

        if literal == CLAUSE_END {
            Ok(self.change_to_state(INPUTState::InputFinished))
        } else {
            Ok(self.change_to_state(INPUTState::OpenClause))
        }
    }

    /// Add a new literal to the current clause or end the clause with value 0.
    /// Switches from any state to INPUT (e.g. for incremental solving, which Kissat
    /// currently doesn't support).
    ///
    /// If the numeral is not a valid [`Literal`], the function will fail.
    fn add_literal_raw_nonzero(self, literal: NonZeroI32) -> Result<Solver<INPUTState>, Error> {
        let literal = Literal::try_from(literal)?;

        unsafe {
            // SAFETY:
            // The pointer is non-null and points to a kissat solver.
            kissat_add(self.solver.solver_pt.as_ptr(), literal.into());
        }

        Ok(self.change_to_state(INPUTState::OpenClause))
    }

    /// Add multiple literals at once.
    fn add_multiple<I>(self, literals: I) -> Solver<INPUTState>
    where
        I: IntoIterator<Item = Literal>,
    {
        let mut solver: Solver<INPUTState> = self.change_state::<INPUTState>();
        for literal in literals {
            solver = solver.add_literal(literal);
        }
        solver
    }

    /// Add multiple literals at once.
    ///
    /// If any of the numerals cannot be converted to [`NonZeroI32`] or is no valid [`Literal`],
    /// the function will fail.
    fn add_multiple_raw<I, N>(self, literals: I) -> Result<Solver<INPUTState>, Error>
    where
        I: IntoIterator<Item = N>,
        NonZeroI32: TryFrom<N>,
    {
        let mut solver: Solver<INPUTState> = self.change_state::<INPUTState>();
        for literal in literals {
            solver = match NonZeroI32::try_from(literal) {
                Ok(n) => solver.add_literal_raw_nonzero(n)?,
                Err(_) => return Err(Error::IncompatibleNumeral),
            }
        }
        Ok(solver)
    }

    /// Add a stream of literals to the solver. The stream can contain zeroes
    /// to denote the end of individual clauses. Otherwise everything will be put
    /// into a single clause (which will be automatically closed if the iterator doesn't
    /// end in a zero).
    ///
    /// If any of the numerals cannot be converted to i32 or is no valid [`Literal`],
    /// the function will fail.
    pub fn add_multiple_stream<I, N>(self, literals: I) -> Result<Solver<INPUTState>, Error>
    where
        I: IntoIterator<Item = N>,
        i32: TryFrom<N>,
    {
        let mut solver: Solver<INPUTState> = self.change_state::<INPUTState>();
        for literal in literals {
            solver = match i32::try_from(literal) {
                Ok(n) => solver.add_literal_raw(n)?,
                Err(_) => return Err(Error::IncompatibleNumeral),
            }
        }
        Ok(solver.finish_clause_check())
    }

    /// Add multiple literals as a single clause, which should not contain any CLAUSE_END.
    /// Adds the delimiting 0 to the end of the clause automatically.
    pub fn add_clause<I>(self, clause: I) -> Solver<INPUTState>
    where
        I: IntoIterator<Item = Literal>,
    {
        let solver = self.add_multiple(clause);
        solver.finish_clause()
    }

    /// Add multiple literals as a single clause.
    /// Adds the delimiting 0 to the end of the clause automatically.
    ///
    /// If any of the numerals cannot be converted to [`NonZeroI32`] or is no valid [`Literal`],
    /// the function will fail.
    pub fn add_clause_raw<I, N>(self, clause: I) -> Result<Solver<INPUTState>, Error>
    where
        I: IntoIterator<Item = N>,
        NonZeroI32: TryFrom<N>,
    {
        let mut solver: Solver<INPUTState> = self.change_state::<INPUTState>();
        solver = solver.add_multiple_raw(clause)?;
        Ok(solver.finish_clause())
    }
}

impl<S> Solver<S>
where
    S: State,
    S: NoInput,
{
    /// Solve the formula input sofar.
    /// Returns the state after solving. This can be any of INPUT, SAT or UNSAT
    /// and can be dynamically translated to their counterpart states.
    ///
    /// In any state that is not input, we can skip checking for closed clauses.
    pub fn solve(self) -> Result<Solver<AnyState>, Error> {
        let result;
        unsafe {
            // SAFETY:
            // The pointer is non-null and points to a kissat solver.
            // In any `NoInput` state, all clauses are closed.
            result = kissat_solve(self.solver.solver_pt.as_ptr());
        }
        let solver_result = SolverResult::try_from(result);
        solver_result
            .map(|state| self.change_to_state(AnyState::from(state)))
            .map_err(|_| Error::UnknownSolverResult)
    }
}

impl Solver<AnyState> {
    /// Explicitly transitions the solver into the SAT state.
    /// Fails if the internal state is not SAT.
    pub fn checked_sat(self) -> Result<Solver<SATState>, Error> {
        let sat = SATState::try_from(self.state)?;
        Ok(self.change_to_state(sat))
    }

    /// Checks whether the solver has reached SAT. Does not change the solver state.
    pub fn is_sat(&self) -> bool {
        SATState::try_from(self.state).is_ok()
    }

    /// Checks whether the solver has reached UNSAT. Does not change the solver state.
    pub fn is_unsat(&self) -> bool {
        UNSATState::try_from(self.state).is_ok()
    }

    /// Explicitly transitions the solver into the UNSAT state.
    /// Fails if the internal state is not UNSAT.
    pub fn checked_unsat(self) -> Result<Solver<UNSATState>, Error> {
        let sat = UNSATState::try_from(self.state)?;
        Ok(self.change_to_state(sat))
    }
}

impl Solver<SATState> {
    /// Evaluates the given literal for the found satisfying assignment.
    /// A literal might be set to True, False or any of these two (Both).
    pub fn value(&self, literal: Literal) -> Result<Assignment, Error> {
        use Assignment::*;

        let value;
        unsafe {
            // SAFETY:
            // The pointer is non-null and points to a kissat solver.
            value = kissat_value(self.solver.solver_pt.as_ptr(), literal.into());
        }

        match Literal::try_from(value)? {
            n if n == CLAUSE_END => Ok(Both),
            n if n == literal => Ok(True),
            n if n == literal.neg()? => Ok(False),
            n => Err(Error::UnassignedLiteral(n)),
        }
    }
}

impl Drop for RawSolver {
    fn drop(&mut self) {
        unsafe {
            // SAFETY:
            // The pointer is non-null and points to a kissat solver.
            kissat_release(self.solver_pt.as_ptr());
        }
    }
}

/// SAFETY: The internal pointer to the kissat solver is always unique, since each call to `kissat_init`
/// allocates a new solver and the pointer to that one is never copied.
unsafe impl<S: State> Send for Solver<S> {}

/// Solves a formula and returns a satisfying assignment.
/// Abstracts all state details away and constructs a new solver for each invocation.
///
/// In contrast to [`decide_formula`] this does construct a satisfying assignment.
/// If any of the numerals cannot be converted to [`NonZeroI32`] or is no valid [`Literal`],
/// the function will fail.
/// This variant of the function also does not allow zeroes in the formula.
/// ```
/// # use kissat_rs::*;
/// # let x: i32 = 1;
/// # let y = 2;
/// # let z = 3;
///
/// // (~x || y) && (~y || z) && (x || ~z) && (x || y || z) - satisfied by x -> True, y -> True, z -> True
/// let formula1 = vec![vec![-x, y], vec![-y, z], vec![x, -z], vec![x, y, z]];
///
/// let satisfying_assignment = solve_formula(formula1)?;
/// if let Some(assignments) = satisfying_assignment {
///     assert_eq!(assignments.get(&x).unwrap(), &Some(Assignment::True));
///     assert_eq!(assignments.get(&y).unwrap(), &Some(Assignment::True));
///     assert_eq!(assignments.get(&z).unwrap(), &Some(Assignment::True));
/// }
///
/// // (x || y || ~z) && ~x && (x || y || z) && (x || ~y) - unsatisfiable (e.g. by resolution)
/// let formula2 = vec![vec![x, y, -z], vec![-x], vec![x, y, z], vec![x, -y]];
/// let unsat_result = solve_formula(formula2)?;
/// assert_eq!(unsat_result, None);
///
/// # Ok::<(),Error>(())
/// ```
pub fn solve_formula<F, C, N>(formula: F) -> Result<Option<HashMap<N, Option<Assignment>>>, Error>
where
    F: IntoIterator<Item = C>,
    C: IntoIterator<Item = N>,
    NonZeroI32: TryFrom<N>,
    Error: From<<NonZeroI32 as TryFrom<N>>::Error>,
    N: Abs<Result = N> + std::cmp::Eq + std::hash::Hash + std::marker::Copy,
{
    let mut assignments = HashMap::new();
    let mut solver = Solver::init();

    for clause in formula {
        for literal in clause {
            assignments.insert(literal.abs(), None);
            let n = NonZeroI32::try_from(literal)?;
            solver = solver.add_literal_raw_nonzero(n)?;
        }
        solver = solver.finish_clause();
    }

    let solved_state = solver.solve()?;

    if let Ok(solver) = solved_state.checked_sat() {
        for (literal, assignment) in assignments.iter_mut() {
            let n = NonZeroI32::try_from(*literal)?;
            let literal = Literal::try_from(n)?;
            let value = solver.value(literal)?;
            assignment.replace(value);
        }

        return Ok(Some(assignments));
    }
    Ok(None)
}

/// Decides whether a given formula is satisfiable or not.
/// Abstracts all state details away and constructs a new solver for each invocation.
///
/// In contrast to [`solve_formula`] this does not construct a satisfying assignment.
/// If any of the numerals cannot be converted to [`NonZeroI32`] or is no valid [`Literal`],
/// the function will fail.
/// This variant of the function does not allow zeroes in the formula.
/// ```
/// # use kissat_rs::*;
/// # let x = 1;
/// # let y = 2;
/// # let z = 3;
/// // (~x || y) && (~y || z) && (x || ~z) && (x || y || z) - satisfied by x -> True, y -> True, z -> True
/// let formula1 = vec![vec![-x, y], vec![-y, z], vec![x, -z], vec![x, y, z]];
/// let is_sat1 = decide_formula(formula1)?;
///
/// assert!(is_sat1);
///
/// // (x || y || ~z) && ~x && (x || y || z) && (x || ~y) - unsatisfiable (e.g. by resolution)
/// let formula2 = vec![vec![x, y, -z], vec![-x], vec![x, y, z], vec![x, -y]];
/// let is_sat2 = decide_formula(formula2)?;
///
/// assert!(!is_sat2);
/// # Ok::<(),Error>(())
///```
pub fn decide_formula<F, C, N>(formula: F) -> Result<bool, Error>
where
    F: IntoIterator<Item = C>,
    C: IntoIterator<Item = N>,
    NonZeroI32: TryFrom<N>,
{
    let mut solver = Solver::init();

    for clause in formula {
        solver = solver.add_clause_raw(clause)?;
    }

    let solved_state = solver.solve()?.checked_sat();
    Ok(solved_state.is_ok())
}

/// Variant of [`solve_formula`] that allows zeroes to appear in the iterator to denote the end of a clause.
///
/// Solves a formula and returns a satisfying assignment.
/// Abstracts all state details away and constructs a new solver for each invocation.
/// If any of the numerals cannot be converted to i32 or is no valid [`Literal`],
/// the function will fail.
/// ```
/// # use kissat_rs::*;
/// # let x: i32 = 1;
/// # let y = 2;
/// # let z = 3;
/// let sep = 0;
///
/// // (~x || y) && (~y || z) && (x || ~z) && (x || y || z) - satisfied by x -> True, y -> True, z -> True
/// let formula1 = vec![-x, y, sep, -y, z, sep, x, -z, sep, x, y, z];
///
/// let satisfying_assignment = solve_formula_stream(formula1)?;
/// if let Some(assignments) = satisfying_assignment {
///     assert_eq!(assignments.get(&x).unwrap(), &Some(Assignment::True));
///     assert_eq!(assignments.get(&y).unwrap(), &Some(Assignment::True));
///     assert_eq!(assignments.get(&z).unwrap(), &Some(Assignment::True));
/// }
///
/// // (x || y || ~z) && ~x && (x || y || z) && (x || ~y) - unsatisfiable (e.g. by resolution)
/// let formula2 = vec![x, y, -z, sep, -x, sep, x, y, z, sep, x, -y];
/// let unsat_result = solve_formula_stream(formula2)?;
/// assert_eq!(unsat_result, None);
///
/// # Ok::<(),Error>(())
/// ```
pub fn solve_formula_stream<F, N>(
    formula: F,
) -> Result<Option<HashMap<N, Option<Assignment>>>, Error>
where
    F: IntoIterator<Item = N>,
    i32: TryFrom<N>,
    Error: From<<i32 as TryFrom<N>>::Error>,
    N: Abs<Result = N> + std::cmp::Eq + std::hash::Hash + std::marker::Copy,
{
    let mut assignments = HashMap::new();
    let mut solver = Solver::init();

    for literal in formula {
        assignments.insert(literal.abs(), None);
        solver = solver.add_literal_raw(i32::try_from(literal)?)?;
    }
    solver = solver.finish_clause_check();

    let solved_state = solver.solve()?;

    if let Ok(solver) = solved_state.checked_sat() {
        for (literal, assignment) in assignments.iter_mut() {
            let n = i32::try_from(*literal)?;
            let literal = Literal::try_from(n)?;
            let value = solver.value(literal)?;
            assignment.replace(value);
        }

        return Ok(Some(assignments));
    }
    Ok(None)
}

/// Variant of [`decide_formula`] that allows zeroes to appear in the iterator to denote the end of a clause.
///
/// Decides whether a given formula is satisfiable or not.
/// Abstracts all state details away and constructs a new solver for each invocation.
/// If any of the numerals cannot be converted to i32 or is no valid [`Literal`],
/// the function will fail.
/// ```
/// # use kissat_rs::*;
/// # let x = 1;
/// # let y = 2;
/// # let z = 3;
/// let sep = 0;
///
/// // (~x || y) && (~y || z) && (x || ~z) && (x || y || z) - satisfied by x -> True, y -> True, z -> True
/// let formula1 = vec![-x, y, sep, -y, z, sep, x, -z, sep, x, y, z];
/// let is_sat1 = decide_formula_stream(formula1)?;
///
/// assert!(is_sat1);
///
/// // (x || y || ~z) && ~x && (x || y || z) && (x || ~y) - unsatisfiable (e.g. by resolution)
/// let formula2 = vec![x, y, -z, sep, -x, sep, x, y, z, sep, x, -y];
/// let is_sat2 = decide_formula_stream(formula2)?;
///
/// assert!(!is_sat2);
/// # Ok::<(),Error>(())
///```
pub fn decide_formula_stream<F, N>(formula: F) -> Result<bool, Error>
where
    F: IntoIterator<Item = N>,
    i32: TryFrom<N>,
{
    let mut solver = Solver::init();

    solver = solver.add_multiple_stream(formula)?;

    let solved_state = solver.solve()?.checked_sat();
    Ok(solved_state.is_ok())
}

#[cfg(test)]
mod test {
    use super::*;

    // This is the same test as in kissat-sys but with the safe API.
    #[test]
    fn test_tie_shirt() -> Result<(), Error> {
        let tie = Literal::try_from(1)?;
        let shirt = Literal::try_from(2)?;

        let mut solver = Solver::init();
        solver = solver
            .add_clause(vec![tie.neg()?, shirt])
            .add_clause(vec![tie, shirt])
            .add_clause(vec![tie.neg()?, shirt.neg()?]);

        let solver_result_state = solver.solve()?.checked_sat()?;

        let tie_result = solver_result_state.value(tie)?;
        assert_eq!(tie_result, Assignment::False);
        let shirt_result = solver_result_state.value(shirt)?;
        assert_eq!(shirt_result, Assignment::True);
        Ok(())
    }
}
