use derive_try_from_primitive::TryFromPrimitive;
use kissat_sys::{kissat, kissat_add, kissat_init, kissat_release, kissat_solve, kissat_value};
use std::{convert::TryFrom, os::raw::c_int};

type Literal = c_int;
const CLAUSE_END: Literal = 0;

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

pub trait State {}
pub trait SAT: State {}
pub trait UNSAT: State {}
pub trait INPUT: State {}

#[derive(Debug)]
pub enum AnyState {
    INPUT,
    SAT,
    UNSAT,
}
impl State for AnyState {}
impl From<SolverResult> for AnyState {
    fn from(result: SolverResult) -> Self {
        match result {
            SolverResult::Interrupted => AnyState::INPUT,
            SolverResult::Satisfiable => AnyState::SAT,
            SolverResult::Unsatisfiable => AnyState::UNSAT,
        }
    }
}

#[derive(Debug)]
pub struct INPUTState {
    internal: (),
}
impl INPUTState {
    pub(crate) fn new() -> Self {
        INPUTState { internal: () }
    }
}
impl State for INPUTState {}
impl INPUT for INPUTState {}
impl TryFrom<AnyState> for INPUTState {
    type Error = ConversionError;

    fn try_from(value: AnyState) -> Result<Self, Self::Error> {
        match value {
            AnyState::INPUT => Ok(INPUTState::new()),
            state => Err(ConversionError(format!(
                "Cannot convert from {:?} to INPUTState!",
                state
            ))),
        }
    }
}

#[derive(Debug)]
pub struct SATState {
    internal: (),
}
impl SATState {
    pub(crate) fn new() -> Self {
        SATState { internal: () }
    }
}
impl State for SATState {}
impl SAT for SATState {}
impl TryFrom<AnyState> for SATState {
    type Error = ConversionError;

    fn try_from(value: AnyState) -> Result<Self, Self::Error> {
        match value {
            AnyState::SAT => Ok(SATState::new()),
            state => Err(ConversionError(format!(
                "Cannot convert from {:?} to SATState!",
                state
            ))),
        }
    }
}

#[derive(Debug)]
pub struct UNSATState {
    internal: (),
}
impl UNSATState {
    pub(crate) fn new() -> Self {
        UNSATState { internal: () }
    }
}
impl State for UNSATState {}
impl UNSAT for UNSATState {}
impl TryFrom<AnyState> for UNSATState {
    type Error = ConversionError;

    fn try_from(value: AnyState) -> Result<Self, Self::Error> {
        match value {
            AnyState::UNSAT => Ok(UNSATState::new()),
            state => Err(ConversionError(format!(
                "Cannot convert from {:?} to UNSATState!",
                state
            ))),
        }
    }
}

#[derive(Debug)]
pub struct ErrorState;
impl std::fmt::Display for ErrorState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Solver error! Kissat was called in an unexpected state!")
    }
}
impl std::error::Error for ErrorState {}

#[derive(Debug)]
pub struct ConversionError(String);

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("State conversion error")]
    StateConversionError(ConversionError),
    #[error("Internal solver error! Solver in erroneous state")]
    InternalError(ErrorState),
}

impl From<ConversionError> for Error {
    fn from(error: ConversionError) -> Self {
        Self::StateConversionError(error)
    }
}

impl From<ErrorState> for Error {
    fn from(error: ErrorState) -> Self {
        Self::InternalError(error)
    }
}

pub struct Solver {
    solver: *mut kissat,
}

impl Solver {
    pub fn init() -> (Self, impl INPUT) {
        let solver_pt;
        unsafe {
            solver_pt = kissat_init();
        }
        (Solver { solver: solver_pt }, INPUTState::new())
    }

    pub fn add<S: State>(&mut self, literal: Literal, _state: S) -> impl INPUT {
        unsafe {
            kissat_add(self.solver, literal);
        }
        INPUTState::new()
    }

    pub fn add_multiple<I, S>(&mut self, literals: I, _state: S) -> impl INPUT
    where
        I: IntoIterator<Item = Literal>,
        S: State,
    {
        for literal in literals {
            let _ = self.add(literal, INPUTState::new());
        }
        INPUTState::new()
    }

    pub fn add_clause<I, S>(&mut self, clause: I, _state: S) -> impl INPUT
    where
        I: IntoIterator<Item = Literal>,
        S: State,
    {
        let _ = self.add_multiple(clause, INPUTState::new());
        self.add(CLAUSE_END, INPUTState::new())
    }

    pub fn solve<S: State>(&mut self, _state: S) -> Result<(SolverResult, AnyState), Error> {
        let result;
        unsafe {
            result = kissat_solve(self.solver);
        }
        let solver_result = SolverResult::try_from(result);
        solver_result
            .map(|result| (result, AnyState::from(result)))
            .map_err(|_| Error::InternalError(ErrorState))
    }

    pub fn value<S: SAT>(
        &self,
        literal: Literal,
        _state: S,
    ) -> Result<(Assignment, impl SAT), Error> {
        use Assignment::*;

        let value;
        unsafe {
            value = kissat_value(self.solver, literal);
        }

        match value {
            0 => Ok((Both, SATState::new())),
            n if n == literal => Ok((True, SATState::new())),
            n if n == -literal => Ok((False, SATState::new())),
            _ => Err(Error::InternalError(ErrorState)),
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

        let (mut solver, state) = Solver::init();
        let state = solver.add_clause(vec![-tie, shirt], state);
        let state = solver.add_clause(vec![tie, shirt], state);
        let state = solver.add_clause(vec![-tie, -shirt], state);

        let (solver_result, state) = solver.solve(state)?;
        assert_eq!(solver_result, SolverResult::Satisfiable);
        let sat_state = SATState::try_from(state)?;

        let (tie_result, sat_state) = solver.value(tie, sat_state)?;
        assert_eq!(tie_result, Assignment::False);
        let (shirt_result, _) = solver.value(shirt, sat_state)?;
        assert_eq!(shirt_result, Assignment::True);
        Ok(())
    }
}
