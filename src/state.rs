use std::convert::TryFrom;

use crate::{Literal, SolverResult};

/// State is used to encode arbitrary start states.
pub trait State {}
pub trait SAT: State {}
pub trait UNSAT: State {}
pub trait INPUT: State {}

/// AnyState provides a safe way to encode variable
/// end state that can also be safely converted to the actual state.
#[derive(Debug)]
pub enum AnyState {
    INPUT(INPUTState),
    SAT(SATState),
    UNSAT(UNSATState),
}
impl State for AnyState {}
impl From<SolverResult> for AnyState {
    fn from(result: SolverResult) -> Self {
        match result {
            SolverResult::Interrupted => AnyState::INPUT(INPUTState::new()),
            SolverResult::Satisfiable => AnyState::SAT(SATState::new()),
            SolverResult::Unsatisfiable => AnyState::UNSAT(UNSATState::new()),
        }
    }
}

/// INPUTState is the actual state type which encodes
/// that the solver received input in the last step.
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
            AnyState::INPUT(input) => Ok(input),
            state => Err(ConversionError(format!(
                "Cannot convert from {:?} to INPUTState!",
                state
            ))),
        }
    }
}

/// SATState is the actual state type which encodes
/// that the solver has found the given formula to be
/// satisfiable in a previous step and has not received
/// more input afterwards.
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
            AnyState::SAT(sat) => Ok(sat),
            state => Err(ConversionError(format!(
                "Cannot convert from {:?} to SATState!",
                state
            ))),
        }
    }
}

/// UNSATState is the actual state type which encodes
/// that the solver has found the given formula to be
/// unsatisfiable in a previous step and has not received
/// more input afterwards.
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
            AnyState::UNSAT(unsat) => Ok(unsat),
            state => Err(ConversionError(format!(
                "Cannot convert from {:?} to UNSATState!",
                state
            ))),
        }
    }
}

#[derive(Debug)]
pub struct ConversionError(String);

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("State conversion error")]
    StateConversionError(ConversionError),
    #[error("Literal was not assigned a value")]
    UnassignedLiteral(Literal),
    #[error("Unknown solver result state")]
    UnknownSolverResult,
}

impl From<ConversionError> for Error {
    fn from(error: ConversionError) -> Self {
        Self::StateConversionError(error)
    }
}
