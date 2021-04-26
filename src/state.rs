use std::convert::TryFrom;

use crate::{Literal, SolverResult};

pub trait State {}
pub trait SAT: State {}
pub trait UNSAT: State {}
pub trait INPUT: State {}

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
