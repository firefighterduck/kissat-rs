use std::{convert::{Infallible, TryFrom}, ffi::c_int, num::TryFromIntError};

use crate::{Literal, Solver, SolverResult};

/// State is used to encode arbitrary start states.
pub trait State: Default {}
pub trait NoInput: State {}

/// AnyState provides a safe way to encode variable
/// end state that can also be safely converted to the actual state.
#[derive(Debug, Clone, Copy)]
pub enum AnyState {
    /// If the solver returns the Interrupted result, we also go back into `Input` state.
    Input,
    Sat,
    Unsat,
}
impl Default for AnyState {
    fn default() -> Self {
        Self::Input
    }
}
impl State for AnyState {}
impl From<SolverResult> for AnyState {
    fn from(result: SolverResult) -> Self {
        match result {
            SolverResult::Interrupted => AnyState::Input,
            SolverResult::Satisfiable => AnyState::Sat,
            SolverResult::Unsatisfiable => AnyState::Unsat,
        }
    }
}

/// INPUTState is the actual state type which encodes
/// that the solver received input in the last step.
#[derive(Debug,Default)]
pub enum INPUTState {
    #[default]
    InputFinished,
    OpenClause
}
impl State for INPUTState {}
impl TryFrom<AnyState> for INPUTState {
    type Error = ConversionError;

    fn try_from(value: AnyState) -> Result<Self, Self::Error> {
        match value {
            AnyState::Input => Ok(INPUTState::InputFinished),
            state => Err(ConversionError(format!(
                "Cannot convert from {state:?} to INPUTState!"
            ))),
        }
    }
}

/// SATState is the actual state type which encodes
/// that the solver has found the given formula to be
/// satisfiable in a previous step and has not received
/// more input afterwards.
#[derive(Debug, Default)]
pub struct SATState;
impl State for SATState {}
impl NoInput for SATState {}
impl TryFrom<AnyState> for SATState {
    type Error = ConversionError;

    fn try_from(value: AnyState) -> Result<Self, Self::Error> {
        match value {
            AnyState::Sat => Ok(SATState),
            state => Err(ConversionError(format!(
                "Cannot convert from {state:?} to SATState!"
            ))),
        }
    }
}

/// UNSATState is the actual state type which encodes
/// that the solver has found the given formula to be
/// unsatisfiable in a previous step and has not received
/// more input afterwards.
#[derive(Debug, Default)]
pub struct UNSATState;
impl State for UNSATState {}
impl NoInput for UNSATState {}
impl TryFrom<AnyState> for UNSATState {
    type Error = ConversionError;

    fn try_from(value: AnyState) -> Result<Self, Self::Error> {
        match value {
            AnyState::Unsat => Ok(UNSATState),
            state => Err(ConversionError(format!(
                "Cannot convert from {state:?} to UNSATState!"
            ))),
        }
    }
}

#[derive(Debug)]
pub struct ConversionError(pub String);

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("State conversion error")]
    StateConversion(ConversionError),
    #[error("Literal was not assigned a value")]
    UnassignedLiteral(Literal),
    #[error("Literal value not supported by kissat")]
    ImpossibleLiteral(c_int),
    #[error("Unknown solver result state")]
    UnknownSolverResult,
    #[error("Clause was not finished before calling solve")]
    UnrecoverableOpenClauseWhenSolving,
    #[error("Value does not fit into i32 used for literals")]
    IncompatibleNumeral
}

#[derive(thiserror::Error,Debug)]
pub enum Error2 {
    #[error("Clause was not finished before calling solve, but can be recovered")]
    RecoverableOpenClauseWhenSolving(Solver<INPUTState>),
    #[error("Wrapped error")]
    WrappedError(Error)
}

impl From<ConversionError> for Error {
    fn from(error: ConversionError) -> Self {
        Self::StateConversion(error)
    }
}

impl From<Error> for Error2 {
    fn from(value: Error) -> Self {
        Self::WrappedError(value)
    }
}

impl From<Error2> for Error {
    fn from(value: Error2) -> Self {
        match value {
            Error2::WrappedError(e) => e,
            Error2::RecoverableOpenClauseWhenSolving(_) => Error::UnrecoverableOpenClauseWhenSolving
        }
    }
}

impl From<TryFromIntError> for Error {
    fn from(_: TryFromIntError) -> Self {
        Self::IncompatibleNumeral
    }
}

impl From<Infallible> for Error {
    fn from(_: Infallible) -> Self {
        unreachable!()
    }
}