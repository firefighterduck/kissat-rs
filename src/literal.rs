use std::{ffi::c_int, ops::Neg};
use super::Error;

pub trait Abs {
    type Result;

    fn abs(self) -> Self::Result;
}

const MAX_VAR: c_int = 30;
/// Constant to denote that maximum identifier for variables in kissat.
/// Any greater value would lead kissat to abort.
pub const EXT_MAX_VAR: c_int = (1 << MAX_VAR) - 1;

/// Literals in kissat must be between [`i32::MIN`] and [`EXT_MAX_VAR`], and
/// their absolute value must be between `0` and [`EXT_MAX_VAR`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(transparent)]
pub struct Literal {
    raw: c_int,
}

pub const CLAUSE_END: Literal = Literal { raw: 0 };

impl TryFrom<c_int> for Literal {
    type Error = Error;

    fn try_from(value: c_int) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(CLAUSE_END),
            v if i32::MIN < v && v.abs() <= EXT_MAX_VAR => Ok(Literal { raw: v }),
            v => Err(Error::ImpossibleLiteral(v)),
        }
    }
}

impl TryFrom<u32> for Literal {
    type Error = Error;

    fn try_from(value: u32) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(CLAUSE_END),
            v if v <= EXT_MAX_VAR as u32 => Ok(Literal { raw: v as i32 }),
            v => Err(Error::ImpossibleLiteral(v as i32)),
        }
    }
}

impl From<Literal> for c_int {
    fn from(val: Literal) -> Self {
        val.raw
    }
}

impl Neg for Literal {
    type Output = Result<Self, Error>;

    fn neg(self) -> Self::Output {
        Self::try_from(-self.raw)
    }
}

impl Abs for Literal {
    type Result = Result<Self, Error>;

    fn abs(self) -> Self::Result {
        Self::try_from(self.raw.abs())
    }
}

impl Abs for c_int {
    type Result = c_int;

    fn abs(self) -> Self::Result {
        self.abs()
    }
}

impl Abs for u32 {
    type Result = u32;

    fn abs(self) -> Self::Result {
        self
    }
}