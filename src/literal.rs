use super::Error;
use std::{
    ffi::c_int,
    mem::transmute,
    num::{NonZero, NonZeroI32},
    ops::Neg,
};

pub trait Abs {
    type Result;

    fn abs(self) -> Self::Result;
}

const MAX_VAR: c_int = 30;
/// Constant to denote that maximum identifier for variables in kissat.
/// Any greater value would lead kissat to abort.
pub const EXT_MAX_VAR: c_int = (1 << MAX_VAR) - 1;

/// Literals in kissat must be between [`i32::MIN`] (exclusive) and [`EXT_MAX_VAR`] (inclusive), and
/// their absolute value must be between `0` and [`EXT_MAX_VAR`] (both inclusive).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Literal(Option<NonZeroI32>);

pub const CLAUSE_END: Literal = Literal(None);

impl TryFrom<c_int> for Literal {
    type Error = Error;

    fn try_from(value: c_int) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(CLAUSE_END),
            v if i32::MIN < v && v.abs() <= EXT_MAX_VAR => Ok(Literal(NonZero::new(v))),
            v => Err(Error::ImpossibleLiteral(v)),
        }
    }
}

impl TryFrom<NonZeroI32> for Literal {
    type Error = Error;

    fn try_from(value: NonZeroI32) -> Result<Self, Self::Error> {
        if NonZeroI32::MIN < value && value.get().abs() <= EXT_MAX_VAR {
            Ok(Literal(Some(value)))
        } else {
            Err(Error::ImpossibleLiteral(value.get()))
        }
    }
}

impl From<Literal> for c_int {
    fn from(val: Literal) -> Self {
        unsafe {
            // SAFETY: Option<NonZeroI32> has a niche optimization and
            // has the same layout as i32.
            transmute::<Option<NonZeroI32>, c_int>(val.0)
        }
    }
}

impl Neg for Literal {
    type Output = Result<Self, Error>;

    fn neg(self) -> Self::Output {
        match self.0 {
            None => Ok(self),
            Some(n) => Self::try_from(-n.get()),
        }
    }
}

impl Abs for Literal {
    type Result = Result<Self, Error>;

    fn abs(self) -> Self::Result {
        match self.0 {
            None => Ok(self),
            Some(n) => Self::try_from(n.get().abs()),
        }
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

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn test_literal_boundaries() -> Result<(), Error> {
        // MIN is not allowed
        let min = i32::MIN;
        assert!(matches!(
            Literal::try_from(min),
            Err(Error::ImpossibleLiteral(_))
        ));

        // EXT_MAX_VAR is allowed
        let max = EXT_MAX_VAR;
        let max_lit = Literal::try_from(max)?;

        // MIN + 1 is not allowed
        let min_lit = Literal::try_from(min + 1);
        assert!(matches!(min_lit, Err(Error::ImpossibleLiteral(_))));

        // - EXT_MAX_VAR is allowed
        let max_neg = max_lit.neg()?;
        assert!(min < max_neg.into());

        // Zero is the clause end.
        let zero_lit = Literal::try_from(0)?;
        assert_eq!(CLAUSE_END, zero_lit);

        Ok(())
    }
}
