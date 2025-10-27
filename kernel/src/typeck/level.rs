use crate::typeck::error::TypeErrorKind;
use crate::typeck::{PrettyPrintContext, TypeError, TypingContext, TypingEnvironment};
use common::{Identifier, PrettyPrint};
use derivative::Derivative;
use parser::ast::item::LevelParameters;
use parser::ast::term::{LevelExpr, LevelExprKind};
use std::cmp::Ordering;
use std::hash::Hash;
use std::io::Write;
use std::ops::Index;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Level(Rc<LevelInner>);

#[derive(Derivative)]
#[derivative(PartialEq)]
#[derivative(Hash)]
#[derive(Debug, Clone, Eq)]
enum LevelInner {
    Zero,
    /// An index into the level parameters of the item this term is a part of
    Parameter {
        index: usize,
        /// The name of the level parameter. For pretty printing only.
        #[derivative(PartialEq = "ignore")]
        #[derivative(Hash = "ignore")]
        name: Identifier,
    },
    Succ(Level),
    Max(Level, Level),
    IMax(Level, Level),
}

#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub struct LevelArgs(pub Vec<Level>);

impl LevelArgs {
    pub fn count(&self) -> usize {
        self.0.len()
    }

    pub fn from_level_parameters(level_parameters: &LevelParameters) -> Self {
        Self(
            level_parameters
                .ids
                .iter()
                .enumerate()
                .map(|(i, id)| Level::parameter(i, *id))
                .collect(),
        )
    }

    pub fn mentions_parameters(&self) -> bool {
        self.0.iter().any(|l| l.mentions_parameters())
    }

    pub fn instantiate_parameters(&self, other: &LevelArgs) -> LevelArgs {
        Self(
            self.0
                .iter()
                .map(|arg| arg.instantiate_parameters(other))
                .collect(),
        )
    }

    pub fn normalize(&self) -> Self {
        Self(self.0.iter().map(|l| l.normalize()).collect())
    }
}

impl Index<usize> for LevelArgs {
    type Output = Level;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl Level {
    pub fn ptr_eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }

    pub fn zero() -> Self {
        Self(Rc::new(LevelInner::Zero))
    }

    pub fn constant(u: usize) -> Self {
        if u == 0 {
            Self::zero()
        } else {
            Self(Rc::new(LevelInner::Succ(Self::constant(u - 1))))
        }
    }

    pub fn parameter(index: usize, name: Identifier) -> Self {
        Self(Rc::new(LevelInner::Parameter { index, name }))
    }

    pub fn succ(&self) -> Self {
        Self(Rc::new(LevelInner::Succ(self.clone())))
    }

    pub fn offset(&self, offset: usize) -> Self {
        if offset == 0 {
            self.clone()
        } else {
            self.succ().offset(offset - 1)
        }
    }

    /// Wrapper for [`Max`] which handles [`Rc`]s
    ///
    /// [`Max`]: LevelInner::Max
    fn max(&self, other: &Self) -> Self {
        Self(Rc::new(LevelInner::Max(self.clone(), other.clone())))
    }

    /// Constructs a level representing the maximum of two levels,
    /// while performing some simple simplifications.
    pub fn smart_max(&self, other: &Self) -> Self {
        use LevelInner::*;

        // If the arguments are the same, just take one
        if self == other {
            self.clone()
        } else {
            match (&*self.0, &*other.0) {
                (Zero, _) => other.clone(),
                (_, Zero) => self.clone(),
                (Max(a, b), v) if *v == *a.0 || *v == *b.0 => self.clone(),
                (u, Max(a, b)) if *u == *a.0 || *u == *b.0 => other.clone(),
                (_, _) => {
                    let (u, ou) = self.to_offset();
                    let (v, ov) = other.to_offset();

                    if u == v {
                        if ou >= ov {
                            self.clone()
                        } else {
                            other.clone()
                        }
                    } else {
                        self.max(other)
                    }
                }
            }
        }
    }

    /// Wrapper for [`IMax`] which handles [`Rc`]s
    ///
    /// [`IMax`]: LevelInner::IMax
    fn imax(&self, other: &Self) -> Self {
        Self(Rc::new(LevelInner::IMax(self.clone(), other.clone())))
    }

    /// Constructs a level representing the impredicative maximum of two levels,
    /// while performing some simple simplifications.
    pub fn smart_imax(&self, other: &Self) -> Self {
        use LevelInner::*;

        if other.is_not_zero() {
            self.smart_max(other)
        } else if *other.0 == Zero {
            Self::zero()
        } else if *self == Self::zero() || *self == Self::zero().succ() {
            other.clone()
        } else if self == other {
            self.clone()
        } else if let IMax(a, b) = other.0.as_ref() {
            self.smart_max(a).smart_imax(b)
        } else {
            self.imax(other)
        }
    }

    /// Checks if a level is guaranteed to be non-zero
    fn is_not_zero(&self) -> bool {
        use LevelInner::*;

        match &*self.0 {
            Zero | Parameter { .. } => false,
            Succ(_) => true,
            Max(a, b) => a.is_not_zero() || b.is_not_zero(),
            IMax(_, b) => b.is_not_zero(),
        }
    }

    /// Strips [`Succ`]s from a level, returning the inner level and the constant
    /// offset which has been removed.
    ///
    /// [`Succ`]: LevelInner::Succ
    fn to_offset(&self) -> (Self, usize) {
        match &*self.0 {
            LevelInner::Succ(u) => {
                let (u, o) = u.to_offset();
                (u, o + 1)
            }
            _ => (self.clone(), 0),
        }
    }

    pub fn mentions_parameters(&self) -> bool {
        match &*self.0 {
            LevelInner::Zero => false,
            LevelInner::Parameter { .. } => true,
            LevelInner::Succ(l) => l.mentions_parameters(),
            LevelInner::Max(a, b) => a.mentions_parameters() || b.mentions_parameters(),
            LevelInner::IMax(a, b) => a.mentions_parameters() || b.mentions_parameters(),
        }
    }

    pub fn instantiate_parameters(&self, args: &LevelArgs) -> Self {
        use LevelInner::*;

        match &*self.0 {
            Zero => self.clone(),
            Parameter { index: p, .. } => args[*p].clone(),
            Succ(s_old) => {
                let s = s_old.instantiate_parameters(args);

                if s.ptr_eq(s_old) {
                    self.clone()
                } else {
                    s.succ()
                }
            }
            Max(u_old, v_old) => {
                let u = u_old.instantiate_parameters(args);
                let v = v_old.instantiate_parameters(args);

                if u.ptr_eq(u_old) && v.ptr_eq(v_old) {
                    self.clone()
                } else {
                    u.smart_max(&v)
                }
            }
            IMax(u_old, v_old) => {
                let u = u_old.instantiate_parameters(args);
                let v = v_old.instantiate_parameters(args);

                if u.ptr_eq(u_old) && v.ptr_eq(v_old) {
                    self.clone()
                } else {
                    u.smart_imax(&v)
                }
            }
        }
    }

    /// A number representing the type of the level
    fn tag(&self) -> usize {
        match *self.0 {
            LevelInner::Zero => 0,
            LevelInner::Parameter { .. } => 1,
            LevelInner::Succ(_) => 2,
            LevelInner::Max(_, _) => 3,
            LevelInner::IMax(_, _) => 4,
        }
    }

    /// A total order on [`LevelInner`]s, where zero is the initial element and
    /// `Succ(u)` is the immediate successor of `u`.
    fn cmp_norm(&self, other: &Self) -> Ordering {
        use LevelInner::*;

        let (u, ou) = self.to_offset();
        let (v, ov) = other.to_offset();
        if u == v {
            ou.cmp(&ov)
        } else {
            match (&*u.0, &*v.0) {
                (Parameter { index: pu, .. }, Parameter { index: pv, .. }) => pu.cmp(pv),
                (Max(au, bu), Max(av, bv)) | (IMax(au, bu), IMax(av, bv)) => {
                    if au == av {
                        bu.cmp_norm(bv)
                    } else {
                        au.cmp_norm(av)
                    }
                }
                (_, _) => u.tag().cmp(&v.tag()),
            }
        }
    }

    /// Collects the arguments to nested [`Max`] expressions into a single vector.
    /// Arguments are normalized, so any level which normalizes to a [`Max`] will have its
    /// arguments collected as well.
    ///
    /// [`Max`]: LevelInner::Max
    fn collect_max_args(&self, buf: &mut Vec<Self>) {
        use LevelInner::*;

        match &*self.0 {
            Max(a, b) => {
                a.normalize().collect_max_args(buf);
                b.normalize().collect_max_args(buf);
            }
            _ => buf.push(self.clone()),
        }
    }

    /// Normalizes a [`Max`] level. A constant offset of `offset` will be added to each argument.
    ///
    /// [`Max`]: LevelInner::Max
    fn normalize_max(&self, offset: usize) -> Self {
        let mut args = Vec::new();
        // Collect the arguments to the `Max`
        self.collect_max_args(&mut args);

        // Sort the args in reverse by `cmp_norm`. This means that arguments which are identical except for
        // a constant offset are next to each other, with the largest one first.
        args.sort_unstable_by(|u, v| u.cmp_norm(v).reverse());
        // Deduplicating the arguments by their non-constant part will therefore
        // only keep the largest of each group.
        args.dedup_by(|u, v| u.to_offset().0 == v.to_offset().0);

        // If the last argument is a constant, it might be redundant if another argument is guaranteed
        // to be larger than it.
        let (last_arg, last_offset) = args.last().unwrap().to_offset();
        if *last_arg.0 == LevelInner::Zero && args.len() > 1 {
            // Find the largest constant offset among the other arguments
            let largest_offset = args
                .iter()
                .take(args.len() - 1)
                .map(|u| u.to_offset().1)
                .max()
                .unwrap();

            if last_offset <= largest_offset {
                args.pop();
            }
        }

        // Offset each argument by `offset` and combine them back into a single level
        let mut args = args.into_iter().map(|u| u.offset(offset));
        let first = args.next().unwrap();
        args.fold(first, |acc, u| u.max(&acc))
    }

    /// Converts a level to a normalized form which is equivalent to it.
    /// Any two equivalent levels will convert to the same normalized form.
    pub fn normalize(&self) -> Self {
        use LevelInner::*;

        let (u, o) = self.to_offset();

        match &*u.0 {
            Succ(_) => unreachable!(),
            Zero | Parameter { .. } => self.clone(),
            Max(_, _) => u.normalize_max(o),
            IMax(a_old, b_old) => {
                let a = a_old.normalize();
                let b = b_old.normalize();

                // imax u (imax v w) = imax (max u v) w
                if let IMax(b1, b2) = b.0.as_ref() {
                    a.smart_max(b1).smart_imax(b2).offset(o).normalize()
                } else if b.is_not_zero() {
                    a.max(&b).normalize_max(o)
                } else {
                    a.smart_imax(&b).offset(o)
                }
            }
        }
    }

    /// Checks whether two levels are definitionally equal i.e. if they are guaranteed to be equal
    /// for any valuation of their parameters
    pub fn def_eq(&self, other: &Self) -> bool {
        self.normalize() == other.normalize()
    }

    /// Checks whether one level is guaranteed to be greater than or equal to another
    pub fn is_geq(&self, other: &Self) -> bool {
        let u = self.normalize();
        let v = other.normalize();

        if u == v || *v.0 == LevelInner::Zero {
            true
        } else if let LevelInner::Max(a, b) = &*v.0 {
            u.is_geq(a) && u.is_geq(b)
        } else if let LevelInner::Max(a, b) = &*u.0
            && (a.is_geq(&v) || b.is_geq(&v))
        {
            true
        } else if let LevelInner::IMax(a, b) = &*v.0 {
            u.is_geq(&a) && u.is_geq(&b)
        } else if let LevelInner::IMax(_, b) = &*u.0 {
            b.is_geq(&v)
        } else {
            let (u, ou) = u.to_offset();
            let (v, ov) = v.to_offset();

            if u == v || *v.0 == LevelInner::Zero {
                ou >= ov
            } else if ou == ov && ou > 0 {
                u.is_geq(&v)
            } else {
                false
            }
        }
    }
}

impl TypingEnvironment {
    pub fn set_level_params(&mut self, params: LevelParameters) -> Result<(), TypeError> {
        if let Some(id) = params.find_duplicate() {
            Err(TypeError {
                span: params.span,
                kind: TypeErrorKind::DuplicateLevelParameter(id),
            })
        } else {
            self.level_parameters = Some(params);
            Ok(())
        }
    }

    pub fn clear_level_params(&mut self) {
        self.level_parameters = None;
    }

    pub fn resolve_level(&self, arg: &LevelExpr) -> Result<Level, TypeError> {
        match &arg.kind {
            LevelExprKind::Literal(l) => {
                if *l > 8 {
                    Err(TypeError {
                        span: arg.span.clone(),
                        kind: TypeErrorKind::LevelLiteralTooBig(*l),
                    })
                } else {
                    Ok(Level::constant(*l))
                }
            }
            LevelExprKind::Parameter(name) => {
                let index =
                    self.level_parameters
                        .as_ref()
                        .unwrap()
                        .lookup(name)
                        .ok_or(TypeError {
                            span: arg.span.clone(),
                            kind: TypeErrorKind::LevelParameterNotFound(*name),
                        })?;
                Ok(Level::parameter(index, *name))
            }
            LevelExprKind::Succ(u) => {
                let u = self.resolve_level(u)?;
                Ok(u.succ())
            }
            LevelExprKind::Max(u, v) => {
                let u = self.resolve_level(u)?;
                let v = self.resolve_level(v)?;
                Ok(u.smart_max(&v))
            }
            LevelExprKind::IMax(u, v) => {
                let u = self.resolve_level(u)?;
                let v = self.resolve_level(v)?;
                Ok(u.smart_imax(&v))
            }

            LevelExprKind::Underscore => {
                Err(TypeError::unsupported(arg.span.clone(), "Level inference"))
            }
            LevelExprKind::Malformed => {
                Err(TypeError::unsupported(arg.span.clone(), "Malformed levels"))
            }
        }
    }
}

impl<'a> TypingContext<'a> {
    pub fn resolve_level(&self, arg: &LevelExpr) -> Result<Level, TypeError> {
        match self {
            TypingContext::Root(env) => env.resolve_level(arg),
            TypingContext::Binders { parent, .. } => parent.resolve_level(arg),
        }
    }

    pub fn resolve_level_args(
        &self,
        level_args: parser::ast::term::LevelArgs,
    ) -> Result<LevelArgs, TypeError> {
        let mut v = Vec::new();

        for arg in level_args.iter() {
            v.push(self.resolve_level(arg)?)
        }

        Ok(LevelArgs(v))
    }
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for LevelArgs {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext<'a>,
    ) -> std::io::Result<()> {
        if self.0.is_empty() {
            return Ok(());
        };

        write!(out, ".{{")?;
        for arg in &self.0 {
            arg.pretty_print(out, context)?;
            write!(out, ", ")?;
        }
        write!(out, "}}")
    }
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for Level {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext<'a>,
    ) -> std::io::Result<()> {
        let (u, o) = self.to_offset();

        if *u.0 == LevelInner::Zero {
            return write!(out, "{o}");
        }

        if o != 0 {
            write!(out, "(")?;
        }

        match &*u.0 {
            LevelInner::Zero => write!(out, "0")?,
            LevelInner::Parameter { name, .. } => name.pretty_print(out, &context.interner())?,
            LevelInner::Succ(u) => {
                write!(out, "(succ ")?;
                u.pretty_print(out, context)?;
                write!(out, ")")?;
            }
            LevelInner::Max(u, v) => {
                write!(out, "(max ")?;
                u.pretty_print(out, context)?;
                write!(out, " ")?;
                v.pretty_print(out, context)?;
                write!(out, ")")?;
            }
            LevelInner::IMax(u, v) => {
                write!(out, "(imax ")?;
                u.pretty_print(out, context)?;
                write!(out, " ")?;
                v.pretty_print(out, context)?;
                write!(out, ")")?
            }
        }

        if o != 0 {
            write!(out, " + {o})")?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use parser::ast::item::LevelParameters;
    use parser::error::Span;

    #[test]
    fn test_instantiate_parameters() {
        let param_0 = Level::parameter(0, Identifier::dummy(0));
        let param_1 = Level::parameter(1, Identifier::dummy(1));
        let param_2 = Level::parameter(2, Identifier::dummy(2));
        let param_20 = Level::parameter(20, Identifier::dummy(20));

        let param_list = LevelArgs(vec![Level::zero(), param_0.clone(), param_20.succ()]);

        assert_eq!(
            Level::zero().instantiate_parameters(&param_list),
            Level::zero()
        );
        assert_eq!(
            Level::zero()
                .max(&Level::zero().succ())
                .instantiate_parameters(&param_list),
            Level::zero().max(&Level::zero().succ())
        );
        assert_eq!(
            Level::zero()
                .imax(&Level::zero())
                .instantiate_parameters(&param_list),
            Level::zero().imax(&Level::zero())
        );

        assert_eq!(param_0.instantiate_parameters(&param_list), Level::zero());
        assert_eq!(param_1.instantiate_parameters(&param_list), param_0);
        assert_eq!(param_2.instantiate_parameters(&param_list), param_20.succ());

        assert_eq!(
            param_0.succ().instantiate_parameters(&param_list),
            Level::zero().succ()
        );
        assert_eq!(
            param_1.max(&param_2).instantiate_parameters(&param_list),
            param_0.max(&param_20.succ())
        );
        assert_eq!(
            param_0.imax(&param_2).instantiate_parameters(&param_list),
            param_20.succ() // The imax gets removed by `smart_imax` because the LHS is zero
        );
    }

    #[test]
    fn test_cmp_norm() {
        let param_0 = Level::parameter(0, Identifier::dummy(0));
        let param_1 = Level::parameter(1, Identifier::dummy(1));
        let param_2 = Level::parameter(2, Identifier::dummy(2));

        assert_eq!(Level::zero().cmp_norm(&Level::zero()), Ordering::Equal);

        // Zero should be less than everything else
        assert_eq!(
            Level::zero().cmp_norm(&Level::zero().succ()),
            Ordering::Less
        );
        assert_eq!(Level::zero().cmp_norm(&param_0), Ordering::Less);
        assert_eq!(
            Level::zero().cmp_norm(&param_0.max(&Level::zero())),
            Ordering::Less
        );
        assert_eq!(
            Level::zero().cmp_norm(&param_1.imax(&param_0)),
            Ordering::Less
        );

        // When comparing parameters, the constant offset only matters if the parameters are equal
        assert_eq!(param_0.cmp_norm(&param_1), Ordering::Less);
        assert_eq!(param_0.succ().cmp_norm(&param_1), Ordering::Less);
        assert_eq!(param_0.cmp_norm(&param_1.succ()), Ordering::Less);

        assert_eq!(param_0.cmp_norm(&param_0), Ordering::Equal);
        assert_eq!(param_0.succ().cmp_norm(&param_0), Ordering::Greater);
        assert_eq!(param_0.cmp_norm(&param_0.succ()), Ordering::Less);

        // When comparing Max and IMax levels, the first parameter takes precedence over the second
        assert_eq!(
            param_0.max(&param_1).cmp_norm(&param_0.max(&param_0)),
            Ordering::Greater
        );
        assert_eq!(
            param_0.max(&param_1).cmp_norm(&param_0.max(&param_1)),
            Ordering::Equal
        );
        assert_eq!(
            param_0.max(&param_1).cmp_norm(&param_0.max(&param_2)),
            Ordering::Less
        );

        assert_eq!(
            param_0.imax(&param_1).cmp_norm(&param_1.imax(&param_0)),
            Ordering::Less
        );
        assert_eq!(
            param_0.imax(&param_1).cmp_norm(&param_1.imax(&param_1)),
            Ordering::Less
        );
        assert_eq!(
            param_0.imax(&param_1).cmp_norm(&param_1.imax(&param_2)),
            Ordering::Less
        );

        assert_eq!(
            param_1.max(&param_1).cmp_norm(&param_0.max(&param_0)),
            Ordering::Greater
        );
        assert_eq!(
            param_1.max(&param_1).cmp_norm(&param_0.max(&param_1)),
            Ordering::Greater
        );
        assert_eq!(
            param_1.max(&param_1).cmp_norm(&param_0.max(&param_2)),
            Ordering::Greater
        );

        // Imax is always greater than max, even when the parameters and/or constant offset are less
        assert_eq!(
            param_0
                .imax(&param_0)
                .cmp_norm(&param_1.max(&param_1).succ()),
            Ordering::Greater
        );
        assert_eq!(
            param_1
                .max(&param_1)
                .succ()
                .cmp_norm(&param_0.imax(&param_0)),
            Ordering::Less
        );
    }

    #[test]
    fn test_normalize() {
        let param_0 = Level::parameter(0, Identifier::dummy(0));
        let param_1 = Level::parameter(1, Identifier::dummy(1));

        // Basic cases
        assert_eq!(Level::zero().normalize(), Level::zero());
        assert_eq!(Level::zero().succ().normalize(), Level::zero().succ());
        assert_eq!(param_0.normalize(), param_0);
        assert_eq!(param_1.succ().normalize(), param_1.succ());

        // Normalize reduces any expression with no parameters to a constant
        assert_eq!(Level::zero().max(&Level::zero()).normalize(), Level::zero());
        assert_eq!(
            Level::constant(1)
                .imax(&Level::constant(2).max(&Level::constant(3).imax(&Level::zero())))
                .normalize(),
            Level::constant(2)
        );
    }

    #[test]
    fn test_normalize_imax() {
        let param_0 = Level::parameter(0, Identifier::dummy(0));
        let param_1 = Level::parameter(1, Identifier::dummy(1));
        let param_2 = Level::parameter(2, Identifier::dummy(2));

        // Imax becomes max if the RHS is not zero
        assert_eq!(
            param_0.imax(&param_1.succ()).normalize(),
            param_0.max(&param_1.succ())
        );
        assert_eq!(
            param_0.imax(&param_1.max(&Level::constant(1))).normalize(),
            Level::constant(1).max(&param_0.max(&param_1))
        );

        // Imax becomes zero if the RHS is zero
        assert_eq!(param_0.imax(&Level::zero()).normalize(), Level::zero());
        assert_eq!(
            param_0.imax(&Level::zero().max(&Level::zero())).normalize(),
            Level::zero()
        );
        assert_eq!(
            param_0.imax(&param_1.imax(&Level::zero())).normalize(),
            Level::zero()
        );

        // Imax simplifies if both arguments are identical
        assert_eq!(param_0.imax(&param_0).normalize(), param_0);
        assert_eq!(
            param_0
                .max(&param_1)
                .imax(&param_1.max(&param_0))
                .normalize(),
            param_0.max(&param_1)
        );

        // Imax becomes RHS if LHS is zero or one
        assert_eq!(Level::zero().imax(&param_0).normalize(), param_0);
        assert_eq!(Level::zero().smart_imax(&param_0).normalize(), param_0);
        assert_eq!(
            Level::zero()
                .max(&Level::zero())
                .imax(&param_1.max(&param_0))
                .normalize(),
            param_0.max(&param_1)
        );

        // imax u (imax v w) becomes imax (max u v) w
        let imax_uvw = param_0.imax(&param_1.imax(&param_2));
        let imax_vuw = param_1.imax(&param_0.imax(&param_2));
        let imax_max = param_0.max(&param_1).imax(&param_2);
        assert_eq!(imax_uvw.normalize(), imax_max);
        assert_eq!(imax_vuw.normalize(), imax_max);
        assert_eq!(param_1.imax(&imax_max).normalize(), imax_max);
        assert_eq!(
            imax_uvw.succ().max(&imax_vuw.succ()).succ().normalize(),
            imax_max.succ().succ().normalize()
        )
    }

    #[test]
    fn test_normalize_max() {
        let param_0 = Level::parameter(0, Identifier::dummy(0));
        let param_1 = Level::parameter(1, Identifier::dummy(1));
        let param_2 = Level::parameter(2, Identifier::dummy(2));
        let param_3 = Level::parameter(3, Identifier::dummy(3));

        // Constant arguments are removed if another argument is guaranteed to be at least as large
        assert_eq!(param_0.max(&Level::zero()).normalize(), param_0); // param_0 >= 0
        assert_eq!(
            param_0.max(&Level::zero().succ()).normalize(),
            Level::zero().succ().max(&param_0) // param_0 is not guaranteed to be >= 1 ...
        );
        assert_eq!(
            param_0.succ().max(&Level::zero().succ()).normalize(),
            param_0.succ() // ... but param_0 + 1 is
        );

        // Normalize sorts arguments
        assert_eq!(param_0.max(&param_1).normalize(), param_0.max(&param_1));
        assert_eq!(param_1.max(&param_0).normalize(), param_0.max(&param_1));
        assert_eq!(param_0.max(&param_0).normalize(), param_0);
        assert_eq!(param_0.max(&Level::zero()).normalize(), param_0);
        assert_eq!(
            param_0.max(&Level::zero().succ()).normalize(),
            Level::zero().succ().max(&param_0)
        );
        assert_eq!(
            Level::zero().succ().max(&param_0).normalize(),
            Level::zero().succ().max(&param_0)
        );

        // Normalize makes everything right associative
        assert_eq!(
            param_1.max(&param_2).max(&param_0).normalize(),
            param_0.max(&param_1.max(&param_2))
        );
        assert_eq!(
            param_0
                .max(&param_2.max(&param_3).max(&param_1))
                .normalize(),
            param_0.max(&param_1.max(&param_2.max(&param_3)))
        );

        // Normalize removes duplicates
        assert_eq!(param_1.max(&param_1).normalize(), param_1);
        assert_eq!(param_1.max(&param_1.succ()).normalize(), param_1.succ());
        assert_eq!(
            param_0.max(&param_1.imax(&param_1)).normalize(),
            param_0.max(&param_1)
        );

        // Normalize pushes `succ`s to leaves
        assert_eq!(
            param_0
                .max(&param_1.succ())
                .succ()
                .max(&param_2)
                .succ()
                .normalize(),
            param_0
                .succ()
                .succ()
                .max(&param_1.succ().succ().succ().max(&param_2.succ()))
        );
    }

    #[test]
    fn test_def_eq() {
        let param_0 = Level::parameter(0, Identifier::dummy(0));
        let param_1 = Level::parameter(1, Identifier::dummy(1));

        assert!(Level::zero().def_eq(&Level::zero()));
        assert!(Level::zero().succ().def_eq(&Level::zero().succ()));
        assert!(!Level::zero().def_eq(&Level::zero().succ()));

        assert!(
            param_0
                .succ()
                .max(&param_1.succ())
                .def_eq(&param_1.max(&param_0).succ())
        );
    }

    #[test]
    fn test_is_geq() {
        let param_0 = Level::parameter(0, Identifier::dummy(0));
        let param_1 = Level::parameter(1, Identifier::dummy(1));
        let param_2 = Level::parameter(2, Identifier::dummy(2));

        assert!(param_0.is_geq(&param_0));
        assert!(param_0.succ().is_geq(&param_0));
        assert!(!param_0.is_geq(&param_0.succ()));
        assert!(param_0.succ().is_geq(&param_0.succ()));

        assert!(!param_0.is_geq(&param_1));
        assert!(!param_1.is_geq(&param_0));
        assert!(!param_1.succ().is_geq(&param_0));
        assert!(!param_1.succ().is_geq(&param_0.succ()));

        assert!(param_0.max(&param_1).is_geq(&param_0));
        assert!(param_0.max(&param_1).is_geq(&param_1));
        assert!(!param_0.max(&param_1).is_geq(&param_2));

        assert!(
            param_0
                .max(&param_1)
                .max(&param_2)
                .is_geq(&param_0.max(&param_2))
        );

        assert!(!param_0.is_geq(&param_1.imax(&param_0)));
        assert!(!param_1.is_geq(&param_1.imax(&param_0)));
        assert!(param_0.max(&param_1).is_geq(&param_1.imax(&param_0)));
        assert!(!param_0.imax(&param_1).is_geq(&param_1.imax(&param_0)));

        assert!(param_0.imax(&param_1).is_geq(&param_1));
        assert!(!param_0.imax(&param_1).is_geq(&param_0));
        assert!(!param_0.imax(&param_1).is_geq(&param_0.max(&param_1)));
    }

    #[test]
    fn test_set_level_params() {
        let mut env = TypingEnvironment::new();

        let id_0 = Identifier::dummy(0);
        let id_1 = Identifier::dummy(1);

        let parameters = LevelParameters::new(&[id_0, id_1]);
        env.set_level_params(parameters)
            .expect("Setting parameters should have succeeded");

        let parameters = LevelParameters::new(&[id_0, id_1, id_0]);
        assert_eq!(
            env.set_level_params(parameters).unwrap_err().kind,
            TypeErrorKind::DuplicateLevelParameter(id_0)
        );
    }

    #[test]
    fn test_resolve_level() {
        let mut env = TypingEnvironment::new();

        let id_0 = Identifier::dummy(0);
        let id_1 = Identifier::dummy(1);
        let id_2 = Identifier::dummy(2);
        let param_0 = Level::parameter(0, id_0);
        let param_1 = Level::parameter(1, id_1);

        let parameters = LevelParameters::new(&[id_0, id_1]);
        env.set_level_params(parameters).unwrap();

        fn l(kind: LevelExprKind) -> LevelExpr {
            LevelExpr {
                span: Span::dummy(),
                kind,
            }
        }

        // Constants
        assert_eq!(
            env.resolve_level(&l(LevelExprKind::Literal(0))).unwrap(),
            Level::zero()
        );
        assert_eq!(
            env.resolve_level(&l(LevelExprKind::Literal(1))).unwrap(),
            Level::zero().succ()
        );
        assert_eq!(
            env.resolve_level(&l(LevelExprKind::Literal(2))).unwrap(),
            Level::zero().succ().succ()
        );

        // Parameters
        assert_eq!(
            env.resolve_level(&l(LevelExprKind::Parameter(id_0)))
                .unwrap(),
            param_0
        );
        assert_eq!(
            env.resolve_level(&l(LevelExprKind::Parameter(id_1)))
                .unwrap(),
            param_1
        );
        assert_eq!(
            env.resolve_level(&l(LevelExprKind::Parameter(id_2)))
                .unwrap_err()
                .kind,
            TypeErrorKind::LevelParameterNotFound(id_2)
        );

        // Max and Imax
        assert_eq!(
            env.resolve_level(&l(LevelExprKind::Max(
                Box::new(l(LevelExprKind::Literal(1))),
                Box::new(l(LevelExprKind::Parameter(id_0)))
            )))
            .unwrap(),
            Level::constant(1).max(&param_0)
        );

        assert_eq!(
            env.resolve_level(&l(LevelExprKind::IMax(
                Box::new(l(LevelExprKind::Succ(Box::new(l(
                    LevelExprKind::Parameter(id_1)
                ))))),
                Box::new(l(LevelExprKind::Succ(Box::new(l(LevelExprKind::Literal(
                    1
                ))))))
            )))
            .unwrap(),
            param_1.succ().max(&Level::constant(2))
        );
    }
}
