//! Helper macros to construct `Expr` and `Cond`.

use vstd::prelude::*;
use std::sync::Arc;
use crate::{Cond, Expr, PrimType};

verus! {

/// A Rust value that `expr!` accepts as an operand.
pub trait ToExpr {
    /// Converts this value to an `Expr`, with an integer bitcast to a literal of its own type.
    fn to_expr(self) -> Arc<Expr>;
}

impl ToExpr for i8 { fn to_expr(self) -> Arc<Expr> { Arc::new(Expr::Lit(self as i64, PrimType::I(8))) } }
impl ToExpr for i16 { fn to_expr(self) -> Arc<Expr> { Arc::new(Expr::Lit(self as i64, PrimType::I(16))) } }
impl ToExpr for i32 { fn to_expr(self) -> Arc<Expr> { Arc::new(Expr::Lit(self as i64, PrimType::I(32))) } }
impl ToExpr for i64 { fn to_expr(self) -> Arc<Expr> { Arc::new(Expr::Lit(self, PrimType::I(64))) } }
impl ToExpr for u8 { fn to_expr(self) -> Arc<Expr> { Arc::new(Expr::Lit(self as i64, PrimType::U(8))) } }
impl ToExpr for u16 { fn to_expr(self) -> Arc<Expr> { Arc::new(Expr::Lit(self as i64, PrimType::U(16))) } }
impl ToExpr for u32 { fn to_expr(self) -> Arc<Expr> { Arc::new(Expr::Lit(self as i64, PrimType::U(32))) } }
impl ToExpr for u64 { fn to_expr(self) -> Arc<Expr> { Arc::new(Expr::Lit(self as i64, PrimType::U(64))) } }
impl ToExpr for isize { fn to_expr(self) -> Arc<Expr> { Arc::new(Expr::Lit(self as i64, PrimType::IWord)) } }
impl ToExpr for usize { fn to_expr(self) -> Arc<Expr> { Arc::new(Expr::Lit(self as i64, PrimType::UWord)) } }
impl ToExpr for Expr { fn to_expr(self) -> Arc<Expr> { Arc::new(self) } }
impl ToExpr for &Expr { fn to_expr(self) -> Arc<Expr> { Arc::new(self.clone()) } }
impl ToExpr for Arc<Expr> { fn to_expr(self) -> Arc<Expr> { self } }

/// A Rust value that `cond!` accepts as an operand.
pub trait ToCond {
    /// Converts this value to a `Cond`.
    fn to_cond(self) -> Arc<Cond>;
}

impl ToCond for Cond { fn to_cond(self) -> Arc<Cond> { Arc::new(self) } }
impl ToCond for &Cond { fn to_cond(self) -> Arc<Cond> { Arc::new(self.clone()) } }
impl ToCond for Arc<Cond> { fn to_cond(self) -> Arc<Cond> { self } }

} // verus!

/// Parses a Rust-like expression into an `Expr`.
#[macro_export]
macro_rules! expr {
    // or := xor ('|' xor)*
    (@or [$($acc:tt)*] $op:ident [$($cur:tt)*] | $($rest:tt)*) =>
        { $crate::expr!(@or [$crate::expr!(@join [$($acc)*] $op xor [$($cur)*])] Or [] $($rest)*) };
    (@or [$($acc:tt)*] $op:ident [$($cur:tt)*] $t:tt $($rest:tt)*) =>
        { $crate::expr!(@or [$($acc)*] $op [$($cur)* $t] $($rest)*) };
    (@or [$($acc:tt)*] $op:ident [$($cur:tt)*]) => { $crate::expr!(@join [$($acc)*] $op xor [$($cur)*]) };

    // xor := and ('^' and)*
    (@xor [$($acc:tt)*] $op:ident [$($cur:tt)*] ^ $($rest:tt)*) =>
        { $crate::expr!(@xor [$crate::expr!(@join [$($acc)*] $op and [$($cur)*])] Xor [] $($rest)*) };
    (@xor [$($acc:tt)*] $op:ident [$($cur:tt)*] $t:tt $($rest:tt)*) =>
        { $crate::expr!(@xor [$($acc)*] $op [$($cur)* $t] $($rest)*) };
    (@xor [$($acc:tt)*] $op:ident [$($cur:tt)*]) => { $crate::expr!(@join [$($acc)*] $op and [$($cur)*]) };
    (@xor $($t:tt)*) => { $crate::expr!(@xor [] Xor [] $($t)*) };

    // and := add ('&' add)*
    (@and [$($acc:tt)*] $op:ident [$($cur:tt)*] & $($rest:tt)*) =>
        { $crate::expr!(@and [$crate::expr!(@join [$($acc)*] $op add [$($cur)*])] And [] $($rest)*) };
    (@and [$($acc:tt)*] $op:ident [$($cur:tt)*] $t:tt $($rest:tt)*) =>
        { $crate::expr!(@and [$($acc)*] $op [$($cur)* $t] $($rest)*) };
    (@and [$($acc:tt)*] $op:ident [$($cur:tt)*]) => { $crate::expr!(@join [$($acc)*] $op add [$($cur)*]) };
    (@and $($t:tt)*) => { $crate::expr!(@and [] And [] $($t)*) };

    // add := cast (('+' | '-') cast)*
    // A `-` that starts an operand is a negative literal, not a subtraction.
    (@add [$($acc:tt)*] $op:ident [] - $($rest:tt)*) => { $crate::expr!(@add [$($acc)*] $op [-] $($rest)*) };
    (@add [$($acc:tt)*] $op:ident [$($cur:tt)*] + $($rest:tt)*) =>
        { $crate::expr!(@add [$crate::expr!(@join [$($acc)*] $op cast [$($cur)*])] Add [] $($rest)*) };
    (@add [$($acc:tt)*] $op:ident [$($cur:tt)*] - $($rest:tt)*) =>
        { $crate::expr!(@add [$crate::expr!(@join [$($acc)*] $op cast [$($cur)*])] Sub [] $($rest)*) };
    (@add [$($acc:tt)*] $op:ident [$($cur:tt)*] $t:tt $($rest:tt)*) =>
        { $crate::expr!(@add [$($acc)*] $op [$($cur)* $t] $($rest)*) };
    (@add [$($acc:tt)*] $op:ident [$($cur:tt)*]) => { $crate::expr!(@join [$($acc)*] $op cast [$($cur)*]) };
    (@add $($t:tt)*) => { $crate::expr!(@add [] Add [] $($t)*) };

    // `acc op next(cur)`, or just `next(cur)` for the first operand.
    (@join [] $op:ident $next:ident [$($cur:tt)*]) => { $crate::expr!(@$next $($cur)*) };
    (@join [$($acc:tt)+] $op:ident $next:ident [$($cur:tt)*]) => {
        ::std::sync::Arc::new($crate::Expr::BinOp($crate::BinOp::$op, $($acc)+, $crate::expr!(@$next $($cur)*)))
    };

    // cast  := (value | atom) ('as' ty)*
    // value := literal | arg
    // arg   := arg0 | arg1 | arg2 | arg3 | arg4 | arg5
    // A value takes its Rust type, so an unsuffixed literal is an `i32`.
    (@cast $l:literal $($rest:tt)*) => { $crate::expr!(@as [$crate::ToExpr::to_expr($l)] $($rest)*) };
    (@cast arg0 $($rest:tt)*) => { $crate::expr!(@as [::std::sync::Arc::new($crate::Expr::Var(0))] $($rest)*) };
    (@cast arg1 $($rest:tt)*) => { $crate::expr!(@as [::std::sync::Arc::new($crate::Expr::Var(1))] $($rest)*) };
    (@cast arg2 $($rest:tt)*) => { $crate::expr!(@as [::std::sync::Arc::new($crate::Expr::Var(2))] $($rest)*) };
    (@cast arg3 $($rest:tt)*) => { $crate::expr!(@as [::std::sync::Arc::new($crate::Expr::Var(3))] $($rest)*) };
    (@cast arg4 $($rest:tt)*) => { $crate::expr!(@as [::std::sync::Arc::new($crate::Expr::Var(4))] $($rest)*) };
    (@cast arg5 $($rest:tt)*) => { $crate::expr!(@as [::std::sync::Arc::new($crate::Expr::Var(5))] $($rest)*) };
    (@cast $x:ident $($rest:tt)*) =>
        { compile_error!(concat!("expected an operand, found `", stringify!($x), "`; wrap a Rust value in `{..}`")) };
    (@cast $a:tt $($rest:tt)*) => { $crate::expr!(@as [$crate::expr!(@atom $a)] $($rest)*) };
    (@as [$($e:tt)*] as $ty:ident $($rest:tt)*) =>
        { $crate::expr!(@as [::std::sync::Arc::new($crate::Expr::Cast($($e)*, $crate::expr!(@ty $ty)))] $($rest)*) };
    (@as [$($e:tt)*]) => { $($e)* };
    (@as [$($e:tt)*] $($t:tt)*) =>
        { compile_error!(concat!("unexpected `", stringify!($($t)*), "` in expression")) };

    // atom := '{' rust-expr '}' | '(' expr ')'
    (@atom { $e:expr }) => { $crate::ToExpr::to_expr($e) };
    (@atom ( $($t:tt)* )) => { $crate::expr!(@arc $($t)*) };
    (@atom $($t:tt)*) => { compile_error!(concat!("expected an operand, found `", stringify!($($t)*), "`")) };

    // ty := i8 | i16 | i32 | i64 | u8 | u16 | u32 | u64 | isize | usize | ptr | ident
    (@ty i8) => { $crate::PrimType::I(8) };
    (@ty i16) => { $crate::PrimType::I(16) };
    (@ty i32) => { $crate::PrimType::I(32) };
    (@ty i64) => { $crate::PrimType::I(64) };
    (@ty u8) => { $crate::PrimType::U(8) };
    (@ty u16) => { $crate::PrimType::U(16) };
    (@ty u32) => { $crate::PrimType::U(32) };
    (@ty u64) => { $crate::PrimType::U(64) };
    (@ty isize) => { $crate::PrimType::IWord };
    (@ty usize) => { $crate::PrimType::UWord };
    (@ty ptr) => { $crate::PrimType::Ptr };
    // A Rust variable holding the `PrimType`.
    (@ty $t:ident) => { $t };

    // expr := or
    (@arc $($t:tt)*) => { $crate::expr!(@or [] Or [] $($t)*) };
    ($($t:tt)*) => { ::std::sync::Arc::unwrap_or_clone($crate::expr!(@arc $($t)*)) };
}

/// Parses a Rust-like expression into a `Cond`.
#[macro_export]
macro_rules! cond {
    // or := and ('||' and)*
    (@or [$($acc:tt)*] $op:ident [$($cur:tt)*] || $($rest:tt)*) =>
        { $crate::cond!(@or [$crate::cond!(@join [$($acc)*] $op and [$($cur)*])] Or [] $($rest)*) };
    (@or [$($acc:tt)*] $op:ident [$($cur:tt)*] $t:tt $($rest:tt)*) =>
        { $crate::cond!(@or [$($acc)*] $op [$($cur)* $t] $($rest)*) };
    (@or [$($acc:tt)*] $op:ident [$($cur:tt)*]) => { $crate::cond!(@join [$($acc)*] $op and [$($cur)*]) };

    // and := not ('&&' not)*
    (@and [$($acc:tt)*] $op:ident [$($cur:tt)*] && $($rest:tt)*) =>
        { $crate::cond!(@and [$crate::cond!(@join [$($acc)*] $op not [$($cur)*])] And [] $($rest)*) };
    (@and [$($acc:tt)*] $op:ident [$($cur:tt)*] $t:tt $($rest:tt)*) =>
        { $crate::cond!(@and [$($acc)*] $op [$($cur)* $t] $($rest)*) };
    (@and [$($acc:tt)*] $op:ident [$($cur:tt)*]) => { $crate::cond!(@join [$($acc)*] $op not [$($cur)*]) };
    (@and $($t:tt)*) => { $crate::cond!(@and [] And [] $($t)*) };

    // `acc op next(cur)`, or just `next(cur)` for the first operand.
    (@join [] $op:ident $next:ident [$($cur:tt)*]) => { $crate::cond!(@$next $($cur)*) };
    (@join [$($acc:tt)+] $op:ident $next:ident [$($cur:tt)*]) => {
        ::std::sync::Arc::new($crate::Cond::$op($($acc)+, $crate::cond!(@$next $($cur)*)))
    };

    // not   := unary | cmp
    // unary := '!' unary | '(' cond ')' | true | false | '{' rust-expr '}'
    (@not ! $($t:tt)+) => { ::std::sync::Arc::new($crate::Cond::Not($crate::cond!(@unary $($t)+))) };
    (@not ( $($t:tt)* )) => { $crate::cond!(@arc $($t)*) };
    (@not true) => { ::std::sync::Arc::new($crate::Cond::True) };
    (@not false) => { ::std::sync::Arc::new($crate::Cond::False) };
    (@not { $c:expr }) => { $crate::ToCond::to_cond($c) };
    (@not $c:ident) =>
        { compile_error!(concat!("expected a condition, found `", stringify!($c), "`; wrap a Rust value in `{..}`")) };
    (@not $($t:tt)*) => { $crate::cond!(@cmp [] $($t)*) };
    (@unary ! $($t:tt)+) => { ::std::sync::Arc::new($crate::Cond::Not($crate::cond!(@unary $($t)+))) };
    (@unary ( $($t:tt)* )) => { $crate::cond!(@arc $($t)*) };
    (@unary true) => { ::std::sync::Arc::new($crate::Cond::True) };
    (@unary false) => { ::std::sync::Arc::new($crate::Cond::False) };
    (@unary { $c:expr }) => { $crate::ToCond::to_cond($c) };
    (@unary $c:ident) =>
        { compile_error!(concat!("expected a condition, found `", stringify!($c), "`; wrap a Rust value in `{..}`")) };
    (@unary $($t:tt)*) => { compile_error!(concat!("`!` wants a parenthesized condition, found `", stringify!($($t)*), "`")) };

    // cmp := expr ('==' | '!=' | '<' | '<=' | '>' | '>=') expr
    (@cmp [$($l:tt)*] == $($r:tt)*) => { $crate::cond!(@mk Eq [$($l)*] [$($r)*]) };
    (@cmp [$($l:tt)*] != $($r:tt)*) =>
        { ::std::sync::Arc::new($crate::Cond::Not($crate::cond!(@mk Eq [$($l)*] [$($r)*]))) };
    (@cmp [$($l:tt)*] < $($r:tt)*) => { $crate::cond!(@mk Lt [$($l)*] [$($r)*]) };
    (@cmp [$($l:tt)*] <= $($r:tt)*) => { $crate::cond!(@mk Le [$($l)*] [$($r)*]) };
    (@cmp [$($l:tt)*] > $($r:tt)*) => { $crate::cond!(@mk Lt [$($r)*] [$($l)*]) };
    (@cmp [$($l:tt)*] >= $($r:tt)*) => { $crate::cond!(@mk Le [$($r)*] [$($l)*]) };
    (@cmp [$($l:tt)*] $t:tt $($rest:tt)*) => { $crate::cond!(@cmp [$($l)* $t] $($rest)*) };
    (@cmp [$($l:tt)*]) => { compile_error!(concat!("expected a comparison, found `", stringify!($($l)*), "`")) };
    (@mk $op:ident [$($l:tt)*] [$($r:tt)*]) => {
        ::std::sync::Arc::new($crate::Cond::Cmp($crate::CmpOp::$op, $crate::expr!(@arc $($l)*), $crate::expr!(@arc $($r)*)))
    };

    // cond := or
    (@arc $($t:tt)*) => { $crate::cond!(@or [] Or [] $($t)*) };
    ($($t:tt)*) => { ::std::sync::Arc::unwrap_or_clone($crate::cond!(@arc $($t)*)) };
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;
    use crate::{Cond, Expr, PrimType};

    #[test]
    fn literal_types() {
        assert_eq!(format!("{:?}", expr!(1)), "Lit(1, I(32))");
        assert_eq!(format!("{:?}", expr!(0x7fff_ffff)), "Lit(2147483647, I(32))");
        assert_eq!(format!("{:?}", expr!(-128i8)), "Lit(-128, I(8))");
        assert_eq!(format!("{:?}", expr!(1i16)), "Lit(1, I(16))");
        assert_eq!(format!("{:?}", expr!(1i32)), "Lit(1, I(32))");
        assert_eq!(format!("{:?}", expr!(1i64)), "Lit(1, I(64))");
        assert_eq!(format!("{:?}", expr!(0xffu8)), "Lit(255, U(8))");
        assert_eq!(format!("{:?}", expr!(0xffffu16)), "Lit(65535, U(16))");
        assert_eq!(format!("{:?}", expr!(0xffff_ffffu32)), "Lit(4294967295, U(32))");
        assert_eq!(format!("{:?}", expr!(1isize)), "Lit(1, IWord)");
        assert_eq!(format!("{:?}", expr!(1usize)), "Lit(1, UWord)");
    }

    #[test]
    fn literal_values() {
        assert_eq!(format!("{:?}", expr!(-1)), "Lit(-1, I(32))");
        assert_eq!(format!("{:?}", expr!(-0x8000_0000)), "Lit(-2147483648, I(32))");
        assert_eq!(format!("{:?}", expr!(-0x8000_0000_0000_0000i64)), "Lit(-9223372036854775808, I(64))");
        assert_eq!(format!("{:?}", expr!(0xffff_ffff_ffff_ffffu64)), "Lit(-1, U(64))");
        assert_eq!(format!("{:?}", expr!(0o644)), "Lit(420, I(32))");
    }

    #[test]
    fn variables() {
        let small: u16 = 9;
        let max = u64::MAX;
        assert_eq!(format!("{:?}", expr!({small})), "Lit(9, U(16))");
        assert_eq!(format!("{:?}", expr!({max})), "Lit(-1, U(64))");
        let owned = expr!(arg0 + 1);
        let borrowed: &Expr = &owned;
        let shared: Arc<Expr> = Arc::new(expr!(arg1));
        assert_eq!(format!("{:?}", expr!({borrowed} & 3)), "BinOp(And, BinOp(Add, Var(0), Lit(1, I(32))), Lit(3, I(32)))");
        assert_eq!(format!("{:?}", expr!({shared} as u32)), "Cast(Var(1), U(32))");
        assert_eq!(format!("{:?}", expr!({owned})), "BinOp(Add, Var(0), Lit(1, I(32)))");
    }

    #[test]
    fn casts() {
        let ty = PrimType::I(16);
        assert_eq!(format!("{:?}", expr!(1 as u8)), "Cast(Lit(1, I(32)), U(8))");
        assert_eq!(format!("{:?}", expr!(-1 as ptr)), "Cast(Lit(-1, I(32)), Ptr)");
        assert_eq!(format!("{:?}", expr!(1u64 as usize)), "Cast(Lit(1, U(64)), UWord)");
        assert_eq!(format!("{:?}", expr!(1 as ty)), "Cast(Lit(1, I(32)), I(16))");
        assert_eq!(format!("{:?}", expr!(arg0 as u32 as isize)), "Cast(Cast(Var(0), U(32)), IWord)");
    }

    #[test]
    fn operators() {
        assert_eq!(format!("{:?}", expr!(arg0 - 1 - 2)), "BinOp(Sub, BinOp(Sub, Var(0), Lit(1, I(32))), Lit(2, I(32)))");
        assert_eq!(format!("{:?}", expr!(arg0 - -1)), "BinOp(Sub, Var(0), Lit(-1, I(32)))");
        assert_eq!(format!("{:?}", expr!(-1 + arg0)), "BinOp(Add, Lit(-1, I(32)), Var(0))");
        assert_eq!(format!("{:?}", expr!(arg0 | 1 ^ 2 & 3 + 4)),
            "BinOp(Or, Var(0), BinOp(Xor, Lit(1, I(32)), BinOp(And, Lit(2, I(32)), BinOp(Add, Lit(3, I(32)), Lit(4, I(32))))))");
        assert_eq!(format!("{:?}", expr!((arg0 | 1) & 2)), "BinOp(And, BinOp(Or, Var(0), Lit(1, I(32))), Lit(2, I(32)))");
        assert_eq!(format!("{:?}", expr!(arg0 + 1 as u8)), "BinOp(Add, Var(0), Cast(Lit(1, I(32)), U(8)))");
        assert_eq!(format!("{:?}", expr!({Expr::Var(1 + 1)})), "Var(2)");
    }

    #[test]
    fn comparisons() {
        assert_eq!(format!("{:?}", cond!(arg0 == 1)), "Cmp(Eq, Var(0), Lit(1, I(32)))");
        assert_eq!(format!("{:?}", cond!(arg0 != 1)), "Not(Cmp(Eq, Var(0), Lit(1, I(32))))");
        assert_eq!(format!("{:?}", cond!(arg0 < 1)), "Cmp(Lt, Var(0), Lit(1, I(32)))");
        assert_eq!(format!("{:?}", cond!(arg0 <= 1)), "Cmp(Le, Var(0), Lit(1, I(32)))");
        assert_eq!(format!("{:?}", cond!(arg0 > 1)), "Cmp(Lt, Lit(1, I(32)), Var(0))");
        assert_eq!(format!("{:?}", cond!(arg0 >= 1)), "Cmp(Le, Lit(1, I(32)), Var(0))");
        assert_eq!(format!("{:?}", cond!(arg0 < -1)), "Cmp(Lt, Var(0), Lit(-1, I(32)))");
        assert_eq!(format!("{:?}", cond!(arg0 & 1u8 == 0u8)), "Cmp(Eq, BinOp(And, Var(0), Lit(1, U(8))), Lit(0, U(8)))");
    }

    #[test]
    fn connectives() {
        assert_eq!(format!("{:?}", cond!(true || false && true)), "Or(True, And(False, True))");
        assert_eq!(format!("{:?}", cond!((true || false) && true)), "And(Or(True, False), True)");
        assert_eq!(format!("{:?}", cond!(!true)), "Not(True)");
        assert_eq!(format!("{:?}", cond!(!!false)), "Not(Not(False))");
        assert_eq!(format!("{:?}", cond!(!(arg0 == 1) || arg1 < 2)),
            "Or(Not(Cmp(Eq, Var(0), Lit(1, I(32)))), Cmp(Lt, Var(1), Lit(2, I(32))))");
    }

    #[test]
    fn paths() {
        assert_eq!(format!("{:?}", expr!({u64::MAX})), "Lit(-1, U(64))");
        assert_eq!(format!("{:?}", expr!({i32::MIN})), "Lit(-2147483648, I(32))");
        assert_eq!(format!("{:?}", expr!({u8::MAX} as u16)), "Cast(Lit(255, U(8)), U(16))");
        assert_eq!(format!("{:?}", expr!(arg0 & {u16::MAX})), "BinOp(And, Var(0), Lit(65535, U(16)))");
        assert_eq!(format!("{:?}", cond!(arg0 < {i8::MIN})), "Cmp(Lt, Var(0), Lit(-128, I(8)))");
    }

    #[test]
    fn cond_variables() {
        let owned = cond!(arg0 == 1);
        let borrowed: &Cond = &owned;
        let shared: Arc<Cond> = Arc::new(cond!(false));
        assert_eq!(format!("{:?}", cond!({borrowed} && arg1 < 2)),
            "And(Cmp(Eq, Var(0), Lit(1, I(32))), Cmp(Lt, Var(1), Lit(2, I(32))))");
        assert_eq!(format!("{:?}", cond!(!{borrowed} || ({borrowed}))),
            "Or(Not(Cmp(Eq, Var(0), Lit(1, I(32)))), Cmp(Eq, Var(0), Lit(1, I(32))))");
        assert_eq!(format!("{:?}", cond!({shared})), "False");
        assert_eq!(format!("{:?}", cond!({owned})), "Cmp(Eq, Var(0), Lit(1, I(32)))");
    }

    #[test]
    fn embedded() {
        let v = vec![7u8, 8u8];
        assert_eq!(format!("{:?}", expr!({1 + 1})), "Lit(2, I(32))");
        assert_eq!(format!("{:?}", expr!({v[1]} as u16)), "Cast(Lit(8, U(8)), U(16))");
        assert_eq!(format!("{:?}", expr!({v.len()})), "Lit(2, UWord)");
        assert_eq!(format!("{:?}", expr!({Expr::Var(6)} + arg5)), "BinOp(Add, Var(6), Var(5))");
        assert_eq!(format!("{:?}", cond!(arg0 == {i16::MIN + 1})), "Cmp(Eq, Var(0), Lit(-32767, I(16)))");
    }

    #[test]
    fn args() {
        assert_eq!(format!("{:?}", expr!(arg0 + arg1 + arg2 + arg3 + arg4 + arg5)),
            "BinOp(Add, BinOp(Add, BinOp(Add, BinOp(Add, BinOp(Add, Var(0), Var(1)), Var(2)), Var(3)), Var(4)), Var(5))");
        assert_eq!(format!("{:?}", expr!(arg3 as u32)), "Cast(Var(3), U(32))");
    }
}
