//! Helper macros to construct `Expr` and `Cond`.

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
        $crate::Expr::BinOp($crate::BinOp::$op,
            ::std::sync::Arc::new($($acc)+), ::std::sync::Arc::new($crate::expr!(@$next $($cur)*)))
    };

    // cast  := (value | atom) ('as' ty)*
    // value := '-' literal | literal | ident
    (@cast - $l:literal $($rest:tt)*) => { $crate::expr!(@lit [-($l as i64)] $($rest)*) };
    (@cast $l:literal $($rest:tt)*) => { $crate::expr!(@lit [$l as u64 as i64] $($rest)*) };
    // A Rust variable holding the value, bitcast like a literal.
    (@cast $x:ident $($rest:tt)*) => { $crate::expr!(@lit [$x as u64 as i64] $($rest)*) };
    (@cast $a:tt $($rest:tt)*) => { $crate::expr!(@as [$crate::expr!(@atom $a)] $($rest)*) };
    // A value cast straight to a type is a literal of that type, and otherwise an `i64`.
    (@lit [$($v:tt)*] as $ty:ident $($rest:tt)*) =>
        { $crate::expr!(@as [$crate::Expr::Lit($($v)*, $crate::expr!(@ty $ty))] $($rest)*) };
    (@lit [$($v:tt)*] $($rest:tt)*) =>
        { $crate::expr!(@as [$crate::Expr::Lit($($v)*, $crate::PrimType::I(64))] $($rest)*) };
    (@as [$($e:tt)*] as $ty:ident $($rest:tt)*) =>
        { $crate::expr!(@as [$crate::Expr::Cast(::std::sync::Arc::new($($e)*), $crate::expr!(@ty $ty))] $($rest)*) };
    (@as [$($e:tt)*]) => { $($e)* };
    (@as [$($e:tt)*] $($t:tt)*) =>
        { compile_error!(concat!("unexpected `", stringify!($($t)*), "` in expression")) };

    // atom := '{' index '}' | '(' expr ')'
    (@atom { $i:expr }) => { $crate::Expr::Var($i) };
    (@atom ( $($t:tt)* )) => { $crate::expr!($($t)*) };
    (@atom $($t:tt)*) => { compile_error!(concat!("expected an operand, found `", stringify!($($t)*), "`")) };

    // ty := i8 | i16 | i32 | i64 | u8 | u16 | u32 | u64 | iword | uword | ptr | ident
    (@ty i8) => { $crate::PrimType::I(8) };
    (@ty i16) => { $crate::PrimType::I(16) };
    (@ty i32) => { $crate::PrimType::I(32) };
    (@ty i64) => { $crate::PrimType::I(64) };
    (@ty u8) => { $crate::PrimType::U(8) };
    (@ty u16) => { $crate::PrimType::U(16) };
    (@ty u32) => { $crate::PrimType::U(32) };
    (@ty u64) => { $crate::PrimType::U(64) };
    (@ty iword) => { $crate::PrimType::IWord };
    (@ty uword) => { $crate::PrimType::UWord };
    (@ty ptr) => { $crate::PrimType::Ptr };
    // A Rust variable holding the `PrimType`.
    (@ty $t:ident) => { $t };

    // expr := or
    ($($t:tt)*) => { $crate::expr!(@or [] Or [] $($t)*) };
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
        $crate::Cond::$op(::std::sync::Arc::new($($acc)+), ::std::sync::Arc::new($crate::cond!(@$next $($cur)*)))
    };

    // not   := unary | cmp
    // unary := '!' unary | '(' cond ')' | true | false
    (@not ! $($t:tt)+) => { $crate::Cond::Not(::std::sync::Arc::new($crate::cond!(@unary $($t)+))) };
    (@not ( $($t:tt)* )) => { $crate::cond!($($t)*) };
    (@not true) => { $crate::Cond::True };
    (@not false) => { $crate::Cond::False };
    (@not $($t:tt)*) => { $crate::cond!(@cmp [] $($t)*) };
    (@unary ! $($t:tt)+) => { $crate::Cond::Not(::std::sync::Arc::new($crate::cond!(@unary $($t)+))) };
    (@unary ( $($t:tt)* )) => { $crate::cond!($($t)*) };
    (@unary true) => { $crate::Cond::True };
    (@unary false) => { $crate::Cond::False };
    (@unary $($t:tt)*) => { compile_error!(concat!("`!` wants a parenthesized condition, found `", stringify!($($t)*), "`")) };

    // cmp := expr ('==' | '!=' | '<' | '<=' | '>' | '>=') expr
    (@cmp [$($l:tt)*] == $($r:tt)*) => { $crate::cond!(@mk Eq [$($l)*] [$($r)*]) };
    (@cmp [$($l:tt)*] != $($r:tt)*) =>
        { $crate::Cond::Not(::std::sync::Arc::new($crate::cond!(@mk Eq [$($l)*] [$($r)*]))) };
    (@cmp [$($l:tt)*] < $($r:tt)*) => { $crate::cond!(@mk Lt [$($l)*] [$($r)*]) };
    // Rust lexes `<-` as one token, so `a <-1` has to be split back.
    (@cmp [$($l:tt)*] <- $($r:tt)*) => { $crate::cond!(@mk Lt [$($l)*] [- $($r)*]) };
    (@cmp [$($l:tt)*] <= $($r:tt)*) => { $crate::cond!(@mk Le [$($l)*] [$($r)*]) };
    (@cmp [$($l:tt)*] > $($r:tt)*) => { $crate::cond!(@mk Lt [$($r)*] [$($l)*]) };
    (@cmp [$($l:tt)*] >= $($r:tt)*) => { $crate::cond!(@mk Le [$($r)*] [$($l)*]) };
    (@cmp [$($l:tt)*] $t:tt $($rest:tt)*) => { $crate::cond!(@cmp [$($l)* $t] $($rest)*) };
    (@cmp [$($l:tt)*]) => { compile_error!(concat!("expected a comparison, found `", stringify!($($l)*), "`")) };
    (@mk $op:ident [$($l:tt)*] [$($r:tt)*]) => {
        $crate::Cond::Cmp($crate::CmpOp::$op,
            ::std::sync::Arc::new($crate::expr!($($l)*)), ::std::sync::Arc::new($crate::expr!($($r)*)))
    };

    // cond := or
    ($($t:tt)*) => { $crate::cond!(@or [] Or [] $($t)*) };
}
