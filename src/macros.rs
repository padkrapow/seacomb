//! Helper macros to construct `Expr`, `Cond`, `Rule`, and `Policy`.

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
///
/// ```
/// use seacomb::*;
///
/// // `@n` is the syscall argument at position `n`.
/// expr!(@0 + 1u32);
/// expr!(@1 & 0o777 | 0o644);
/// expr!(-1i64 - @2);
///
/// // `as` for bitcasting, and `{..}` embeds a Rust `ToExpr` value.
/// let mask: u32 = 0xff;
/// expr!((@1 as u32) & {mask});
/// expr!(@2 as ptr);
/// expr!({u16::MAX} as usize + @3);
/// ```
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
    // value := literal | arg | ident
    // arg   := '@' integer
    // A value takes its Rust type, so an unsuffixed literal is an `i32`.
    (@cast $l:literal $($rest:tt)*) => { $crate::expr!(@as [$crate::ToExpr::to_expr($l)] $($rest)*) };
    (@cast @ $n:literal $($rest:tt)*) => { $crate::expr!(@as [::std::sync::Arc::new($crate::Expr::Var($n))] $($rest)*) };
    (@cast @ $($rest:tt)*) => { compile_error!(concat!("expected an argument index after `@`, found `", stringify!($($rest)*), "`")) };
    (@cast $x:ident $($rest:tt)*) =>
        { $crate::expr!(@as [$crate::ToExpr::to_expr(::std::clone::Clone::clone(&$x))] $($rest)*) };
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
///
/// ```
/// use seacomb::*;
///
/// // Comparisons.
/// cond!(@0 == 2);
/// cond!(@1 & 0x80000u32 != 0u32);
/// cond!(@2 >= 4096usize);
///
/// // Logical connectives, and `{..}` embeds a Rust `ToCond` value.
/// let stdin = cond!(@0 == 0);
/// cond!(!{&stdin} && (@2 < 4096usize || true));
/// cond!({stdin} || false);
/// ```
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

/// Parses a rule into a `Rule`.
///
/// ```
/// use seacomb::*;
///
/// // Unconditional rules.
/// rule!(kill execve(_, _, _));
/// rule!(trap(7) getpid());
///
/// // Conditional rules.
/// rule!(errno(1) write(fd, _, count) if fd == 2u32 && count > 0usize);
/// rule!(log openat(_, _, flags) if flags & 0o100 != 0);
///
/// // `[..]` limits a rule to some archs, and `exact` skips the x86 `socketcall` form.
/// rule!([x86] allow exact bind(fd, addr, len));
/// rule!([x86_64, aarch64] notify ptrace());
/// ```
#[macro_export]
macro_rules! rule {
    // rule    := ['[' arch (',' arch)* ']'] action ['exact'] syscall '(' names ')' ['if' cond]
    // action  := kill | kill_thread | trap '(' rust-expr ')' | errno '(' rust-expr ')'
    //          | trace '(' rust-expr ')' | log | allow | notify | '{' rust-expr '}'
    // syscall := ident | '{' rust-expr '}'
    (@act $archs:tt $a:ident ( $($e:tt)* ) $($rest:tt)*) => { $crate::rule!(@exact $archs [$a ($($e)*)] $($rest)*) };
    (@act $archs:tt $a:ident $($rest:tt)*) => { $crate::rule!(@exact $archs [$a] $($rest)*) };
    (@act $archs:tt { $($a:tt)* } $($rest:tt)*) => { $crate::rule!(@exact $archs [{ $($a)* }] $($rest)*) };
    (@act $archs:tt $($t:tt)*) => { compile_error!(concat!("expected an action, found `", stringify!($($t)*), "`")) };

    // `exact` sets `no_mux`.
    (@exact $archs:tt $act:tt exact $($rest:tt)*) => { $crate::rule!(@syscall $archs $act true $($rest)*) };
    (@exact $archs:tt $act:tt $($rest:tt)*) => { $crate::rule!(@syscall $archs $act false $($rest)*) };

    (@syscall $archs:tt $act:tt $exact:tt { $s:expr } ( $($names:tt)* ) $($rest:tt)*) =>
        { $crate::rule!(@mk $archs $act $exact [$s] [$($names)*] $($rest)*) };
    (@syscall $archs:tt $act:tt $exact:tt $name:ident ( $($names:tt)* ) $($rest:tt)*) => {
        $crate::rule!(@mk $archs $act $exact [const {
            match $crate::Syscall::lookup(stringify!($name)) {
                ::core::option::Option::Some(s) => s,
                ::core::option::Option::None => ::core::panic!(concat!("unknown syscall `", stringify!($name), "`")),
            }
        }] [$($names)*] $($rest)*)
    };
    (@syscall $archs:tt $act:tt $exact:tt $($t:tt)*) =>
        { compile_error!(concat!("expected a syscall, found `", stringify!($($t)*), "`")) };

    // Binds each name to the argument at its position, so `if` can refer to it.
    (@mk [$($arch:tt),*] [$($act:tt)*] $exact:tt [$($sys:tt)*] [$($arg:tt),* $(,)?] $(if $($c:tt)+)?) => {{
        $( $crate::rule!(@name $arg); )*
        #[allow(unused_variables)]
        let [$($arg,)* ..] = [
            $crate::Expr::Var(0), $crate::Expr::Var(1), $crate::Expr::Var(2),
            $crate::Expr::Var(3), $crate::Expr::Var(4), $crate::Expr::Var(5),
        ];
        $crate::Rule {
            action: $crate::rule!(@action $($act)*),
            syscall: $($sys)*,
            cond: $crate::rule!(@cond $($($c)+)?),
            archs: {
                // Keeps the first of each arch, since `[native, x86]` repeats one on an x86 host.
                #[allow(unused_mut)]
                let mut archs = ::std::vec::Vec::new();
                $(
                    let arch = $crate::rule!(@arch $arch);
                    if !archs.contains(&arch) {
                        archs.push(arch);
                    }
                )*
                archs
            },
            no_mux: $exact,
        }
    }};
    (@mk $archs:tt $act:tt $exact:tt $sys:tt $names:tt if) => { compile_error!("`if` wants a condition") };
    (@mk $archs:tt $act:tt $exact:tt $sys:tt $names:tt $($t:tt)*) =>
        { compile_error!(concat!("expected `if`, found `", stringify!($($t)*), "`")) };

    // A rule without `if` always applies.
    (@cond) => { ::std::sync::Arc::new($crate::Cond::True) };
    (@cond $($c:tt)+) => { $crate::cond!(@arc $($c)+) };

    // name := ident | '_'
    (@name $x:ident) => {};
    (@name _) => {};
    (@name $x:tt) => { compile_error!(concat!("expected an argument name, found `", stringify!($x), "`")) };

    // An action on its own, which `policy!` also takes for its header.
    (@action kill) => { $crate::Action::KillProcess };
    (@action kill_thread) => { $crate::Action::KillThread };
    (@action trap ($e:expr)) => { $crate::Action::Trap($e) };
    (@action errno ($e:expr)) => { $crate::Action::Errno($e) };
    (@action trace ($e:expr)) => { $crate::Action::Trace($e) };
    (@action log) => { $crate::Action::Log };
    (@action allow) => { $crate::Action::Allow };
    (@action notify) => { $crate::Action::Notify };
    (@action { $a:expr }) => { $a };
    (@action $($t:tt)*) => { compile_error!(concat!("expected an action, found `", stringify!($($t)*), "`")) };

    // arch := x86 | x86_64 | arm | aarch64 | native | '{' rust-expr '}'
    (@arch x86) => { $crate::Arch::X86 };
    (@arch x86_64) => { $crate::Arch::X86_64 };
    (@arch arm) => { $crate::Arch::Arm };
    (@arch aarch64) => { $crate::Arch::Aarch64 };
    (@arch native) => { $crate::Arch::native()? };
    (@arch { $a:expr }) => { $a };
    (@arch $a:tt) => { compile_error!(concat!("unknown arch `", stringify!($a), "`")) };

    ([] $($t:tt)*) => { compile_error!("`[..]` wants at least one arch") };
    ([$($arch:tt),+ $(,)?] $($rest:tt)*) => { $crate::rule!(@act [$($arch),+] $($rest)*) };
    ($($rest:tt)*) => { $crate::rule!(@act [] $($rest)*) };
}

/// Parses a policy into a `Result<Policy, Error>`.
///
/// ```
/// use seacomb::*;
///
/// // Allow by default on x86-64 and AArch64, and kill the process on any other arch.
/// policy! {
///     default allow on x86_64, aarch64 else kill;
///     errno(1) write(fd, _, _) if fd == 2u32;
///     kill execve(_, _, _);
/// }.unwrap();
///
/// // `native` is the current host at build time, and `{..}` embeds a Rust `Rule`.
/// let no_ptrace = rule!(errno(1) ptrace(_, _, _, _));
/// policy!(default allow on native; {no_ptrace}).unwrap();
/// policy!(default errno(38) on native; allow read(); allow write(); allow exit_group()).unwrap();
///
/// // Type checking: `buf` has type `ptr`, so it cannot be compared to `usize`.
/// policy!(default allow on x86_64; allow write(_, buf, _) if buf < 4096usize).unwrap_err();
/// ```
#[macro_export]
macro_rules! policy {
    // policy := header ';' (rule ';')*, where the last ';' may be left off
    // header := 'default' action 'on' arch (',' arch)* ['else' action], where a repeated arch counts once
    // arch   := rule's arch
    // rule   := rule's rule | '{' rust-expr '}'

    // Takes up to four tokens a step to find each `;`, which keeps long policies under the default `recursion_limit`.
    (@split [$($done:tt)*] [$($cur:tt)*] ; $($rest:tt)*) =>
        { $crate::policy!(@split [$($done)* [$($cur)*]] [] $($rest)*) };
    (@split [$($done:tt)*] [$($cur:tt)*] $a:tt ; $($rest:tt)*) =>
        { $crate::policy!(@split [$($done)* [$($cur)* $a]] [] $($rest)*) };
    (@split [$($done:tt)*] [$($cur:tt)*] $a:tt $b:tt ; $($rest:tt)*) =>
        { $crate::policy!(@split [$($done)* [$($cur)* $a $b]] [] $($rest)*) };
    (@split [$($done:tt)*] [$($cur:tt)*] $a:tt $b:tt $c:tt ; $($rest:tt)*) =>
        { $crate::policy!(@split [$($done)* [$($cur)* $a $b $c]] [] $($rest)*) };
    (@split $done:tt [$($cur:tt)*] $a:tt $b:tt $c:tt $d:tt $($rest:tt)*) =>
        { $crate::policy!(@split $done [$($cur)* $a $b $c $d] $($rest)*) };
    (@split [$($done:tt)*] []) => { $crate::policy!(@mk $($done)*) };
    (@split [$($done:tt)*] [$($cur:tt)*] $($rest:tt)*) => { $crate::policy!(@mk $($done)* [$($cur)* $($rest)*]) };

    // Runs in a closure, so a failed step returns its error.
    (@mk [$($header:tt)*] $([$($rule:tt)*])*) => {
        (|| -> ::core::result::Result<$crate::Policy, $crate::Error> {
            #[allow(unused_mut)]
            let mut policy = $crate::policy!(@header $($header)*);
            $( policy.add($crate::policy!(@rule $($rule)*))?; )*
            ::core::result::Result::Ok(policy)
        })()
    };
    (@mk) => { compile_error!("`policy!` wants a `default` header") };

    (@header default $a:tt on $($arch:tt),+ $(else $($bad:tt)+)?) =>
        { $crate::policy!(@new [$a] [$($arch),+] $([$($bad)+])?) };
    (@header default $a:tt $b:tt on $($arch:tt),+ $(else $($bad:tt)+)?) =>
        { $crate::policy!(@new [$a $b] [$($arch),+] $([$($bad)+])?) };
    (@header $($t:tt)*) =>
        { compile_error!(concat!("expected `default <action> on <archs>`, found `", stringify!($($t)*), "`")) };

    // Without `else`, the bad-arch action stays the one `Policy::new` picks.
    (@new [$($act:tt)+] [$($arch:tt),+] $([$($bad:tt)+])?) => {{
        let mut policy = $crate::Policy::new($crate::rule!(@action $($act)+))?;
        $( policy.add_arch($crate::rule!(@arch $arch))?; )+
        $( policy.on_bad_arch($crate::rule!(@action $($bad)+))?; )?
        policy
    }};

    (@rule { $r:expr }) => { $r };
    (@rule $($t:tt)*) => { $crate::rule!($($t)*) };

    ($($t:tt)*) => { $crate::policy!(@split [] [] $($t)*) };
}

/// Cases that `rule!` should reject.
///
/// ```compile_fail
/// seacomb::rule!(allow raed(fd));
/// ```
/// ```compile_fail
/// seacomb::rule!(deny read(fd));
/// ```
/// ```compile_fail
/// seacomb::rule!(kill process read(fd));
/// ```
/// ```compile_fail
/// seacomb::rule!(trap read(fd));
/// ```
/// ```compile_fail
/// seacomb::rule!(allow on read(fd));
/// ```
/// ```compile_fail
/// seacomb::rule!(allow exact(fd));
/// ```
/// ```compile_fail
/// seacomb::rule!(allow read);
/// ```
/// ```compile_fail
/// seacomb::rule!(allow read(1));
/// ```
/// ```compile_fail
/// seacomb::rule!(allow read(a, b, c, d, e, f, g));
/// ```
/// ```compile_fail
/// seacomb::rule!([mips] allow read(fd));
/// ```
/// ```compile_fail
/// seacomb::rule!([] allow read(fd));
/// ```
/// ```compile_fail
/// seacomb::rule!([x86] [arm] allow read(fd));
/// ```
/// ```compile_fail
/// seacomb::rule!(allow read(fd) [x86]);
/// ```
/// ```compile_fail
/// seacomb::rule!(allow read(fd) if);
/// ```
/// ```compile_fail
/// seacomb::rule!(allow read(fd) when fd == 0);
/// ```
/// ```compile_fail
/// seacomb::rule!(allow read(fd) if bogus == 0);
/// ```
/// ```compile_fail
/// seacomb::rule!(allow read(fd) if @x == 0);
/// ```
/// ```compile_fail
/// seacomb::rule!(errno(70000) read(fd));
/// ```
#[cfg(doctest)]
struct RuleMacroTests;

/// Cases that `policy!` should reject.
///
/// ```compile_fail
/// seacomb::policy!();
/// ```
/// ```compile_fail
/// seacomb::policy!(allow read(fd));
/// ```
/// ```compile_fail
/// seacomb::policy!(allow read(fd); default allow on x86);
/// ```
/// ```compile_fail
/// seacomb::policy!(default allow);
/// ```
/// ```compile_fail
/// seacomb::policy!(default allow on);
/// ```
/// ```compile_fail
/// seacomb::policy!(default allow on x86 arm);
/// ```
/// ```compile_fail
/// seacomb::policy!(default allow on x86, arm,);
/// ```
/// ```compile_fail
/// seacomb::policy!(default allow on mips);
/// ```
/// ```compile_fail
/// seacomb::policy!(default deny on x86);
/// ```
/// ```compile_fail
/// seacomb::policy!(default allow on x86 else);
/// ```
/// ```compile_fail
/// seacomb::policy!(default allow on x86 else kill process);
/// ```
/// ```compile_fail
/// seacomb::policy!(default allow on x86; allow read(fd) allow write(fd));
/// ```
/// ```compile_fail
/// seacomb::policy!(default allow on x86;; allow read(fd));
/// ```
#[cfg(doctest)]
struct PolicyMacroTests;

#[cfg(test)]
mod tests {
    use std::sync::Arc;
    use crate::{Action, Arch, CheckError, Cond, Error, Expr, PrimType, Syscall};

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
        let owned = expr!(@0 + 1);
        let borrowed: &Expr = &owned;
        let shared: Arc<Expr> = Arc::new(expr!(@1));
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
        assert_eq!(format!("{:?}", expr!(@0 as u32 as isize)), "Cast(Cast(Var(0), U(32)), IWord)");
    }

    #[test]
    fn operators() {
        assert_eq!(format!("{:?}", expr!(@0 - 1 - 2)), "BinOp(Sub, BinOp(Sub, Var(0), Lit(1, I(32))), Lit(2, I(32)))");
        assert_eq!(format!("{:?}", expr!(@0 - -1)), "BinOp(Sub, Var(0), Lit(-1, I(32)))");
        assert_eq!(format!("{:?}", expr!(-1 + @0)), "BinOp(Add, Lit(-1, I(32)), Var(0))");
        assert_eq!(format!("{:?}", expr!(@0 | 1 ^ 2 & 3 + 4)),
            "BinOp(Or, Var(0), BinOp(Xor, Lit(1, I(32)), BinOp(And, Lit(2, I(32)), BinOp(Add, Lit(3, I(32)), Lit(4, I(32))))))");
        assert_eq!(format!("{:?}", expr!((@0 | 1) & 2)), "BinOp(And, BinOp(Or, Var(0), Lit(1, I(32))), Lit(2, I(32)))");
        assert_eq!(format!("{:?}", expr!(@0 + 1 as u8)), "BinOp(Add, Var(0), Cast(Lit(1, I(32)), U(8)))");
        assert_eq!(format!("{:?}", expr!({Expr::Var(1 + 1)})), "Var(2)");
    }

    #[test]
    fn comparisons() {
        assert_eq!(format!("{:?}", cond!(@0 == 1)), "Cmp(Eq, Var(0), Lit(1, I(32)))");
        assert_eq!(format!("{:?}", cond!(@0 != 1)), "Not(Cmp(Eq, Var(0), Lit(1, I(32))))");
        assert_eq!(format!("{:?}", cond!(@0 < 1)), "Cmp(Lt, Var(0), Lit(1, I(32)))");
        assert_eq!(format!("{:?}", cond!(@0 <= 1)), "Cmp(Le, Var(0), Lit(1, I(32)))");
        assert_eq!(format!("{:?}", cond!(@0 > 1)), "Cmp(Lt, Lit(1, I(32)), Var(0))");
        assert_eq!(format!("{:?}", cond!(@0 >= 1)), "Cmp(Le, Lit(1, I(32)), Var(0))");
        assert_eq!(format!("{:?}", cond!(@0 < -1)), "Cmp(Lt, Var(0), Lit(-1, I(32)))");
        assert_eq!(format!("{:?}", cond!(@0 & 1u8 == 0u8)), "Cmp(Eq, BinOp(And, Var(0), Lit(1, U(8))), Lit(0, U(8)))");
    }

    #[test]
    fn connectives() {
        assert_eq!(format!("{:?}", cond!(true || false && true)), "Or(True, And(False, True))");
        assert_eq!(format!("{:?}", cond!((true || false) && true)), "And(Or(True, False), True)");
        assert_eq!(format!("{:?}", cond!(!true)), "Not(True)");
        assert_eq!(format!("{:?}", cond!(!!false)), "Not(Not(False))");
        assert_eq!(format!("{:?}", cond!(!(@0 == 1) || @1 < 2)),
            "Or(Not(Cmp(Eq, Var(0), Lit(1, I(32)))), Cmp(Lt, Var(1), Lit(2, I(32))))");
    }

    #[test]
    fn paths() {
        assert_eq!(format!("{:?}", expr!({u64::MAX})), "Lit(-1, U(64))");
        assert_eq!(format!("{:?}", expr!({i32::MIN})), "Lit(-2147483648, I(32))");
        assert_eq!(format!("{:?}", expr!({u8::MAX} as u16)), "Cast(Lit(255, U(8)), U(16))");
        assert_eq!(format!("{:?}", expr!(@0 & {u16::MAX})), "BinOp(And, Var(0), Lit(65535, U(16)))");
        assert_eq!(format!("{:?}", cond!(@0 < {i8::MIN})), "Cmp(Lt, Var(0), Lit(-128, I(8)))");
    }

    #[test]
    fn cond_variables() {
        let owned = cond!(@0 == 1);
        let borrowed: &Cond = &owned;
        let shared: Arc<Cond> = Arc::new(cond!(false));
        assert_eq!(format!("{:?}", cond!({borrowed} && @1 < 2)),
            "And(Cmp(Eq, Var(0), Lit(1, I(32))), Cmp(Lt, Var(1), Lit(2, I(32))))");
        assert_eq!(format!("{:?}", cond!(!{borrowed} || ({borrowed}))),
            "Or(Not(Cmp(Eq, Var(0), Lit(1, I(32)))), Cmp(Eq, Var(0), Lit(1, I(32))))");
        assert_eq!(format!("{:?}", cond!({shared})), "False");
        assert_eq!(format!("{:?}", cond!({owned})), "Cmp(Eq, Var(0), Lit(1, I(32)))");
    }

    #[test]
    fn embedded() {
        let v = [7u8, 8u8];
        assert_eq!(format!("{:?}", expr!({1 + 1})), "Lit(2, I(32))");
        assert_eq!(format!("{:?}", expr!({v[1]} as u16)), "Cast(Lit(8, U(8)), U(16))");
        assert_eq!(format!("{:?}", expr!({v.len()})), "Lit(2, UWord)");
        assert_eq!(format!("{:?}", expr!({Expr::Var(6)} + @5)), "BinOp(Add, Var(6), Var(5))");
        assert_eq!(format!("{:?}", cond!(@0 == {i16::MIN + 1})), "Cmp(Eq, Var(0), Lit(-32767, I(16)))");
    }

    #[test]
    fn args() {
        assert_eq!(format!("{:?}", expr!(@0 + @1 + @2 + @3 + @4 + @5)),
            "BinOp(Add, BinOp(Add, BinOp(Add, BinOp(Add, BinOp(Add, Var(0), Var(1)), Var(2)), Var(3)), Var(4)), Var(5))");
        assert_eq!(format!("{:?}", expr!(@3 as u32)), "Cast(Var(3), U(32))");
    }

    #[test]
    fn rule_actions() {
        let action = Action::Trap(7);
        assert_eq!(format!("{:?}", rule!(allow getpid())),
            "Rule { action: Allow, syscall: Getpid, cond: True, archs: [], no_mux: false }");
        assert_eq!(format!("{:?}", rule!(errno(1) getpid()).action), "Errno(1)");
        assert_eq!(format!("{:?}", rule!(errno(1 + 1) getpid()).action), "Errno(2)");
        assert_eq!(format!("{:?}", rule!(kill getpid()).action), "KillProcess");
        assert_eq!(format!("{:?}", rule!(kill_thread getpid()).action), "KillThread");
        assert_eq!(format!("{:?}", rule!(trap(3) getpid()).action), "Trap(3)");
        assert_eq!(format!("{:?}", rule!(trace(u16::MAX) getpid()).action), "Trace(65535)");
        assert_eq!(format!("{:?}", rule!(log getpid()).action), "Log");
        assert_eq!(format!("{:?}", rule!(notify getpid()).action), "Notify");
        assert_eq!(format!("{:?}", rule!({action} getpid()).action), "Trap(7)");
        assert_eq!(format!("{:?}", rule!({Action::Notify} getpid()).action), "Notify");
    }

    #[test]
    fn rule_syscalls() {
        let syscall = Syscall::Lseek;
        assert_eq!(format!("{:?}", rule!(allow exit_group(status)).syscall), "ExitGroup");
        assert_eq!(format!("{:?}", rule!(allow _llseek(fd)).syscall), "_Llseek");
        assert_eq!(format!("{:?}", rule!(allow break()).syscall), "Break");
        assert_eq!(format!("{:?}", rule!(allow kill(pid, sig)).syscall), "Kill");
        assert_eq!(format!("{:?}", rule!(kill kill(pid, sig)).syscall), "Kill");
        assert_eq!(format!("{:?}", rule!(allow {syscall}(fd, offset) if offset == 0isize)),
            "Rule { action: Allow, syscall: Lseek, cond: Cmp(Eq, Var(1), Lit(0, IWord)), archs: [], no_mux: false }");
    }

    #[test]
    fn rule_exact() {
        let syscall = Syscall::Socket;
        assert!(rule!(allow exact bind(fd, addr, len)).no_mux);
        assert!(rule!(allow exact {syscall}()).no_mux);
        assert!(!rule!(allow bind(fd, addr, len)).no_mux);
        assert_eq!(format!("{:?}", rule!([x86] errno(1) exact socket(domain) if domain == 1)),
            "Rule { action: Errno(1), syscall: Socket, cond: Cmp(Eq, Var(0), Lit(1, I(32))), archs: [X86], no_mux: true }");
    }

    #[test]
    fn rule_archs() {
        let native = Arch::Arm;
        let archs = [Arch::X86, Arch::Aarch64];
        assert_eq!(format!("{:?}", rule!([x86] allow getpid()).archs), "[X86]");
        assert_eq!(format!("{:?}", rule!([x86, x86_64, arm, aarch64] allow getpid()).archs), "[X86, X86_64, Arm, Aarch64]");
        assert_eq!(format!("{:?}", rule!([{native}] allow getpid()).archs), "[Arm]");
        assert_eq!(format!("{:?}", rule!([x86_64, {archs[1]}] allow getpid()).archs), "[X86_64, Aarch64]");
        assert_eq!(format!("{:?}", rule!([x86, x86] allow getpid()).archs), "[X86]");
        assert_eq!(format!("{:?}", rule!([x86, arm,] allow getpid()).archs), "[X86, Arm]");
    }

    #[test]
    fn rule_conds() {
        assert_eq!(format!("{:?}", rule!(allow getpid()).cond), "True");
        assert_eq!(format!("{:?}", rule!(allow getpid() if false).cond), "False");
        assert_eq!(format!("{:?}", rule!([arm] allow getpid() if true || false).cond), "Or(True, False)");
        assert_eq!(format!("{:?}", rule!(allow write(fd, buf, count) if fd == 1u32 || count < 2usize).cond),
            "Or(Cmp(Eq, Var(0), Lit(1, U(32))), Cmp(Lt, Var(2), Lit(2, UWord)))");
        let c = cond!(@0 == 1);
        assert_eq!(format!("{:?}", rule!(allow getpid() if {&c} && !{c}).cond),
            "And(Cmp(Eq, Var(0), Lit(1, I(32))), Not(Cmp(Eq, Var(0), Lit(1, I(32)))))");
    }

    #[test]
    fn rule_names() {
        // `_` skips a position, and the names may stop short of the signature.
        assert_eq!(format!("{:?}", rule!(allow openat(_, _, flags) if flags == 0).cond),
            "Cmp(Eq, Var(2), Lit(0, I(32)))");
        assert_eq!(format!("{:?}", rule!(allow mmap(a, b, c, d, e, f) if f == a).cond), "Cmp(Eq, Var(5), Var(0))");
        assert_eq!(format!("{:?}", rule!(allow read(fd,) if fd == 0).cond), "Cmp(Eq, Var(0), Lit(0, I(32)))");
        // `@n` still means position `n` next to the names.
        assert_eq!(format!("{:?}", rule!(allow read(fd) if fd == @2).cond), "Cmp(Eq, Var(0), Var(2))");
        // A bare Rust variable is a value, and a name hides one of the same name, even in `{..}`.
        let fd = 3u32;
        assert_eq!(format!("{:?}", rule!(allow read(count) if count == fd).cond), "Cmp(Eq, Var(0), Lit(3, U(32)))");
        assert_eq!(format!("{:?}", rule!(allow read(fd) if fd == {fd}).cond), "Cmp(Eq, Var(0), Var(0))");
        assert_eq!(fd, 3);
    }

    #[test]
    fn lookup() {
        assert_eq!(Syscall::lookup("read"), Some(Syscall::Read));
        assert_eq!(Syscall::lookup("_llseek"), Some(Syscall::_Llseek));
        assert_eq!(Syscall::lookup("skip"), Some(Syscall::Skip));
        assert_eq!(Syscall::lookup("rea"), None);
        assert_eq!(Syscall::lookup("readx"), None);
        assert_eq!(Syscall::lookup("Read"), None);
        assert_eq!(Syscall::lookup(""), None);
    }

    #[test]
    fn policy_header() {
        let other = Arch::Arm;
        assert_eq!(format!("{:?}", policy!(default allow on x86).unwrap()),
            "Policy { archs: [X86], rules: [], act_no_match: Allow, act_bad_arch: KillThread }");
        assert_eq!(format!("{:?}", policy!(default errno(1) on x86, x86_64, arm, aarch64 else kill).unwrap()),
            "Policy { archs: [X86, X86_64, Arm, Aarch64], rules: [], act_no_match: Errno(1), act_bad_arch: KillProcess }");
        assert_eq!(format!("{:?}", policy!(default {Action::Log} on {other} else trap(1 + 1)).unwrap()),
            "Policy { archs: [Arm], rules: [], act_no_match: Log, act_bad_arch: Trap(2) }");
        assert_eq!(policy!(default kill_thread on native).unwrap().archs, [Arch::native().unwrap()]);
        assert_eq!(policy!(default allow on x86, x86).unwrap().archs, [Arch::X86]);
    }

    #[test]
    fn policy_rules() {
        let extra = rule!(log getuid());
        let policy = policy! {
            default allow on x86;
            errno(1) getpid();
            [x86] kill exact read(fd) if fd == 0u32;
            {extra.clone()}
        }.unwrap();
        assert_eq!(policy.rules, [rule!(errno(1) getpid()), rule!([x86] kill exact read(fd) if fd == 0u32), extra]);
        // The last `;` may be left off.
        assert_eq!(policy!(default allow on x86; allow getpid();), policy!(default allow on x86; allow getpid()));
    }

    #[test]
    fn policy_errors() {
        assert!(matches!(policy!(default errno(4096) on x86), Err(Error::Check(CheckError::InvalidErrno(_)))));
        assert!(matches!(policy!(default allow on x86 else errno(4096)), Err(Error::Check(CheckError::InvalidErrno(_)))));
        assert!(matches!(policy!(default allow on x86; [arm] allow getpid()), Err(Error::Check(CheckError::RuleArchNotEnabled))));
        assert!(matches!(
            policy!(default allow on x86; allow getpid(); errno(4096) getppid()),
            Err(Error::Check(CheckError::InvalidErrno(_))),
        ));
    }

    #[test]
    fn policy_long() {
        // A hundred rules without conditions stay under the default `recursion_limit`.
        let policy = policy! {
            default allow on x86_64;
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
            allow read(fd, buf, count);
        }.unwrap();
        assert_eq!(policy.rules.len(), 100);
    }
}
