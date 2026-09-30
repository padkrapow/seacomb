//! `Display` impls for policy AST.

use std::fmt::{self, Display, Formatter};
use crate::spec::{policy::*, expr::*, syscall::Syscall};

impl Display for PrimType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            PrimType::I(n) => write!(f, "i{n}"),
            PrimType::U(n) => write!(f, "u{n}"),
            PrimType::IWord => write!(f, "isize"),
            PrimType::UWord => write!(f, "usize"),
            PrimType::Ptr => write!(f, "ptr"),
        }
    }
}

impl Display for Syscall {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

impl Display for CmpOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            CmpOp::Eq => "equality",
            CmpOp::Lt => "less-than",
            CmpOp::Le => "less-or-equal",
        })
    }
}

impl Display for BinOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            BinOp::Add => "addition",
            BinOp::Sub => "subtraction",
            BinOp::And => "bitwise-and",
            BinOp::Or => "bitwise-or",
            BinOp::Xor => "bitwise-xor",
        })
    }
}

impl Expr {
    /// How tightly this expression binds in `expr!`.
    fn prec(&self) -> u8 {
        match self {
            Expr::BinOp(BinOp::Or, ..) => 0,
            Expr::BinOp(BinOp::Xor, ..) => 1,
            Expr::BinOp(BinOp::And, ..) => 2,
            Expr::BinOp(BinOp::Add | BinOp::Sub, ..) => 3,
            _ => 4,
        }
    }

    /// Writes this expression, in parentheses if it binds looser than `prec`.
    fn fmt_prec(&self, f: &mut Formatter<'_>, prec: u8) -> fmt::Result {
        if self.prec() < prec { write!(f, "({self})") } else { write!(f, "{self}") }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Var(i) => write!(f, "@{i}"),
            // `expr!` reads an unsuffixed literal as an `i32`.
            Expr::Lit(v, PrimType::I(32)) => write!(f, "{v}"),
            Expr::Lit(v, ty) if !ty.exec_signed() => write!(f, "{}{ty}", *v as u64),
            Expr::Lit(v, ty) => write!(f, "{v}{ty}"),
            Expr::Cast(e, ty) => {
                e.fmt_prec(f, 4)?;
                write!(f, " as {ty}")
            }
            // Left-associative, so only the right operand needs parentheses at the same precedence.
            Expr::BinOp(op, l, r) => {
                l.fmt_prec(f, self.prec())?;
                f.write_str(match op {
                    BinOp::Add => " + ",
                    BinOp::Sub => " - ",
                    BinOp::And => " & ",
                    BinOp::Or => " | ",
                    BinOp::Xor => " ^ ",
                })?;
                r.fmt_prec(f, self.prec() + 1)
            }
        }
    }
}

impl Cond {
    /// How tightly this condition binds in `cond!`, from 0 for `||` up to 3 for an operand of `!`.
    fn prec(&self) -> u8 {
        match self {
            Cond::Or(..) => 0,
            Cond::And(..) => 1,
            Cond::Cmp(..) => 2,
            Cond::Not(c) if matches!(**c, Cond::Cmp(CmpOp::Eq, ..)) => 2,
            _ => 3,
        }
    }

    /// Writes this condition, in parentheses if it binds looser than `prec`.
    fn fmt_prec(&self, f: &mut Formatter<'_>, prec: u8) -> fmt::Result {
        if self.prec() < prec { write!(f, "({self})") } else { write!(f, "{self}") }
    }
}

impl Display for Cond {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Cond::True => f.write_str("true"),
            Cond::False => f.write_str("false"),
            // `cond!` turns `>` and `>=` into `<` and `<=`, so those are all it needs.
            Cond::Cmp(op, l, r) => {
                let op = match op {
                    CmpOp::Eq => "==",
                    CmpOp::Lt => "<",
                    CmpOp::Le => "<=",
                };
                write!(f, "{l} {op} {r}")
            }
            Cond::Not(c) => match &**c {
                Cond::Cmp(CmpOp::Eq, l, r) => write!(f, "{l} != {r}"),
                c => {
                    f.write_str("!")?;
                    c.fmt_prec(f, 3)
                }
            },
            Cond::And(l, r) => {
                l.fmt_prec(f, 1)?;
                f.write_str(" && ")?;
                r.fmt_prec(f, 2)
            }
            Cond::Or(l, r) => {
                l.fmt_prec(f, 0)?;
                f.write_str(" || ")?;
                r.fmt_prec(f, 1)
            }
        }
    }
}

impl Display for Arch {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Arch::X86 => "x86",
            Arch::X86_64 => "x86_64",
            Arch::Arm => "arm",
            Arch::Aarch64 => "aarch64",
        })
    }
}

impl Display for Action {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Action::KillProcess => f.write_str("kill"),
            Action::KillThread => f.write_str("kill_thread"),
            Action::Trap(n) => write!(f, "trap({n})"),
            Action::Errno(n) => write!(f, "errno({n})"),
            Action::Trace(n) => write!(f, "trace({n})"),
            Action::Log => f.write_str("log"),
            Action::Allow => f.write_str("allow"),
            Action::Notify => f.write_str("notify"),
        }
    }
}

impl Display for Rule {
    /// Writes the rule with no argument names, so its condition refers to each argument as `@n`.
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if !self.archs.is_empty() {
            let archs: Vec<_> = self.archs.iter().map(Arch::to_string).collect();
            write!(f, "[{}] ", archs.join(", "))?;
        }
        write!(f, "{} ", self.action)?;
        if self.no_mux {
            f.write_str("exact ")?;
        }
        write!(f, "{}()", self.syscall)?;
        if *self.cond != Cond::True {
            write!(f, " if {}", self.cond)?;
        }
        Ok(())
    }
}

impl Display for Policy {
    /// Writes the header and then each rule on a line of its own.
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let archs: Vec<_> = self.archs.iter().map(Arch::to_string).collect();
        write!(f, "default {} on {} else {};", self.act_no_match, archs.join(", "), self.act_bad_arch)?;
        for rule in &self.rules {
            write!(f, "\n{rule};")?;
        }
        Ok(())
    }
}
