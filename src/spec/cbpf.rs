//! Abstract syntax and semantics of a subset of cBPF accepted by seccomp.

use vstd::prelude::*;

// Syntax
verus! {

#[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub enum Src { K(u32), X }

#[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub enum RetVal { K(u32), A }

#[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub enum AluOp {
    Add = 0x00, Sub = 0x10, Mul = 0x20, Div = 0x30, Or = 0x40,
    And = 0x50, Lsh = 0x60, Rsh = 0x70, Xor = 0xa0,
}

/// Comparison of a conditional jump (`BPF_OP` of class `BPF_JMP`, except `BPF_JA`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub enum JmpOp { Eq = 0x10, Gt = 0x20, Ge = 0x30, Set = 0x40 }

/// `struct sock_filter`, restricted to instructions accepted by `seccomp_check_filter()`:
/// <https://github.com/torvalds/linux/blob/40288c9206c17eb66a603262e06a58d300d0f279/kernel/seccomp.c#L286-L343>
#[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub enum Instr {
    /// `BPF_LD | BPF_W | BPF_ABS`: `A = *(u32 *)((char *)&data + k)`.
    LdAbs(u32),
    /// `BPF_LD | BPF_W | BPF_LEN`: `A = data.len()`.
    LdLen,
    /// `BPF_LD | BPF_IMM`: `A = k`.
    LdImm(u32),
    /// `BPF_LD | BPF_MEM`: `A = M[k]`.
    LdMem(u32),
    /// `BPF_LDX | BPF_W | BPF_LEN`: `X = data.len()`.
    LdxLen,
    /// `BPF_LDX | BPF_IMM`: `X = k`.
    LdxImm(u32),
    /// `BPF_LDX | BPF_MEM`: `X = M[k]`.
    LdxMem(u32),
    /// `BPF_ST`: `M[k] = A`.
    St(u32),
    /// `BPF_STX`: `M[k] = X`.
    Stx(u32),
    /// `BPF_ALU | op | src`: `A = A op src`.
    Alu(AluOp, Src),
    /// `BPF_ALU | BPF_NEG`: `A = -A`.
    Neg,
    /// `BPF_JMP | BPF_JA`: skip `k` instructions.
    Ja(u32),
    /// `BPF_JMP | op | src`: skip `jt` instructions if `A op src` holds, else `jf`.
    Jmp { op: JmpOp, src: Src, jt: u8, jf: u8 },
    /// `BPF_RET | rval`: return `rval`.
    Ret(RetVal),
    /// `BPF_MISC | BPF_TAX`: `X = A`.
    Tax,
    /// `BPF_MISC | BPF_TXA`: `A = X`.
    Txa,
}

/// `struct sock_fprog`.
#[derive(Debug, Clone, PartialEq, Eq)]
// Verus does not yet model non-Copy Clone derives.
#[verifier::external_derive(Clone)]
pub struct Program {
    pub instrs: Vec<Instr>,
}

impl Instr {
    /// Well-formed instructions.
    pub open spec fn wf(self, pc: nat, max_pc: nat) -> bool {
        match self {
            Instr::LdAbs(k) => k % 4 == 0,
            // Check for division by zero.
            Instr::Alu(AluOp::Div, Src::K(k)) => k != 0,
            Instr::Alu(AluOp::Lsh, Src::K(k)) => k < 32,
            Instr::Alu(AluOp::Rsh, Src::K(k)) => k < 32,
            // Check for invalid memory addresses.
            Instr::LdMem(k) => k < Program::MEM_WORDS,
            Instr::LdxMem(k) => k < Program::MEM_WORDS,
            Instr::St(k) => k < Program::MEM_WORDS,
            Instr::Stx(k) => k < Program::MEM_WORDS,
            // Jump targets stay inside the program.
            Instr::Ja(k) => pc + 1 + k < max_pc,
            Instr::Jmp { jt, jf, .. } => pc + 1 + jt < max_pc && pc + 1 + jf < max_pc,
            _ => true,
        }
    }
}

impl Program {
    /// `BPF_MEMWORDS` in `linux/bpf_common.h`.
    pub const MEM_WORDS: u32 = 16;

    /// Structural instruction validity, without input-buffer bounds, Linux installation
    /// limits, or scratch-memory initialization analysis.
    pub open spec fn wf(self) -> bool {
        &&& self.instrs@.last() is Ret
        &&& forall |pc: int| #![trigger self.instrs@[pc]]
                0 <= pc < self.instrs@.len() ==> self.instrs@[pc].wf(pc as nat, self.instrs@.len())
    }
}

} // verus!

// Semantics
verus! {

#[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub enum Outcome {
    Return(u32),
    RuntimeError,
}

pub struct MachineState {
    pub pc: nat,
    pub a: u32,
    pub x: u32,
    pub mem: Seq<Option<u32>>,
}

impl Src {
    pub open spec fn eval(self, st: MachineState) -> u32 {
        match self {
            Src::K(k) => k,
            Src::X => st.x,
        }
    }
}

impl RetVal {
    pub open spec fn eval(self, st: MachineState) -> u32 {
        match self {
            RetVal::K(k) => k,
            RetVal::A => st.a,
        }
    }
}

impl AluOp {
    /// Applies the ALU operator to 32-bit operands.
    pub open spec fn eval(self, lhs: u32, rhs: u32) -> u32 {
        match self {
            AluOp::Add => (lhs + rhs) as u32,
            AluOp::Sub => (lhs - rhs) as u32,
            AluOp::Mul => (lhs * rhs) as u32,
            AluOp::Div => lhs / rhs,
            AluOp::Or  => lhs | rhs,
            AluOp::And => lhs & rhs,
            AluOp::Xor => lhs ^ rhs,
            AluOp::Lsh => lhs << (rhs % 32),
            AluOp::Rsh => lhs >> (rhs % 32),
        }
    }
}

impl JmpOp {
    /// Evaluates an unsigned comparison.
    pub open spec fn eval(self, lhs: u32, rhs: u32) -> bool {
        match self {
            JmpOp::Eq => lhs == rhs,
            JmpOp::Gt => lhs > rhs,
            JmpOp::Ge => lhs >= rhs,
            JmpOp::Set => (lhs & rhs) != 0,
        }
    }
}

impl MachineState {
    /// `bpf_convert_filter()` zeroes A and X before the first cBPF instruction:
    /// <https://github.com/torvalds/linux/blob/40288c9206c17eb66a603262e06a58d300d0f279/net/core/filter.c#L613-L617>.
    /// Scratch memory is uninitialized stack.
    pub open spec fn init() -> Self {
        MachineState {
            pc: 0,
            a: 0,
            x: 0,
            mem: Seq::new(Program::MEM_WORDS as nat, |_: int| None),
        }
    }

    pub open spec fn next_a(self, a: u32) -> Self {
        MachineState {
            pc: self.pc + 1,
            a,
            ..self
        }
    }

    pub open spec fn next_x(self, x: u32) -> Self {
        MachineState {
            pc: self.pc + 1,
            x,
            ..self
        }
    }

    pub open spec fn next_mem(self, k: int, v: u32) -> Self
        recommends 0 <= k < self.mem.len(),
    {
        MachineState {
            pc: self.pc + 1,
            mem: self.mem.update(k, Some(v)),
            ..self
        }
    }

    /// Advances past the current instruction and then skip `n` instructions.
    pub open spec fn jump(self, n: nat) -> Self {
        MachineState {
            pc: self.pc + 1 + n,
            ..self
        }
    }
}

impl Instr {
    /// Executes exactly one instruction.
    ///
    /// `Ok(st)` means execution continues in `st`.
    /// `Err(outcome)` means execution terminates with `outcome`.
    ///
    /// `data` is the 64-byte image of `struct seccomp_data` in little endian.
    pub open spec fn step(self, data: &[u8], st: MachineState) -> Result<MachineState, Outcome> {
        match self {
            Instr::LdAbs(k) => {
                if k + 4 <= data@.len() {
                    // Load the 32-bit word at byte offset `off` of `data`, the in-memory image of
                    // `struct seccomp_data`, in *little endian*.
                    // Unlike socket filters, seccomp context loads are not byte-swapped:
                    // `seccomp_check_filter()` rewrites `BPF_LD | BPF_W | BPF_ABS` into the
                    // kernel-internal `BPF_LDX | BPF_W | BPF_ABS`
                    // (<https://github.com/torvalds/linux/blob/40288c9206c17eb66a603262e06a58d300d0f279/kernel/seccomp.c#L287-L288>).
                    let b0 = data@[k as int] as u32;
                    let b1 = data@[k + 1] as u32;
                    let b2 = data@[k + 2] as u32;
                    let b3 = data@[k + 3] as u32;
                    Ok(st.next_a(b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)))
                } else {
                    // Rejected statically by `seccomp_check_filter()`.
                    Err(Outcome::RuntimeError)
                }
            }
            Instr::LdLen => Ok(st.next_a(data.len() as u32)),
            Instr::LdImm(k) => Ok(st.next_a(k)),
            Instr::LdMem(k) => {
                if k < st.mem.len() {
                    match st.mem[k as int] {
                        Some(v) => Ok(st.next_a(v)),
                        // `check_load_and_stores()`.
                        None => Err(Outcome::RuntimeError),
                    }
                } else {
                    Err(Outcome::RuntimeError)
                }
            }
            Instr::LdxLen => Ok(st.next_x(data@.len() as u32)),
            Instr::LdxImm(k) => Ok(st.next_x(k)),
            Instr::LdxMem(k) => {
                if k < st.mem.len() {
                    match st.mem[k as int] {
                        Some(v) => Ok(st.next_x(v)),
                        None => Err(Outcome::RuntimeError),
                    }
                } else {
                    Err(Outcome::RuntimeError)
                }
            }
            Instr::St(k) => {
                if k < st.mem.len() {
                    Ok(st.next_mem(k as int, st.a))
                } else {
                    Err(Outcome::RuntimeError)
                }
            }
            Instr::Stx(k) => {
                if k < st.mem.len() {
                    Ok(st.next_mem(k as int, st.x))
                } else {
                    Err(Outcome::RuntimeError)
                }
            }
            // [`bpf_convert_filter()`](https://github.com/torvalds/linux/blob/40288c9206c17eb66a603262e06a58d300d0f279/net/core/filter.c#L693-L702).
            Instr::Alu(op, src) => {
                let rhs = src.eval(st);
                if op is Div && rhs == 0 {
                    Err(Outcome::Return(0))
                } else {
                    Ok(st.next_a(op.eval(st.a, rhs)))
                }
            }
            Instr::Neg => Ok(st.next_a(-st.a as u32)),
            Instr::Ja(k) => Ok(st.jump(k as nat)),
            Instr::Jmp { op, src, jt, jf } => {
                let rhs = src.eval(st);
                let skip = if op.eval(st.a, rhs) { jt as nat } else { jf as nat };
                Ok(st.jump(skip))
            }
            Instr::Ret(rval) => Err(Outcome::Return(rval.eval(st))),
            Instr::Tax => Ok(st.next_x(st.a)),
            Instr::Txa => Ok(st.next_a(st.x)),
        }
    }
}

impl Program {
    /// Executes from an arbitrary machine state.
    pub open spec fn eval_from(self, data: &[u8], st: MachineState) -> Outcome
        decreases self.instrs@.len() - st.pc when self.wf()
    {
        if st.pc >= self.instrs@.len() {
            Outcome::RuntimeError
        } else {
            match self.instrs@[st.pc as int].step(data, st) {
                Ok(next) => self.eval_from(data, next),
                Err(outcome) => outcome,
            }
        }
    }

    /// Runs the filter on one `struct seccomp_data` (in little endian).
    pub open spec fn eval(self, data: &[u8]) -> Outcome
        recommends self.wf()
    {
        self.eval_from(data, MachineState::init())
    }
}

} // verus!
