//! The filter as the builder sees it, addressed by labels instead of program counters.
//!
//! A label counts instructions back from the end of the program, so it names the same
//! program point however much is later emitted in front of it, and a fact proved about
//! the instructions emitted so far still holds of the whole program.

use vstd::prelude::*;
use crate::spec::cbpf::*;
use super::builder::Builder;

verus! {

/// The machine state apart from the program counter.
#[allow(dead_code)]
pub(super) struct Regs {
    pub(super) a: u32,
    pub(super) x: u32,
    pub(super) mem: Seq<Option<u32>>,
}

impl Regs {
    /// The machine state with these registers at program counter `pc`.
    pub(super) open spec fn at(self, pc: nat) -> MachineState {
        MachineState { pc, a: self.a, x: self.x, mem: self.mem }
    }

    /// The registers of machine state `st`.
    pub(super) open spec fn of(st: MachineState) -> Regs {
        Regs { a: st.a, x: st.x, mem: st.mem }
    }

    /// Whether scratch memory has the size the kernel gives it.
    pub(super) open spec fn wf(self) -> bool {
        self.mem.len() == Program::MEM_WORDS
    }

    /// Whether `A op src` holds in these registers.
    pub(super) open spec fn test(self, op: JmpOp, src: Src) -> bool {
        op.eval(self.a, src.eval(self.at(0)))
    }
}

impl Instr {
    /// Every instruction moves the program counter forward.
    pub(super) proof fn lemma_advances(self, data: &[u8], st: MachineState)
        ensures self.step(data, st) matches Ok(next) ==> next.pc > st.pc
    {
    }

    /// An instruction does the same wherever it sits, apart from where it leaves the
    /// program counter.
    pub(super) proof fn lemma_shift(self, data: &[u8], r: Regs, pc: nat, other: nat)
        ensures
            self.step(data, r.at(pc)) matches Ok(next) ==> {
                &&& self.step(data, r.at(other)) matches Ok(then)
                &&& Regs::of(next) == Regs::of(then)
                &&& next.pc - pc == then.pc - other
            },
            self.step(data, r.at(pc)) matches Err(outcome)
                ==> self.step(data, r.at(other)) == Err::<MachineState, Outcome>(outcome),
    {
    }

    /// Whether the instruction at `pc` of a block of `len` instructions is well-formed,
    /// and jumps no further than the block's end.
    pub(super) open spec fn fits(self, pc: nat, len: nat) -> bool {
        match self {
            Instr::Ja(k) => pc + 1 + k <= len,
            Instr::Jmp { jt, jf, .. } => pc + 1 + jt <= len && pc + 1 + jf <= len,
            _ => Builder::instr_ok(self, 0),
        }
    }

    /// Whether every instruction of `block` from `pc` on fits it.
    pub(super) open spec fn fits_from(block: Seq<Instr>, pc: nat) -> bool
        decreases block.len() - pc
    {
        pc >= block.len() || block[pc as int].fits(pc, block.len()) && Self::fits_from(block, pc + 1)
    }

    /// Every instruction of a block that fits from `pc` on fits it.
    pub(super) proof fn lemma_fits(block: Seq<Instr>, pc: nat)
        requires Self::fits_from(block, pc)
        ensures forall |i: int| #![trigger block[i]] pc <= i < block.len() ==> block[i].fits(i as nat, block.len())
        decreases block.len() - pc
    {
        if pc < block.len() {
            Self::lemma_fits(block, pc + 1);
        }
    }

    /// Runs `block` from instruction `pc` on while control stays inside it, and returns
    /// the registers it leaves the block with.
    pub(super) open spec fn exec_block(block: Seq<Instr>, pc: nat, data: &[u8], r: Regs) -> Option<Regs>
        decreases block.len() - pc
    {
        if pc >= block.len() {
            if pc == block.len() { Some(r) } else { None }
        } else {
            match block[pc as int].step(data, r.at(pc)) {
                Ok(next) => if pc < next.pc <= block.len() {
                    Self::exec_block(block, next.pc, data, Regs::of(next))
                } else {
                    None
                },
                Err(_) => None,
            }
        }
    }
}

impl Builder {
    /// Whether `ext` is `rev` with more instructions emitted in front of it.
    pub(super) open spec fn extends(rev: Seq<Instr>, ext: Seq<Instr>) -> bool {
        &&& rev.len() <= ext.len()
        &&& forall |i: int| #![trigger ext[i]] 0 <= i < rev.len() ==> ext[i] == rev[i]
    }

    /// The little-endian word at byte offset `k` of `data`, as `LdAbs` reads it.
    pub(super) open spec fn word(data: &[u8], k: u32) -> u32 {
        (data@[k as int] as u32)
            | ((data@[k + 1] as u32) << 8)
            | ((data@[k + 2] as u32) << 16)
            | ((data@[k + 3] as u32) << 24)
    }

    /// Runs the instructions emitted so far, entered `label` of them before their end
    /// with registers `r`.
    pub(super) open spec fn run(rev: Seq<Instr>, data: &[u8], label: nat, r: Regs) -> Outcome
        decreases label
        via Self::run_decreases
    {
        if label == 0 || label > rev.len() {
            Outcome::RuntimeError
        } else {
            match rev[label - 1].step(data, r.at(label)) {
                Ok(next) =>
                    if next.pc > 2 * label {
                        Outcome::RuntimeError
                    } else {
                        Self::run(rev, data, (2 * label - next.pc) as nat, Regs::of(next))
                    },
                Err(outcome) => outcome,
            }
        }
    }

    #[via_fn]
    proof fn run_decreases(rev: Seq<Instr>, data: &[u8], label: nat, r: Regs) {
        if label != 0 && label <= rev.len() {
            rev[label - 1].lemma_advances(data, r.at(label));
        }
    }

    /// Whether every extension of `rev`, entered at `from` with registers `r`, carries
    /// on at `to` with registers `t`.
    pub(super) open spec fn goes(rev: Seq<Instr>, data: &[u8], from: nat, r: Regs, to: nat, t: Regs) -> bool {
        forall |ext: Seq<Instr>| Self::extends(rev, ext)
            ==> #[trigger] Self::run(ext, data, from, r) == Self::run(ext, data, to, t)
    }

    /// Whether every extension of `rev`, entered at `from` with registers `r`, carries
    /// on at `to` with some well-formed registers.
    pub(super) open spec fn lands(rev: Seq<Instr>, data: &[u8], from: nat, r: Regs, to: nat) -> bool {
        exists |t: Regs| t.wf() && #[trigger] Self::goes(rev, data, from, r, to, t)
    }

    /// Whether every extension of `rev`, entered at `from` with registers `r`, carries
    /// on at `to` with some well-formed registers whose `A` holds `b`.
    pub(super) open spec fn passes(rev: Seq<Instr>, data: &[u8], from: nat, r: Regs, to: nat, b: u32) -> bool {
        exists |t: Regs| t.wf() && t.a == b && #[trigger] Self::goes(rev, data, from, r, to, t)
    }

    /// Whether every extension of `rev`, entered at `from` with registers `r`, returns `ret`.
    pub(super) open spec fn returns(rev: Seq<Instr>, data: &[u8], from: nat, r: Regs, ret: u32) -> bool {
        forall |ext: Seq<Instr>| Self::extends(rev, ext)
            ==> #[trigger] Self::run(ext, data, from, r) == Outcome::Return(ret)
    }

    /// Whether every extension of `rev`, entered at `from` with any well-formed registers,
    /// returns `ret`.
    pub(super) open spec fn returns_all(rev: Seq<Instr>, data: &[u8], from: nat, ret: u32) -> bool {
        forall |r: Regs| r.wf() ==> #[trigger] Self::returns(rev, data, from, r, ret)
    }

    /// Whether the instruction `i` slots back from the end of the program belongs there.
    pub(super) open spec fn instr_ok(instr: Instr, i: nat) -> bool {
        match instr {
            Instr::LdAbs(k) => k % 4 == 0,
            Instr::Alu(AluOp::Div, Src::K(k)) => k != 0,
            Instr::Alu(AluOp::Lsh, Src::K(k)) => k < 32,
            Instr::Alu(AluOp::Rsh, Src::K(k)) => k < 32,
            Instr::LdMem(k) => k < Program::MEM_WORDS,
            Instr::LdxMem(k) => k < Program::MEM_WORDS,
            Instr::St(k) => k < Program::MEM_WORDS,
            Instr::Stx(k) => k < Program::MEM_WORDS,
            Instr::Ja(k) => k < i,
            Instr::Jmp { jt, jf, .. } => jt < i && jf < i,
            _ => true,
        }
    }

    /// Whether the instructions emitted so far can end a well-formed program.
    pub(super) open spec fn wf(self) -> bool {
        forall |i: int| #![trigger self.rev@[i]]
            0 <= i < self.rev@.len() ==> Self::instr_ok(self.rev@[i], i as nat)
    }

    /// A well-formed buffer whose first instruction returns makes a well-formed program.
    pub(super) proof fn lemma_wf(self, prog: Program)
        requires
            self.wf(),
            0 < self.rev@.len(),
            self.rev@[0] is Ret,
            prog.instrs@ == self.rev@.reverse(),
        ensures
            prog.wf(),
            prog.instrs@.reverse() == self.rev@,
    {
        let len = self.rev@.len();
        assert forall |pc: int| #![trigger prog.instrs@[pc]] 0 <= pc < len implies
            prog.instrs@[pc].wf(pc as nat, len) by {
            assert(Self::instr_ok(self.rev@[len - 1 - pc], (len - 1 - pc) as nat));
        }
        assert(prog.instrs@.reverse() =~= self.rev@);
    }

    /// Entering `from` runs the stretch of code that reaches `mid` and then the one behind it.
    pub(super) proof fn lemma_goes_trans(rev: Seq<Instr>, ext: Seq<Instr>, data: &[u8], from: nat, r: Regs, mid: nat, m: Regs, to: nat, t: Regs)
        requires
            Self::extends(rev, ext),
            Self::goes(ext, data, from, r, mid, m),
            Self::goes(rev, data, mid, m, to, t),
        ensures Self::goes(ext, data, from, r, to, t)
    {
        assert forall |far: Seq<Instr>| Self::extends(ext, far)
            implies #[trigger] Self::run(far, data, from, r) == Self::run(far, data, to, t) by {
            assert(Self::run(far, data, from, r) == Self::run(far, data, mid, m));
            assert(Self::extends(rev, far));
            assert(Self::run(far, data, mid, m) == Self::run(far, data, to, t));
        }
    }

    /// Entering `from` reaches `mid` with registers `m`, and then wherever `mid` goes from there.
    pub(super) proof fn lemma_then(rev: Seq<Instr>, ext: Seq<Instr>, data: &[u8], from: nat, r: Regs, mid: nat, m: Regs, to: nat, b: u32)
        requires
            Self::extends(rev, ext),
            Self::goes(ext, data, from, r, mid, m),
        ensures
            Self::lands(rev, data, mid, m, to) ==> Self::lands(ext, data, from, r, to),
            Self::passes(rev, data, mid, m, to, b) ==> Self::passes(ext, data, from, r, to, b),
            Self::returns(rev, data, mid, m, b) ==> Self::returns(ext, data, from, r, b),
    {
        if Self::lands(rev, data, mid, m, to) {
            let t = choose |t: Regs| t.wf() && #[trigger] Self::goes(rev, data, mid, m, to, t);
            Self::lemma_goes_trans(rev, ext, data, from, r, mid, m, to, t);
        }
        if Self::passes(rev, data, mid, m, to, b) {
            let t = choose |t: Regs| t.wf() && t.a == b && #[trigger] Self::goes(rev, data, mid, m, to, t);
            Self::lemma_goes_trans(rev, ext, data, from, r, mid, m, to, t);
        }
        if Self::returns(rev, data, mid, m, b) {
            assert forall |far: Seq<Instr>| Self::extends(ext, far)
                implies #[trigger] Self::run(far, data, from, r) == Outcome::Return(b) by {
                assert(Self::run(far, data, from, r) == Self::run(far, data, mid, m));
                assert(Self::extends(rev, far));
            }
        }
    }

    /// The instruction at the front of `rev` takes registers `r` to wherever it steps them.
    pub(super) proof fn lemma_front(rev: Seq<Instr>, data: &[u8], r: Regs)
        requires 0 < rev.len()
        ensures
            rev[rev.len() - 1].step(data, r.at(rev.len())) matches Ok(next) ==> (next.pc <= 2 * rev.len()
                ==> Self::goes(rev, data, rev.len(), r, (2 * rev.len() - next.pc) as nat, Regs::of(next))),
            rev[rev.len() - 1].step(data, r.at(rev.len())) matches Err(outcome)
                ==> forall |ext: Seq<Instr>| Self::extends(rev, ext)
                    ==> #[trigger] Self::run(ext, data, rev.len(), r) == outcome,
    {
        let label = rev.len();
        assert forall |ext: Seq<Instr>| Self::extends(rev, ext)
            implies #[trigger] ext[label - 1] == rev[label - 1] by {
        }
    }

    /// The load at the front of `rev` hands `A` the word at `k`.
    pub(super) proof fn lemma_ld(rev: Seq<Instr>, k: u32)
        requires
            0 < rev.len(),
            rev[rev.len() - 1] == Instr::LdAbs(k),
        ensures
            forall |data: &[u8], r: Regs| k + 4 <= data@.len() ==>
                #[trigger] Self::goes(rev, data, rev.len(), r, (rev.len() - 1) as nat,
                    Regs { a: Self::word(data, k), ..r }),
    {
        assert forall |data: &[u8], r: Regs| k + 4 <= data@.len() implies
            #[trigger] Self::goes(rev, data, rev.len(), r, (rev.len() - 1) as nat,
                Regs { a: Self::word(data, k), ..r }) by {
            Self::lemma_front(rev, data, r);
        }
    }

    /// The operation at the front of `rev` applies `op` to `A`.
    pub(super) proof fn lemma_alu(rev: Seq<Instr>, op: AluOp, k: u32)
        requires
            0 < rev.len(),
            rev[rev.len() - 1] == Instr::Alu(op, Src::K(k)),
            !(op is Div && k == 0),
        ensures
            forall |data: &[u8], r: Regs| #[trigger] Self::goes(rev, data, rev.len(), r,
                (rev.len() - 1) as nat, Regs { a: op.eval(r.a, k), ..r }),
    {
        assert forall |data: &[u8], r: Regs| #[trigger] Self::goes(rev, data, rev.len(), r,
            (rev.len() - 1) as nat, Regs { a: op.eval(r.a, k), ..r }) by {
            Self::lemma_front(rev, data, r);
        }
    }

    /// The return at `label` ends the filter with `k`.
    pub(super) proof fn lemma_ret(rev: Seq<Instr>, label: nat, k: u32)
        requires 0 < label <= rev.len(), rev[label - 1] == Instr::Ret(RetVal::K(k))
        ensures forall |data: &[u8]| #[trigger] Self::returns_all(rev, data, label, k)
    {
        assert forall |data: &[u8], r: Regs| #[trigger] Self::returns(rev, data, label, r, k) by {
            assert forall |ext: Seq<Instr>| Self::extends(rev, ext)
                implies #[trigger] Self::run(ext, data, label, r) == Outcome::Return(k) by {
                assert(ext[label - 1] == rev[label - 1]);
            }
        }
    }

    /// The unconditional jump at the front of `rev` skips `k` instructions.
    pub(super) proof fn lemma_ja(rev: Seq<Instr>, k: u32)
        requires 0 < rev.len(), rev[rev.len() - 1] == Instr::Ja(k), k < rev.len() - 1
        ensures
            forall |data: &[u8], r: Regs, to: nat|
                to == rev.len() - 1 - k ==> #[trigger] Self::goes(rev, data, rev.len(), r, to, r),
    {
        assert forall |data: &[u8], r: Regs, to: nat|
            to == rev.len() - 1 - k implies #[trigger] Self::goes(rev, data, rev.len(), r, to, r) by {
            Self::lemma_front(rev, data, r);
        }
    }

    /// The conditional jump at the front of `rev` skips `jt` instructions when `A op src`
    /// holds and `jf` when it does not.
    pub(super) proof fn lemma_jmp(rev: Seq<Instr>, op: JmpOp, src: Src, jt: u8, jf: u8)
        requires
            0 < rev.len(),
            rev[rev.len() - 1] == (Instr::Jmp { op, src, jt, jf }),
            jt < rev.len() - 1,
            jf < rev.len() - 1,
        ensures
            forall |data: &[u8], r: Regs, to: nat| r.test(op, src) && to == rev.len() - 1 - jt ==>
                #[trigger] Self::goes(rev, data, rev.len(), r, to, r),
            forall |data: &[u8], r: Regs, to: nat| !r.test(op, src) && to == rev.len() - 1 - jf ==>
                #[trigger] Self::goes(rev, data, rev.len(), r, to, r),
    {
        assert forall |data: &[u8], r: Regs, to: nat|
            (r.test(op, src) && to == rev.len() - 1 - jt) || (!r.test(op, src) && to == rev.len() - 1 - jf)
            implies #[trigger] Self::goes(rev, data, rev.len(), r, to, r) by {
            Self::lemma_front(rev, data, r);
        }
    }

    /// A block emitted in front of `base` runs from its instruction `pc` on as
    /// [`Instr::exec_block`] says.
    pub(super) proof fn lemma_block(rev: Seq<Instr>, base: nat, block: Seq<Instr>, data: &[u8], pc: nat, r: Regs)
        requires
            rev.len() == base + block.len(),
            forall |i: int| #![trigger block[i]] 0 <= i < block.len() ==> rev[base + block.len() - 1 - i] == block[i],
            pc <= block.len(),
        ensures
            Instr::exec_block(block, pc, data, r) matches Some(t)
                ==> Self::goes(rev, data, (base + block.len() - pc) as nat, r, base, t),
        decreases block.len() - pc
    {
        let label = (base + block.len() - pc) as nat;
        if pc < block.len() {
            let instr = block[pc as int];
            assert(rev[base + block.len() - 1 - pc] == instr);
            assert(rev[label - 1] == instr);
            instr.lemma_shift(data, r, pc, label);
            if let Ok(next) = instr.step(data, r.at(pc)) {
                if pc < next.pc <= block.len() {
                    Self::lemma_block(rev, base, block, data, next.pc, Regs::of(next));
                    if let Some(t) = Instr::exec_block(block, pc, data, r) {
                        let then = instr.step(data, r.at(label))->Ok_0;
                        assert forall |ext: Seq<Instr>| Self::extends(rev, ext)
                            implies #[trigger] Self::run(ext, data, label, r)
                                == Self::run(ext, data, (base + block.len() - next.pc) as nat, Regs::of(next)) by {
                            assert(ext[label - 1] == instr);
                            assert(then.pc <= 2 * label);
                            assert((2 * label - then.pc) as nat == (base + block.len() - next.pc) as nat);
                        }
                        Self::lemma_goes_trans(rev, rev, data, label, r,
                            (base + block.len() - next.pc) as nat, Regs::of(next), base, t);
                    }
                }
            }
        }
    }
}

impl Program {
    /// The filter's outcome from an arbitrary state, seen through the builder's labels.
    pub(super) proof fn lemma_run_from(self, data: &[u8], st: MachineState)
        requires
            self.wf(),
            st.pc <= self.instrs@.len(),
        ensures self.eval_from(data, st)
            == Builder::run(self.instrs@.reverse(), data, (self.instrs@.len() - st.pc) as nat, Regs::of(st))
        decreases self.instrs@.len() - st.pc
    {
        let len = self.instrs@.len();
        if st.pc < len {
            let instr = self.instrs@[st.pc as int];
            let label = (len - st.pc) as nat;
            assert(self.instrs@.reverse()[label - 1] == instr);
            assert(instr.wf(st.pc, len));
            assert(Regs::of(st).at(st.pc) == st);
            instr.lemma_shift(data, Regs::of(st), st.pc, label);
            if instr.step(data, st) is Ok {
                self.lemma_run_from(data, instr.step(data, st)->Ok_0);
            }
        }
    }

    /// The filter's outcome, seen through the builder's labels.
    pub(super) proof fn lemma_run(self, data: &[u8])
        requires self.wf()
        ensures
            self.eval(data) == Builder::run(self.instrs@.reverse(), data, self.instrs@.len(),
                Regs::of(MachineState::init())),
            Regs::of(MachineState::init()).wf(),
            Regs::of(MachineState::init()).a == 0,
    {
        self.lemma_run_from(data, MachineState::init());
    }
}

} // verus!
