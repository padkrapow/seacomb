//! The buffer a filter is assembled in, back to front.

use vstd::prelude::*;
use crate::spec::cbpf::*;
use super::CompileError;
#[allow(unused_imports)]
use super::machine::Regs;

verus! {

/// A program point of a [`Builder`], to be used as a jump target.
pub(super) type Label = usize;

/// Assembles a program *back to front* to calculate jump offets more easily.
pub(super) struct Builder {
    /// The instructions emitted so far, in reverse program order.
    pub(super) rev: Vec<Instr>,
}

impl Builder {
    pub(super) fn new() -> (res: Builder)
        ensures res.rev@.len() == 0
    {
        Builder { rev: Vec::new() }
    }

    /// The point just in front of everything emitted so far, i.e. where control
    /// arrives once the instructions emitted up to now have run to their end.
    pub(super) fn label(&self) -> (res: Label)
        ensures res == self.rev@.len()
    {
        self.rev.len()
    }

    /// Puts one instruction in front of the program.
    pub(super) fn emit(&mut self, instr: Instr)
        ensures
            Builder::extends(old(self).rev@, final(self).rev@),
            final(self).rev@ == old(self).rev@.push(instr),
            old(self).wf() && Builder::instr_ok(instr, old(self).rev@.len()) ==> final(self).wf(),
    {
        self.rev.push(instr);
    }

    /// Puts a conditional jump in front of the program: control moves to `target`
    /// when `A op src` equals `expect`, and falls through otherwise.
    ///
    /// A cBPF jump offset is a single byte, so a target further away than that is
    /// reached through a `Ja` trampoline.
    pub(super) fn emit_jump(&mut self, op: JmpOp, src: Src, expect: bool, target: Label) -> (res: Result<(), CompileError>)
        requires
            0 < target <= self.rev@.len(),
            self.wf(),
        ensures
            Builder::extends(old(self).rev@, final(self).rev@),
            final(self).wf(),
            res is Ok ==> forall |data: &[u8], r: Regs| r.test(op, src) == expect ==>
                #[trigger] Builder::goes(final(self).rev@, data, final(self).rev@.len(), r, target as nat, r),
            res is Ok ==> forall |data: &[u8], r: Regs| r.test(op, src) != expect ==>
                #[trigger] Builder::goes(final(self).rev@, data, final(self).rev@.len(), r,
                    old(self).rev@.len(), r),
            res is Ok ==> forall |data: &[u8], r: Regs, to: nat|
                (r.test(op, src) == expect ==> to == target)
                && (r.test(op, src) != expect ==>
                    Builder::lands(old(self).rev@, data, old(self).rev@.len(), r, to))
                && r.wf() ==> #[trigger] Builder::lands(final(self).rev@, data, final(self).rev@.len(), r, to),
    {
        let ghost prev = self.rev@;
        let off = self.label() - target;
        if off > u32::MAX as usize {
            return Err(CompileError::JmpIdxOverflow);
        }
        if off <= u8::MAX as usize {
            let off = off as u8;
            let jt = if expect { off } else { 0 };
            let jf = if expect { 0 } else { off };
            self.emit(Instr::Jmp { op, src, jt, jf });
            proof { Builder::lemma_jmp(self.rev@, op, src, jt, jf); }
        } else {
            //      jmp op, src     ; take the branch that leads into the trampoline
            //      ja  target
            self.emit(Instr::Ja(off as u32));
            proof { Builder::lemma_ja(self.rev@, off as u32); }
            let ghost trampoline = self.rev@;
            let jt = if expect { 0 } else { 1 };
            let jf = if expect { 1 } else { 0 };
            self.emit(Instr::Jmp { op, src, jt, jf });
            proof {
                Builder::lemma_jmp(self.rev@, op, src, jt, jf);
                assert forall |data: &[u8], r: Regs| r.test(op, src) == expect implies
                    #[trigger] Builder::goes(self.rev@, data, self.rev@.len(), r, target as nat, r) by {
                    assert(Builder::goes(trampoline, data, trampoline.len(), r, target as nat, r));
                    Builder::lemma_goes_trans(trampoline, self.rev@, data, self.rev@.len(), r,
                        trampoline.len(), r, target as nat, r);
                }
            }
        }
        proof {
            assert forall |data: &[u8], r: Regs, to: nat|
                (r.test(op, src) == expect ==> to == target)
                && (r.test(op, src) != expect ==> Builder::lands(prev, data, prev.len(), r, to))
                && r.wf() implies #[trigger] Builder::lands(self.rev@, data, self.rev@.len(), r, to) by {
                if r.test(op, src) == expect {
                    assert(Builder::goes(self.rev@, data, self.rev@.len(), r, to, r));
                } else {
                    assert(Builder::goes(self.rev@, data, self.rev@.len(), r, prev.len(), r));
                    Builder::lemma_then(prev, self.rev@, data, self.rev@.len(), r, prev.len(), r, to, 0);
                }
            }
        }
        Ok(())
    }

    /// Puts an unconditional jump to `target` in front of the program.
    ///
    /// ```text
    ///     ja  target
    /// ```
    pub(super) fn emit_goto(&mut self, target: Label) -> (res: Result<(), CompileError>)
        requires
            0 < target <= self.rev@.len(),
            self.wf(),
        ensures
            Builder::extends(old(self).rev@, final(self).rev@),
            final(self).wf(),
            res is Ok ==> forall |data: &[u8], r: Regs|
                #[trigger] Builder::goes(final(self).rev@, data, final(self).rev@.len(), r, target as nat, r),
    {
        let off = self.label() - target;
        if off > u32::MAX as usize {
            return Err(CompileError::JmpIdxOverflow);
        }
        self.emit(Instr::Ja(off as u32));
        proof { Builder::lemma_ja(self.rev@, off as u32); }
        Ok(())
    }

    /// Puts a load of the word at `k`, masked with `mask` and flipped by `bias`, in front
    /// of the program.
    ///
    /// ```text
    ///     ld  [k]
    ///     and #mask               ; mask != 0xffffffff
    ///     xor #bias               ; bias != 0
    /// ```
    pub(super) fn emit_load(&mut self, k: u32, mask: u32, bias: u32)
        requires k % 4 == 0, self.wf()
        ensures
            Builder::extends(old(self).rev@, final(self).rev@),
            final(self).wf(),
            forall |data: &[u8], r: Regs| k + 4 <= data@.len() ==>
                #[trigger] Builder::goes(final(self).rev@, data, final(self).rev@.len(), r,
                    old(self).rev@.len(), Regs { a: (Builder::word(data, k) & mask) ^ bias, ..r }),
            forall |data: &[u8], r: Regs, to: nat| k + 4 <= data@.len()
                && Builder::lands(old(self).rev@, data, old(self).rev@.len(),
                    Regs { a: (Builder::word(data, k) & mask) ^ bias, ..r }, to)
                ==> #[trigger] Builder::lands(final(self).rev@, data, final(self).rev@.len(), r, to),
    {
        let ghost r_xor = self.rev@;
        if bias != 0 {
            self.emit(Instr::Alu(AluOp::Xor, Src::K(bias)));
            proof { Builder::lemma_alu(self.rev@, AluOp::Xor, bias); }
        }
        let ghost r_and = self.rev@;
        if mask != u32::MAX {
            self.emit(Instr::Alu(AluOp::And, Src::K(mask)));
            proof { Builder::lemma_alu(self.rev@, AluOp::And, mask); }
        }
        let ghost r_ld = self.rev@;
        self.emit(Instr::LdAbs(k));
        proof {
            Builder::lemma_ld(self.rev@, k);
            assert forall |data: &[u8], r: Regs| k + 4 <= data@.len() implies
                #[trigger] Builder::goes(self.rev@, data, self.rev@.len(), r, r_xor.len(),
                    Regs { a: (Builder::word(data, k) & mask) ^ bias, ..r }) by {
                let w = Builder::word(data, k);
                let m = w & mask;
                assert((w & u32::MAX) == w) by (bit_vector);
                assert((m ^ 0u32) == m) by (bit_vector);
                let (rw, rm, rb) = (Regs { a: w, ..r }, Regs { a: m, ..r }, Regs { a: m ^ bias, ..r });
                assert(Builder::goes(r_and, data, r_and.len(), rm, r_xor.len(), rb));
                assert(Builder::goes(r_ld, data, r_ld.len(), rw, r_and.len(), rm));
                Builder::lemma_goes_trans(r_and, r_ld, data, r_ld.len(), rw, r_and.len(), rm, r_xor.len(), rb);
                assert(Builder::goes(self.rev@, data, self.rev@.len(), r, r_ld.len(), rw));
                Builder::lemma_goes_trans(r_ld, self.rev@, data, self.rev@.len(), r, r_ld.len(), rw, r_xor.len(), rb);
            }
            assert forall |data: &[u8], r: Regs, to: nat| k + 4 <= data@.len()
                && Builder::lands(r_xor, data, r_xor.len(), Regs { a: (Builder::word(data, k) & mask) ^ bias, ..r }, to)
                implies #[trigger] Builder::lands(self.rev@, data, self.rev@.len(), r, to) by {
                let rb = Regs { a: (Builder::word(data, k) & mask) ^ bias, ..r };
                assert(Builder::goes(self.rev@, data, self.rev@.len(), r, r_xor.len(), rb));
                Builder::lemma_then(r_xor, self.rev@, data, self.rev@.len(), r, r_xor.len(), rb, to, 0);
            }
        }
    }

    /// Puts `block` in front of the program, running into what follows it.
    pub(super) fn emit_block(&mut self, block: &[Instr])
        requires
            old(self).wf(),
            0 < old(self).rev@.len(),
            Instr::fits_from(block@, 0),
        ensures
            Builder::extends(old(self).rev@, final(self).rev@),
            final(self).wf(),
            forall |data: &[u8], r: Regs| #[trigger] Instr::exec_block(block@, 0, data, r) matches Some(t)
                ==> Builder::goes(final(self).rev@, data, final(self).rev@.len(), r, old(self).rev@.len(), t),
    {
        let ghost base = self.rev@;
        proof { Instr::lemma_fits(block@, 0); }
        let mut i = block.len();
        while i > 0
            invariant
                i <= block@.len(),
                0 < base.len(),
                self.wf(),
                self.rev@.len() == base.len() + block@.len() - i,
                Builder::extends(base, self.rev@),
                forall |j: int| #![trigger block@[j]] i <= j < block@.len()
                    ==> self.rev@[base.len() + block@.len() - 1 - j] == block@[j],
                forall |j: int| #![trigger block@[j]] 0 <= j < block@.len() ==> block@[j].fits(j as nat, block@.len()),
            decreases i
        {
            i -= 1;
            proof { assert(block@[i as int].fits(i as nat, block@.len())); }
            self.emit(block[i]);
        }
        proof {
            assert forall |data: &[u8], r: Regs| #[trigger] Instr::exec_block(block@, 0, data, r) is Some
                implies Builder::goes(self.rev@, data, self.rev@.len(), r, base.len(),
                    Instr::exec_block(block@, 0, data, r)->Some_0) by {
                Builder::lemma_block(self.rev@, base.len(), block@, data, 0, r);
            }
        }
    }

    /// Reverses the buffer into a program.
    pub(super) fn finish(self) -> (res: Program)
        ensures res.instrs@ == self.rev@.reverse()
    {
        let ghost all = self.rev@;
        let mut rev = self.rev;
        let mut instrs: Vec<Instr> = Vec::new();
        while let Some(instr) = rev.pop()
            invariant
                rev@.len() <= all.len(),
                forall |j: int| #![trigger all[j]] 0 <= j < rev@.len() ==> rev@[j] == all[j],
                instrs@.len() == all.len() - rev@.len(),
                forall |j: int| #![trigger instrs@[j]]
                    0 <= j < instrs@.len() ==> instrs@[j] == all[all.len() - 1 - j],
            ensures rev@.len() == 0
            decreases rev@.len()
        {
            instrs.push(instr);
        }
        assert(instrs@ =~= all.reverse());
        Program { instrs }
    }
}

} // verus!
