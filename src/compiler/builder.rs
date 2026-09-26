//! The buffer a filter is assembled in, back to front.

use vstd::prelude::*;
use crate::spec::cbpf::*;
use super::CompileError;

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
            src is K,
            0 < target <= self.rev@.len(),
            self.wf(),
        ensures
            Builder::extends(old(self).rev@, final(self).rev@),
            final(self).wf(),
            res is Ok ==> forall |data: &[u8], a: u32| op.eval(a, src->K_0) == expect ==>
                #[trigger] Builder::goes_to(final(self).rev@, data, final(self).rev@.len(),
                    a, target as nat, a),
            res is Ok ==> forall |data: &[u8], a: u32| op.eval(a, src->K_0) != expect ==>
                #[trigger] Builder::goes_to(final(self).rev@, data, final(self).rev@.len(),
                    a, old(self).rev@.len(), a),
            res is Ok ==> forall |data: &[u8], a: u32, to: nat|
                (op.eval(a, src->K_0) == expect ==> to == target)
                && (op.eval(a, src->K_0) != expect ==>
                    Builder::lands(old(self).rev@, data, old(self).rev@.len(), a, to))
                ==> #[trigger] Builder::lands(final(self).rev@, data, final(self).rev@.len(),
                    a, to),
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
            proof { Builder::lemma_jmp(self.rev@, op, src->K_0, jt, jf); }
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
                Builder::lemma_jmp(self.rev@, op, src->K_0, jt, jf);
                assert forall |data: &[u8], a: u32| op.eval(a, src->K_0) == expect implies
                    #[trigger] Builder::goes_to(self.rev@, data, self.rev@.len(), a, target as nat, a) by {
                    Builder::lemma_then(trampoline, self.rev@, data, self.rev@.len(), a,
                        trampoline.len(), a, target as nat, a);
                }
            }
        }
        proof {
            assert forall |data: &[u8], a: u32, to: nat|
                (op.eval(a, src->K_0) == expect ==> to == target)
                && (op.eval(a, src->K_0) != expect ==> Builder::lands(prev, data, prev.len(), a, to))
                implies #[trigger] Builder::lands(self.rev@, data, self.rev@.len(), a, to) by {
                if op.eval(a, src->K_0) == expect {
                    assert(Builder::goes_to(self.rev@, data, self.rev@.len(), a, to, a));
                } else {
                    let m = choose |m: u32| Builder::goes_to(prev, data, prev.len(), a, to, m);
                    Builder::lemma_then(prev, self.rev@, data, self.rev@.len(), a,
                        prev.len(), a, to, m);
                }
            }
        }
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
            forall |data: &[u8], a: u32, to: nat| k + 4 <= data@.len()
                && Builder::lands(old(self).rev@, data, old(self).rev@.len(),
                    (Builder::word(data, k) & mask) ^ bias, to)
                ==> #[trigger] Builder::lands(final(self).rev@, data, final(self).rev@.len(),
                    a, to),
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
            assert forall |data: &[u8], a: u32, to: nat| k + 4 <= data@.len()
                && Builder::lands(r_xor, data, r_xor.len(), (Builder::word(data, k) & mask) ^ bias, to)
                implies #[trigger] Builder::lands(self.rev@, data, self.rev@.len(), a, to) by {
                let w = Builder::word(data, k);
                let m = w & mask;
                assert((w & u32::MAX) == w) by (bit_vector);
                assert((m ^ 0u32) == m) by (bit_vector);
                assert(Builder::goes_to(r_and, data, r_and.len(), m, r_xor.len(), m ^ bias));
                Builder::lemma_then(r_xor, r_and, data, r_and.len(), m, r_xor.len(), m ^ bias, to, 0);
                assert(Builder::goes_to(r_ld, data, r_ld.len(), w, r_and.len(), m));
                Builder::lemma_then(r_and, r_ld, data, r_ld.len(), w, r_and.len(), m, to, 0);
                assert(Builder::goes_to(self.rev@, data, self.rev@.len(), a, r_ld.len(), w));
                Builder::lemma_then(r_ld, self.rev@, data, self.rev@.len(), a, r_ld.len(), w, to, 0);
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
