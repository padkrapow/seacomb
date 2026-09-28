//! Compiling expressions to the 64-bit patterns of their values, one scratch pair each.

use vstd::prelude::*;
use vstd::pervasive::unreached;
use crate::spec::{policy::*, expr::*, cbpf::*};
use super::CompileError;
use super::builder::Builder;
use super::machine::Regs;

verus! {

impl Expr {
    /// The 64-bit two's complement pattern of `v`.
    pub(super) open spec fn pat(v: int) -> u64 {
        (v % 0x1_0000_0000_0000_0000) as u64
    }

    /// The pattern of this expression's value on the event `data` describes.
    pub(super) open spec fn pattern(&self, arch: Arch, ctx: Seq<PrimType>, data: &[u8]) -> u64 {
        Self::pat(self.value(arch, ctx, data))
    }
}

impl PrimType {
    /// The pattern of the value this type reads the bits `q` as.
    pub(super) open spec fn norm(self, arch: Arch, q: u64) -> u64 {
        Expr::pat(self.to_int(arch, q))
    }

    /// The mask of a type narrower than 64 bits keeps its low bits.
    proof fn lemma_mask(self, arch: Arch)
        ensures
            self.bits(arch) < 64 ==> self.mask(arch) == ((1u64 << self.bits(arch)) - 1) as u64,
            self.bits(arch) < 64 ==> self.mask(arch) as int + 1
                == vstd::arithmetic::power2::pow2(self.bits(arch) as nat),
            self.bits(arch) >= 64 ==> self.mask(arch) == u64::MAX,
    {
        if self.bits(arch) < 64 {
            vstd::bits::lemma_u64_pow2_no_overflow(self.bits(arch) as nat);
            vstd::bits::lemma_u64_shl_is_mul(1, self.bits(arch));
        }
    }

    /// [`PrimType::norm`] in bit operations: the bits within the mask, with the sign bit
    /// copied above it if the type is signed.
    pub(super) proof fn lemma_norm(self, arch: Arch, q: u64)
        ensures self.norm(arch, q) == {
            let mask = self.mask(arch);
            let p = q & mask;
            if self.signed() && p > mask >> 1u64 { p | !mask } else { p }
        }
    {
        let mask = self.mask(arch);
        let p = q & mask;
        let v = self.to_int(arch, q);
        assert(p <= mask) by (bit_vector) requires p == q & mask;
        if self.signed() && p > mask >> 1u64 {
            assert((p | !mask) == (p + !mask) as u64 && !mask == u64::MAX - mask) by (bit_vector)
                requires p == q & mask;
            assert(v + 0x1_0000_0000_0000_0000 == (p | !mask) as int);
            vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(v, 0x1_0000_0000_0000_0000);
            vstd::arithmetic::div_mod::lemma_small_mod((p | !mask) as nat, 0x1_0000_0000_0000_0000);
        } else {
            vstd::arithmetic::div_mod::lemma_small_mod(p as nat, 0x1_0000_0000_0000_0000);
        }
    }

    /// Reducing `v` to this type's bits agrees, within the mask, with its pattern.
    pub(super) proof fn lemma_to_bits(self, arch: Arch, v: int)
        ensures
            self.to_bits(arch, v) & self.mask(arch) == Expr::pat(v) & self.mask(arch),
            self.to_int(arch, self.to_bits(arch, v)) == self.to_int(arch, Expr::pat(v)),
    {
        let mask = self.mask(arch);
        let bits = self.bits(arch);
        self.lemma_mask(arch);
        if bits < 64 {
            let m = vstd::arithmetic::power2::pow2(bits as nat) as int;
            let x = self.to_bits(arch, v);
            let pv = Expr::pat(v);
            vstd::arithmetic::power2::lemma_pow2_pos(bits as nat);
            vstd::arithmetic::power2::lemma_pow2_adds(bits as nat, (64 - bits) as nat);
            vstd::arithmetic::power2::lemma2_to64();
            vstd::arithmetic::power2::lemma_pow2_pos((64 - bits) as nat);
            vstd::bits::lemma_u64_low_bits_mask_is_mod(x, bits as nat);
            vstd::bits::lemma_u64_low_bits_mask_is_mod(pv, bits as nat);
            vstd::arithmetic::div_mod::lemma_mod_mod(v, m, vstd::arithmetic::power2::pow2((64 - bits) as nat) as int);
            vstd::arithmetic::div_mod::lemma_mod_bound(v, m);
            vstd::arithmetic::div_mod::lemma_small_mod(x as nat, m as nat);
            assert(x & mask == x % (m as u64));
            assert(pv & mask == pv % (m as u64));
        }
        let x = self.to_bits(arch, v);
        let pv = Expr::pat(v);
        assert((x & mask) & mask == x & mask && (pv & mask) & mask == pv & mask) by (bit_vector);
    }

    /// The pattern of `v` converted to this type is the one it reads `v`'s pattern as.
    pub(super) proof fn lemma_norm_trunc(self, arch: Arch, v: int)
        ensures Expr::pat(self.trunc(arch, v)) == self.norm(arch, Expr::pat(v))
    {
        self.lemma_to_bits(arch, v);
    }

    /// Types of one width and signedness read bits alike.
    pub(super) proof fn lemma_same(self, other: PrimType, arch: Arch)
        requires self.bits(arch) == other.bits(arch), self.signed() == other.signed()
        ensures
            self.mask(arch) == other.mask(arch),
            forall |x: u64| #[trigger] self.to_int(arch, x) == other.to_int(arch, x),
            forall |v: int| #[trigger] self.trunc(arch, v) == other.trunc(arch, v),
            forall |x: u64| #[trigger] self.norm(arch, x) == other.norm(arch, x),
    {
    }

    /// Executable version of [`PrimType::norm`].
    pub(super) fn exec_norm(self, arch: Arch, q: u64) -> (res: u64)
        ensures res == self.norm(arch, q)
    {
        let mask = self.exec_mask(arch);
        let p = q & mask;
        proof { self.lemma_norm(arch, q); }
        if self.exec_signed() && p > mask >> 1 { p | !mask } else { p }
    }

    /// Normalizing bits in the lower word of a type narrower than 32 bits.
    proof fn lemma_norm_narrow(q: u64, m: u64, b: u64, s: bool)
        requires 0 < b < 32, m == ((1u64 << b) - 1) as u64
        ensures ({
            let p = q & m;
            let n = if s && p > m >> 1u64 { p | !m } else { p };
            let m0 = m as u32;
            let s0 = ((m >> 1u64) + 1) as u32;
            let lo = if s { (((q as u32 & m0) ^ s0) - s0) as u32 } else { q as u32 & m0 };
            &&& n as u32 == lo
            &&& (n >> 32u64) as u32 == if s { (-((lo >> 31u32) as int)) as u32 } else { 0 }
        })
    {
        let p = q & m;
        let m0 = m as u32;
        let s0 = ((m >> 1u64) + 1) as u32;
        let w = q as u32;
        let lo = (((w & m0) ^ s0) - s0) as u32;
        let n = if s && p > m >> 1u64 { p | !m } else { p };
        if s && p > m >> 1u64 {
            assert((p | !m) as u32 == lo && ((p | !m) >> 32u64) as u32 == (-((lo >> 31u32) as int)) as u32)
                by (bit_vector)
                requires 0 < b < 32, m == ((1u64 << b) - 1) as u64, p == q & m, p > m >> 1u64,
                    m0 == m as u32, s0 == ((m >> 1u64) + 1) as u32, w == q as u32,
                    lo == (((w & m0) ^ s0) - s0) as u32;
        } else if s {
            assert(p as u32 == lo && (p >> 32u64) as u32 == (-((lo >> 31u32) as int)) as u32) by (bit_vector)
                requires 0 < b < 32, m == ((1u64 << b) - 1) as u64, p == q & m, p <= m >> 1u64,
                    m0 == m as u32, s0 == ((m >> 1u64) + 1) as u32, w == q as u32,
                    lo == (((w & m0) ^ s0) - s0) as u32;
        } else {
            assert(p as u32 == w & m0 && (p >> 32u64) as u32 == 0) by (bit_vector)
                requires 0 < b < 32, m == ((1u64 << b) - 1) as u64, p == q & m, m0 == m as u32,
                    w == q as u32;
        }
    }

    /// Normalizing bits of a type exactly 32 bits wide.
    proof fn lemma_norm_word(q: u64, s: bool)
        ensures ({
            let m = 0xFFFF_FFFFu64;
            let p = q & m;
            let n = if s && p > m >> 1u64 { p | !m } else { p };
            &&& n as u32 == q as u32
            &&& (n >> 32u64) as u32 == if s { (-(((q as u32) >> 31u32) as int)) as u32 } else { 0 }
        })
    {
        let m = 0xFFFF_FFFFu64;
        let p = q & m;
        let w = q as u32;
        if s && p > m >> 1u64 {
            assert((p | !m) as u32 == w && ((p | !m) >> 32u64) as u32 == (-((w >> 31u32) as int)) as u32)
                by (bit_vector)
                requires m == 0xFFFF_FFFFu64, p == q & m, p > m >> 1u64, w == q as u32;
        } else {
            assert(p as u32 == w && (p >> 32u64) as u32 == 0) by (bit_vector)
                requires m == 0xFFFF_FFFFu64, p == q & m, w == q as u32;
            if s {
                assert((-((w >> 31u32) as int)) as u32 == 0) by (bit_vector)
                    requires m == 0xFFFF_FFFFu64, p == q & m, p <= m >> 1u64, w == q as u32;
            }
        }
    }
}

impl Regs {
    /// Whether scratch pair `slot` holds the pattern `p`, low word first.
    pub(super) open spec fn holds(self, slot: nat, p: u64) -> bool {
        &&& self.mem[2 * slot as int] == Some(p as u32)
        &&& self.mem[2 * slot as int + 1] == Some((p >> 32) as u32)
    }

    /// Whether the scratch words below `n` are those of `r`.
    pub(super) open spec fn keeps(self, r: Regs, n: nat) -> bool {
        forall |k: int| 0 <= k < n ==> #[trigger] self.mem[k] == r.mem[k]
    }
}

impl Builder {
    /// Whether every extension of `rev`, entered at `from` with registers `r`, carries on
    /// at `to` with scratch pair `slot` holding `p`, and the words below it as `r` has them.
    pub(super) open spec fn stores(rev: Seq<Instr>, data: &[u8], from: nat, r: Regs, to: nat, slot: nat, p: u64) -> bool {
        exists |t: Regs| t.wf() && t.holds(slot, p) && t.keeps(r, 2 * slot)
            && #[trigger] Self::goes(rev, data, from, r, to, t)
    }

    /// A stretch that stores into a pair followed by one that stores into a pair no
    /// higher stores into the second pair.
    pub(super) proof fn lemma_stores_then(rev: Seq<Instr>, ext: Seq<Instr>, data: &[u8], from: nat, r: Regs, mid: nat, m: Regs, n: nat, to: nat, slot: nat, p: u64)
        requires
            Self::extends(rev, ext),
            Self::goes(ext, data, from, r, mid, m),
            m.keeps(r, n),
            2 * slot <= n,
            Self::stores(rev, data, mid, m, to, slot, p),
        ensures Self::stores(ext, data, from, r, to, slot, p)
    {
        let t = choose |t: Regs| t.wf() && t.holds(slot, p) && t.keeps(m, 2 * slot)
            && #[trigger] Self::goes(rev, data, mid, m, to, t);
        Self::lemma_goes_trans(rev, ext, data, from, r, mid, m, to, t);
        assert(t.keeps(r, 2 * slot));
    }
}

impl PrimType {
    /// Emits code that replaces the bits in scratch pair `slot` with the pattern of the
    /// value this type reads them as.
    ///
    /// ```text
    ///     ld  M[lo]               ; bits < 32, or signed
    ///     and #mask               ; bits < 32
    ///     xor #sign               ; bits < 32, signed only
    ///     sub #sign               ; bits < 32, signed only
    ///     st  M[lo]               ; bits < 32
    ///     rsh #31                 ; signed, or ld #0 if unsigned
    ///     neg                     ; signed only
    ///     st  M[hi]
    ///
    ///                             ; bits == 64 emits nothing
    /// ```
    pub(super) fn emit_norm(self, b: &mut Builder, arch: Arch, slot: u32)
        requires self.wf(), old(b).wf(), 0 < old(b).rev@.len(), slot < 8
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            forall |data: &[u8], r: Regs, q: u64| r.wf() && r.mem[2 * slot as int] == Some(q as u32)
                && (self.bits(arch) > 32 ==> r.mem[2 * slot + 1] == Some((q >> 32) as u32))
                ==> #[trigger] Builder::stores(final(b).rev@, data, final(b).rev@.len(), r,
                    old(b).rev@.len(), slot as nat, self.norm(arch, q)),
    {
        let ghost base = b.rev@;
        let bits = self.exec_bits(arch);
        let signed = self.exec_signed();
        let mask = self.exec_mask(arch);
        let lo = 2 * slot;
        let hi = 2 * slot + 1;
        proof { self.lemma_mask(arch); }
        if bits >= 64 {
            proof {
                assert forall |data: &[u8], r: Regs, q: u64| r.wf() && r.mem[2 * slot as int] == Some(q as u32)
                    && (self.bits(arch) > 32 ==> r.mem[2 * slot + 1] == Some((q >> 32) as u32))
                    implies #[trigger] Builder::stores(b.rev@, data, b.rev@.len(), r, base.len(), slot as nat,
                        self.norm(arch, q)) by {
                    self.lemma_norm(arch, q);
                    assert(q & u64::MAX == q && q | !u64::MAX == q) by (bit_vector);
                    assert(Builder::goes(b.rev@, data, b.rev@.len(), r, base.len(), r));
                }
            }
            return;
        }
        if bits == 32 {
            if signed {
                let block = [Instr::LdMem(lo), Instr::Alu(AluOp::Rsh, Src::K(31)), Instr::Neg, Instr::St(hi)];
                proof { reveal_with_fuel(Instr::fits_from, 5); }
                b.emit_block(&block);
                proof { self.lemma_norm_block(b.rev@, base, arch, slot); }
            } else {
                let block = [Instr::LdImm(0), Instr::St(hi)];
                proof { reveal_with_fuel(Instr::fits_from, 3); }
                b.emit_block(&block);
                proof { self.lemma_norm_block(b.rev@, base, arch, slot); }
            }
        } else {
            let m0 = mask as u32;
            proof { assert(mask >> 1u64 < u64::MAX) by (bit_vector); }
            let s0 = ((mask >> 1) + 1) as u32;
            if signed {
                let block = [Instr::LdMem(lo), Instr::Alu(AluOp::And, Src::K(m0)),
                    Instr::Alu(AluOp::Xor, Src::K(s0)), Instr::Alu(AluOp::Sub, Src::K(s0)), Instr::St(lo),
                    Instr::Alu(AluOp::Rsh, Src::K(31)), Instr::Neg, Instr::St(hi)];
                proof { reveal_with_fuel(Instr::fits_from, 9); }
                b.emit_block(&block);
                proof { self.lemma_norm_block(b.rev@, base, arch, slot); }
            } else {
                let block = [Instr::LdMem(lo), Instr::Alu(AluOp::And, Src::K(m0)), Instr::St(lo),
                    Instr::LdImm(0), Instr::St(hi)];
                proof { reveal_with_fuel(Instr::fits_from, 6); }
                b.emit_block(&block);
                proof { self.lemma_norm_block(b.rev@, base, arch, slot); }
            }
        }
    }

    /// The instructions [`PrimType::emit_norm`] emits for this type and scratch pair `slot`.
    pub(super) open spec fn norm_block(self, arch: Arch, slot: u32) -> Seq<Instr> {
        let lo = (2 * slot) as u32;
        let hi = (2 * slot + 1) as u32;
        let mask = self.mask(arch);
        if self.bits(arch) == 32 {
            if self.signed() {
                seq![Instr::LdMem(lo), Instr::Alu(AluOp::Rsh, Src::K(31)), Instr::Neg, Instr::St(hi)]
            } else {
                seq![Instr::LdImm(0), Instr::St(hi)]
            }
        } else {
            let m0 = mask as u32;
            let s0 = ((mask >> 1u64) + 1) as u32;
            if self.signed() {
                seq![Instr::LdMem(lo), Instr::Alu(AluOp::And, Src::K(m0)),
                    Instr::Alu(AluOp::Xor, Src::K(s0)), Instr::Alu(AluOp::Sub, Src::K(s0)), Instr::St(lo),
                    Instr::Alu(AluOp::Rsh, Src::K(31)), Instr::Neg, Instr::St(hi)]
            } else {
                seq![Instr::LdMem(lo), Instr::Alu(AluOp::And, Src::K(m0)), Instr::St(lo),
                    Instr::LdImm(0), Instr::St(hi)]
            }
        }
    }

    /// The block [`PrimType::emit_norm`] emits for this type normalizes the pair it works on.
    proof fn lemma_norm_block(self, rev: Seq<Instr>, base: Seq<Instr>, arch: Arch, slot: u32)
        requires
            slot < 8,
            self.wf(),
            self.bits(arch) < 64,
            forall |data: &[u8], r: Regs| #[trigger] Instr::exec_block(self.norm_block(arch, slot), 0, data, r)
                matches Some(t) ==> Builder::goes(rev, data, rev.len(), r, base.len(), t),
        ensures
            forall |data: &[u8], r: Regs, q: u64| r.wf() && r.mem[2 * slot as int] == Some(q as u32)
                && (self.bits(arch) > 32 ==> r.mem[2 * slot + 1] == Some((q >> 32) as u32))
                ==> #[trigger] Builder::stores(rev, data, rev.len(), r, base.len(), slot as nat, self.norm(arch, q)),
    {
        assert forall |data: &[u8], r: Regs, q: u64| r.wf() && r.mem[2 * slot as int] == Some(q as u32)
            && (self.bits(arch) > 32 ==> r.mem[2 * slot + 1] == Some((q >> 32) as u32))
            implies #[trigger] Builder::stores(rev, data, rev.len(), r, base.len(), slot as nat, self.norm(arch, q)) by {
            let t = if self.bits(arch) == 32 {
                self.lemma_norm_run_word(arch, slot, data, r, q)
            } else {
                self.lemma_norm_run_narrow(arch, slot, data, r, q)
            };
            assert(Builder::goes(rev, data, rev.len(), r, base.len(), t));
        }
    }

    /// Running the block [`PrimType::emit_norm`] emits for a type exactly 32 bits wide
    /// normalizes the pair it works on.
    proof fn lemma_norm_run_word(self, arch: Arch, slot: u32, data: &[u8], r: Regs, q: u64) -> (t: Regs)
        requires
            slot < 8,
            self.bits(arch) == 32,
            r.wf(),
            r.mem[2 * slot as int] == Some(q as u32),
        ensures
            Instr::exec_block(self.norm_block(arch, slot), 0, data, r) == Some(t),
            t.wf(),
            t.holds(slot as nat, self.norm(arch, q)),
            t.keeps(r, 2 * slot as nat),
    {
        self.lemma_mask(arch);
        self.lemma_norm(arch, q);
        assert(((1u64 << 32u64) - 1) as u64 == 0xFFFF_FFFFu64) by (bit_vector);
        Self::lemma_norm_word(q, self.signed());
        reveal_with_fuel(Instr::exec_block, 5);
        Instr::exec_block(self.norm_block(arch, slot), 0, data, r)->Some_0
    }

    /// Running the block [`PrimType::emit_norm`] emits for a type narrower than 32 bits
    /// normalizes the pair it works on.
    proof fn lemma_norm_run_narrow(self, arch: Arch, slot: u32, data: &[u8], r: Regs, q: u64) -> (t: Regs)
        requires
            slot < 8,
            0 < self.bits(arch) < 32,
            r.wf(),
            r.mem[2 * slot as int] == Some(q as u32),
        ensures
            Instr::exec_block(self.norm_block(arch, slot), 0, data, r) == Some(t),
            t.wf(),
            t.holds(slot as nat, self.norm(arch, q)),
            t.keeps(r, 2 * slot as nat),
    {
        self.lemma_mask(arch);
        self.lemma_norm(arch, q);
        Self::lemma_norm_narrow(q, self.mask(arch), self.bits(arch), self.signed());
        reveal_with_fuel(Instr::exec_block, 9);
        Instr::exec_block(self.norm_block(arch, slot), 0, data, r)->Some_0
    }
}

impl Expr {
    /// Whether this expression has a type.
    pub(super) open spec fn typed(&self, arch: Arch, ctx: Seq<PrimType>) -> bool {
        exists |t: PrimType| self.of_type(arch, ctx, t)
    }

    /// Whether every type of this expression has the width, signedness, and pointerness
    /// of `ty`.
    pub(super) open spec fn shaped(&self, arch: Arch, ctx: Seq<PrimType>, ty: PrimType) -> bool {
        forall |t: PrimType| #[trigger] self.of_type(arch, ctx, t) ==> {
            &&& t.bits(arch) == ty.bits(arch)
            &&& t.signed() == ty.signed()
            &&& (t == PrimType::Ptr) == (ty == PrimType::Ptr)
        }
    }

    /// Whether this expression has one of the types [`PrimType::wf`] allows.
    spec fn listed(&self, arch: Arch, ctx: Seq<PrimType>) -> bool {
        ||| self.of_type(arch, ctx, PrimType::I(8)) ||| self.of_type(arch, ctx, PrimType::I(16))
        ||| self.of_type(arch, ctx, PrimType::I(32)) ||| self.of_type(arch, ctx, PrimType::I(64))
        ||| self.of_type(arch, ctx, PrimType::U(8)) ||| self.of_type(arch, ctx, PrimType::U(16))
        ||| self.of_type(arch, ctx, PrimType::U(32)) ||| self.of_type(arch, ctx, PrimType::U(64))
        ||| self.of_type(arch, ctx, PrimType::IWord) ||| self.of_type(arch, ctx, PrimType::UWord)
        ||| self.of_type(arch, ctx, PrimType::Ptr)
    }

    /// The operands of a typed expression are typed.
    pub(super) proof fn lemma_operands_typed(&self, arch: Arch, ctx: Seq<PrimType>)
        requires self.typed(arch, ctx)
        ensures
            self matches Expr::Cast(e, _) ==> e.typed(arch, ctx),
            self matches Expr::BinOp(_, l, r) ==> l.typed(arch, ctx) && r.typed(arch, ctx),
    {
        // The operands' types sit under an `exists` over the fueled recursive call, which
        // no term of `of_type` at the default fuel matches. A second unfolding reveals that
        // they are well-formed, and listing the well-formed types supplies the terms.
        reveal_with_fuel(Expr::of_type, 2);
        match self {
            Expr::Cast(e, _) => assert(e.listed(arch, ctx)),
            Expr::BinOp(_, l, r) => assert(l.listed(arch, ctx) && r.listed(arch, ctx)),
            _ => {}
        }
    }

    /// Returns a type of the width, signedness, and pointerness every type of this
    /// expression has.
    pub(super) fn ty(&self, arch: Arch, sig: &[PrimType]) -> (res: PrimType)
        requires self.typed(arch, sig@)
        ensures res.wf(), self.shaped(arch, sig@, res)
        decreases self
    {
        proof { self.lemma_operands_typed(arch, sig@); }
        match self {
            Expr::Var(i) => sig[*i as usize],
            Expr::Lit(_, t) | Expr::Cast(_, t) => *t,
            Expr::BinOp(op, l, r) => {
                let t1 = l.ty(arch, sig);
                let t2 = r.ty(arch, sig);
                let res = if matches!(op, BinOp::Add | BinOp::Sub) && t1.exec_subtype_of(arch, t2) { t2 } else { t1 };
                proof {
                    assert forall |t: PrimType| #[trigger] self.of_type(arch, sig@, t) implies {
                        &&& t.bits(arch) == res.bits(arch)
                        &&& t.signed() == res.signed()
                        &&& (t == PrimType::Ptr) == (res == PrimType::Ptr)
                    } by {
                        if *op is Add || *op is Sub {
                            self.lemma_operands(arch, sig@, t);
                        } else {
                            assert(l.of_type(arch, sig@, t));
                            assert(r.of_type(arch, sig@, t));
                        }
                    }
                }
                res
            }
        }
    }

    /// The number of nodes in this expression.
    pub(super) open spec fn size(self) -> nat
        decreases self
    {
        match self {
            Expr::Var(_) | Expr::Lit(..) => 1,
            Expr::Cast(e, _) => 1 + e.size(),
            Expr::BinOp(_, l, r) => 1 + l.size() + r.size(),
        }
    }

    /// Emits code that computes the pattern of this expression's value into scratch pair
    /// `slot`, and leaves the pairs below it alone.
    pub(super) fn emit_value(&self, b: &mut Builder, arch: Arch, sig: &[PrimType], slot: u32)
        -> (res: Result<(), CompileError>)
        requires old(b).wf(), 0 < old(b).rev@.len(), slot < 8, self.typed(arch, sig@)
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf() ==>
                #[trigger] Builder::stores(final(b).rev@, data, final(b).rev@.len(), r,
                    old(b).rev@.len(), slot as nat, self.pattern(arch, sig@, data)),
        decreases self.size(), 2nat
    {
        match self {
            Expr::Var(_) => self.emit_var(b, arch, sig, slot),
            Expr::Lit(..) => self.emit_lit(b, arch, sig, slot),
            Expr::Cast(..) => self.emit_cast(b, arch, sig, slot),
            Expr::BinOp(..) => self.emit_binary(b, arch, sig, slot),
        }
    }

    /// [`Expr::emit_value`] for an argument.
    ///
    /// ```text
    ///     ld  [lo]
    ///     st  M[lo]
    ///     ld  [hi]                ; bits > 32
    ///     st  M[hi]               ; bits > 32
    ///     <normalize>
    /// ```
    fn emit_var(&self, b: &mut Builder, arch: Arch, sig: &[PrimType], slot: u32) -> (res: Result<(), CompileError>)
        requires old(b).wf(), 0 < old(b).rev@.len(), slot < 8, self is Var, self.typed(arch, sig@)
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf() ==>
                #[trigger] Builder::stores(final(b).rev@, data, final(b).rev@.len(), r,
                    old(b).rev@.len(), slot as nat, self.pattern(arch, sig@, data)),
    {
        let i = match self {
            Expr::Var(i) => *i as usize,
            _ => unreached(),
        };
        let ty = sig[i];
        let at = arch.arg_slot(sig, i)?;
        let lo = Policy::OFFSET_EVENT_ARGS + 8 * at;
        let hi = if arch.exec_splits(ty) { lo + 8 } else { lo + 4 };
        let ghost base = b.rev@;
        ty.emit_norm(b, arch, slot);
        let ghost r_norm = b.rev@;
        let ghost facts = |data: &[u8]| {
            let ev = Event::of(data);
            let raw = arch.raw(ev.args, ty, at as nat);
            &&& self.pattern(arch, sig@, data) == ty.norm(arch, raw)
            &&& Builder::word(data, lo) == raw as u32
            &&& Builder::word(data, hi) == (raw >> 32) as u32
            &&& hi + 4 <= data@.len()
        };
        proof {
            assert forall |data: &[u8]| Event::parse(data) is Some implies #[trigger] facts(data) by {
                let ev = Event::of(data);
                Event::lemma_image(data);
                let raw = arch.raw(ev.args, ty, at as nat);
                assert(arch.interp_args(ev.args, sig@)[i as int] == raw);
                arch.lemma_raw_words(ev.args, ty, at as nat);
                let lv = ev.args[at as int];
                assert((lv & 0xFFFF_FFFF) as u32 == lv as u32) by (bit_vector);
                assert(Builder::word(data, (Policy::OFFSET_EVENT_ARGS + 8 * at) as u32)
                    == (ev.args[at as int] & 0xFFFF_FFFF) as u32);
                if arch.splits(ty) {
                    let hv = ev.args[at + 1 as int];
                    assert((hv & 0xFFFF_FFFF) as u32 == hv as u32) by (bit_vector);
                    assert(Builder::word(data, (Policy::OFFSET_EVENT_ARGS + 8 * (at + 1)) as u32)
                        == (ev.args[at + 1 as int] & 0xFFFF_FFFF) as u32);
                } else {
                    assert(Builder::word(data, (Policy::OFFSET_EVENT_ARGS + 8 * at + 4) as u32)
                        == (ev.args[at as int] >> 32) as u32);
                }
            }
        }
        if ty.exec_bits(arch) > 32 {
            let block = [Instr::LdAbs(lo), Instr::St(2 * slot), Instr::LdAbs(hi), Instr::St(2 * slot + 1)];
            proof { reveal_with_fuel(Instr::fits_from, 5); }
            b.emit_block(&block);
            proof {
                assert forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf() implies
                    #[trigger] Builder::stores(b.rev@, data, b.rev@.len(), r, base.len(), slot as nat,
                        self.pattern(arch, sig@, data)) by {
                    assert(facts(data));
                    let raw = arch.raw(Event::of(data).args, ty, at as nat);
                    reveal_with_fuel(Instr::exec_block, 5);
                    let t = Instr::exec_block(block@, 0, data, r)->Some_0;
                    assert(t.keeps(r, 2 * slot as nat));
                    assert(Builder::stores(r_norm, data, r_norm.len(), t, base.len(), slot as nat, ty.norm(arch, raw)));
                    Builder::lemma_stores_then(r_norm, b.rev@, data, b.rev@.len(), r, r_norm.len(), t,
                        2 * slot as nat, base.len(), slot as nat, ty.norm(arch, raw));
                }
            }
        } else {
            let block = [Instr::LdAbs(lo), Instr::St(2 * slot)];
            proof { reveal_with_fuel(Instr::fits_from, 3); }
            b.emit_block(&block);
            proof {
                assert forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf() implies
                    #[trigger] Builder::stores(b.rev@, data, b.rev@.len(), r, base.len(), slot as nat,
                        self.pattern(arch, sig@, data)) by {
                    assert(facts(data));
                    let raw = arch.raw(Event::of(data).args, ty, at as nat);
                    reveal_with_fuel(Instr::exec_block, 3);
                    let t = Instr::exec_block(block@, 0, data, r)->Some_0;
                    assert(t.keeps(r, 2 * slot as nat));
                    assert(Builder::stores(r_norm, data, r_norm.len(), t, base.len(), slot as nat, ty.norm(arch, raw)));
                    Builder::lemma_stores_then(r_norm, b.rev@, data, b.rev@.len(), r, r_norm.len(), t,
                        2 * slot as nat, base.len(), slot as nat, ty.norm(arch, raw));
                }
            }
        }
        Ok(())
    }

    /// [`Expr::emit_value`] for a literal.
    ///
    /// ```text
    ///     ld  #lo
    ///     st  M[lo]
    ///     ld  #hi
    ///     st  M[hi]
    /// ```
    #[allow(unused_variables)]
    fn emit_lit(&self, b: &mut Builder, arch: Arch, sig: &[PrimType], slot: u32) -> (res: Result<(), CompileError>)
        requires old(b).wf(), 0 < old(b).rev@.len(), slot < 8, self is Lit
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf() ==>
                #[trigger] Builder::stores(final(b).rev@, data, final(b).rev@.len(), r,
                    old(b).rev@.len(), slot as nat, self.pattern(arch, sig@, data)),
    {
        let (c, ty) = match self {
            Expr::Lit(c, ty) => (*c, *ty),
            _ => unreached(),
        };
        // The 64-bit two's complement word of `c`.
        let q = if c >= 0 { c as u64 } else { u64::MAX - (-(c + 1)) as u64 };
        let n = ty.exec_norm(arch, q);
        let ghost base = b.rev@;
        let block = [Instr::LdImm(n as u32), Instr::St(2 * slot), Instr::LdImm((n >> 32) as u32), Instr::St(2 * slot + 1)];
        proof { reveal_with_fuel(Instr::fits_from, 5); }
        b.emit_block(&block);
        proof {
            assert(q == Expr::pat(c as int)) by {
                if c < 0 {
                    vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(c as int, 0x1_0000_0000_0000_0000);
                }
                vstd::arithmetic::div_mod::lemma_small_mod(q as nat, 0x1_0000_0000_0000_0000);
            }
            ty.lemma_norm_trunc(arch, c as int);
            assert forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf() implies
                #[trigger] Builder::stores(b.rev@, data, b.rev@.len(), r, base.len(), slot as nat,
                    self.pattern(arch, sig@, data)) by {
                reveal_with_fuel(Instr::exec_block, 5);
                let t = Instr::exec_block(block@, 0, data, r)->Some_0;
                assert(t.keeps(r, 2 * slot as nat));
                assert(t.holds(slot as nat, n));
                assert(Builder::goes(b.rev@, data, b.rev@.len(), r, base.len(), t));
            }
        }
        Ok(())
    }

    /// [`Expr::emit_value`] for a conversion.
    ///
    /// ```text
    ///     <operand>
    ///     <normalize>
    /// ```
    fn emit_cast(&self, b: &mut Builder, arch: Arch, sig: &[PrimType], slot: u32)
        -> (res: Result<(), CompileError>)
        requires old(b).wf(), 0 < old(b).rev@.len(), slot < 8, self is Cast, self.typed(arch, sig@)
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf() ==>
                #[trigger] Builder::stores(final(b).rev@, data, final(b).rev@.len(), r,
                    old(b).rev@.len(), slot as nat, self.pattern(arch, sig@, data)),
        decreases self.size(), 1nat
    {
        let (e, ty) = match self {
            Expr::Cast(e, ty) => (e, *ty),
            _ => unreached(),
        };
        proof { self.lemma_operands_typed(arch, sig@); }
        let ghost base = b.rev@;
        ty.emit_norm(b, arch, slot);
        let ghost r_norm = b.rev@;
        e.emit_value(b, arch, sig, slot)?;
        proof {
            assert forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf() implies
                #[trigger] Builder::stores(b.rev@, data, b.rev@.len(), r, base.len(), slot as nat,
                    self.pattern(arch, sig@, data)) by {
                let pe = e.pattern(arch, sig@, data);
                ty.lemma_norm_trunc(arch, e.value(arch, sig@, data));
                assert(Builder::stores(b.rev@, data, b.rev@.len(), r, r_norm.len(), slot as nat, pe));
                let t = choose |t: Regs| t.wf() && t.holds(slot as nat, pe) && t.keeps(r, 2 * slot as nat)
                    && #[trigger] Builder::goes(b.rev@, data, b.rev@.len(), r, r_norm.len(), t);
                assert(Builder::stores(r_norm, data, r_norm.len(), t, base.len(), slot as nat, ty.norm(arch, pe)));
                Builder::lemma_stores_then(r_norm, b.rev@, data, b.rev@.len(), r, r_norm.len(), t,
                    2 * slot as nat, base.len(), slot as nat, ty.norm(arch, pe));
            }
        }
        Ok(())
    }

    /// [`Expr::emit_value`] for a binary operation.
    ///
    /// ```text
    ///     <operand computed first>
    ///     <operand computed second>
    ///     <combination>
    /// ```
    fn emit_binary(&self, b: &mut Builder, arch: Arch, sig: &[PrimType], slot: u32)
        -> (res: Result<(), CompileError>)
        requires old(b).wf(), 0 < old(b).rev@.len(), slot < 8, self is BinOp, self.typed(arch, sig@)
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf() ==>
                #[trigger] Builder::stores(final(b).rev@, data, final(b).rev@.len(), r,
                    old(b).rev@.len(), slot as nat, self.pattern(arch, sig@, data)),
        decreases self.size(), 1nat
    {
        if slot + 1 >= 8 {
            return Err(CompileError::ScratchOverflow);
        }
        let (op, l, r) = match self {
            Expr::BinOp(op, l, r) => (*op, l, r),
            _ => unreached(),
        };
        let ty = self.ty(arch, sig);
        proof { self.lemma_operands_typed(arch, sig@); }
        // The operand that needs more scratch pairs goes first, into `slot`.
        let (ls, rs) = if l.pairs() >= r.pairs() { (slot, slot + 1) } else { (slot + 1, slot) };
        let ghost base = b.rev@;
        op.emit_pairs(b, arch, ty, ls, rs, slot);
        let ghost mid = b.rev@;
        l.emit_operands(r, b, arch, sig, slot, ls, rs)?;
        proof {
            assert forall |data: &[u8], r0: Regs| Event::parse(data) is Some && r0.wf() implies
                #[trigger] Builder::stores(b.rev@, data, b.rev@.len(), r0, base.len(), slot as nat,
                    self.pattern(arch, sig@, data)) by {
                let pl = l.pattern(arch, sig@, data);
                let pr = r.pattern(arch, sig@, data);
                self.lemma_binary_pattern(arch, sig@, data, ty);
                assert(Builder::stores2(b.rev@, data, b.rev@.len(), r0, mid.len(), slot as nat, ls as nat, pl, rs as nat, pr));
                assert forall |t: Regs| t.wf() && t.holds(ls as nat, pl) && t.holds(rs as nat, pr) implies
                    #[trigger] Builder::stores(mid, data, mid.len(), t, base.len(), slot as nat,
                        self.pattern(arch, sig@, data)) by {
                    assert(Builder::stores(mid, data, mid.len(), t, base.len(), slot as nat, ty.norm(arch, op.apply(pl, pr))));
                }
                Builder::lemma_combine(mid, b.rev@, data, b.rev@.len(), r0, mid.len(), slot as nat,
                    ls as nat, pl, rs as nat, pr, base.len(), self.pattern(arch, sig@, data));
            }
        }
        Ok(())
    }

    /// Returns how many scratch pairs computing this expression takes, given that the
    /// operand needing more of them goes first.
    pub(super) fn pairs(&self) -> u32
        decreases self
    {
        match self {
            Expr::Var(_) | Expr::Lit(..) => 1,
            Expr::Cast(e, _) => e.pairs(),
            Expr::BinOp(_, l, r) => {
                let p = l.pairs();
                let q = r.pairs();
                if p == q {
                    if p < u32::MAX { p + 1 } else { p }
                } else if p > q {
                    p
                } else {
                    q
                }
            }
        }
    }

    /// Emits code that computes this expression and `other` into scratch pairs `ls` and
    /// `rs`, which are `slot` and `slot + 1` in some order, and leaves the pairs below
    /// `slot` alone.
    #[allow(unused_variables, clippy::too_many_arguments)]
    pub(super) fn emit_operands(&self, other: &Expr, b: &mut Builder, arch: Arch, sig: &[PrimType], slot: u32,
        ls: u32, rs: u32) -> (res: Result<(), CompileError>)
        requires
            old(b).wf(), 0 < old(b).rev@.len(), slot + 1 < 8,
            self.typed(arch, sig@), other.typed(arch, sig@),
            ls == slot && rs == slot + 1 || ls == slot + 1 && rs == slot,
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], r: Regs| Event::parse(data) is Some && r.wf() ==>
                #[trigger] Builder::stores2(final(b).rev@, data, final(b).rev@.len(), r, old(b).rev@.len(),
                    slot as nat, ls as nat, self.pattern(arch, sig@, data), rs as nat, other.pattern(arch, sig@, data)),
        decreases self.size() + other.size(), 0nat
    {
        let (first, second) = if ls == slot { (self, other) } else { (other, self) };
        let ghost base = b.rev@;
        second.emit_value(b, arch, sig, slot + 1)?;
        let ghost mid = b.rev@;
        first.emit_value(b, arch, sig, slot)?;
        proof {
            assert forall |data: &[u8], r0: Regs| Event::parse(data) is Some && r0.wf() implies
                #[trigger] Builder::stores2(b.rev@, data, b.rev@.len(), r0, base.len(), slot as nat,
                    ls as nat, self.pattern(arch, sig@, data), rs as nat, other.pattern(arch, sig@, data)) by {
                let pf = first.pattern(arch, sig@, data);
                let ps = second.pattern(arch, sig@, data);
                assert(Builder::stores(b.rev@, data, b.rev@.len(), r0, mid.len(), slot as nat, pf));
                let t1 = choose |t: Regs| t.wf() && t.holds(slot as nat, pf) && t.keeps(r0, 2 * slot as nat)
                    && #[trigger] Builder::goes(b.rev@, data, b.rev@.len(), r0, mid.len(), t);
                assert(Builder::stores(mid, data, mid.len(), t1, base.len(), (slot + 1) as nat, ps));
                let t2 = choose |t: Regs| t.wf() && t.holds((slot + 1) as nat, ps) && t.keeps(t1, 2 * (slot + 1) as nat)
                    && #[trigger] Builder::goes(mid, data, mid.len(), t1, base.len(), t);
                Builder::lemma_goes_trans(mid, b.rev@, data, b.rev@.len(), r0, mid.len(), t1, base.len(), t2);
                assert(t2.holds(slot as nat, pf));
                assert(t2.keeps(r0, 2 * slot as nat));
            }
        }
        Ok(())
    }
}

impl Builder {
    /// Whether every extension of `rev`, entered at `from` with registers `r`, carries on
    /// at `to` with scratch pairs `ls` and `rs` holding `pl` and `pr`, and the words below
    /// pair `below` as `r` has them.
    pub(super) open spec fn stores2(rev: Seq<Instr>, data: &[u8], from: nat, r: Regs, to: nat, below: nat, ls: nat, pl: u64, rs: nat, pr: u64) -> bool {
        exists |t: Regs| t.wf() && t.holds(ls, pl) && t.holds(rs, pr) && t.keeps(r, 2 * below)
            && #[trigger] Self::goes(rev, data, from, r, to, t)
    }

    /// Code that stores two operands followed by code that combines them stores the combination.
    pub(super) proof fn lemma_combine(rev: Seq<Instr>, ext: Seq<Instr>, data: &[u8], from: nat, r: Regs, mid: nat, below: nat, ls: nat, pl: u64, rs: nat, pr: u64, to: nat, p: u64)
        requires
            Self::extends(rev, ext),
            Self::stores2(ext, data, from, r, mid, below, ls, pl, rs, pr),
            forall |t: Regs| t.wf() && t.holds(ls, pl) && t.holds(rs, pr)
                ==> #[trigger] Self::stores(rev, data, mid, t, to, below, p),
        ensures Self::stores(ext, data, from, r, to, below, p)
    {
        let t = choose |t: Regs| t.wf() && t.holds(ls, pl) && t.holds(rs, pr) && t.keeps(r, 2 * below)
            && #[trigger] Self::goes(ext, data, from, r, mid, t);
        assert(Self::stores(rev, data, mid, t, to, below, p));
        Self::lemma_stores_then(rev, ext, data, from, r, mid, t, 2 * below, to, below, p);
    }
}

impl Expr {
    /// The value a pattern stands for, read as signed or not.
    pub(super) open spec fn unpat(p: u64, signed: bool) -> int {
        if signed && p >= 0x8000_0000_0000_0000 { p - 0x1_0000_0000_0000_0000 } else { p as int }
    }

    /// The words of a pattern, as integers.
    pub(super) proof fn lemma_words(p: u64)
        ensures
            (p as u32) as int == p as int % 0x1_0000_0000,
            ((p >> 32u64) as u32) as int == p as int / 0x1_0000_0000,
    {
        let w = p as u32;
        let h = p >> 32u64;
        assert(w as u64 == p & 0xFFFF_FFFF && h <= 0xFFFF_FFFF) by (bit_vector)
            requires w == p as u32, h == p >> 32u64;
        vstd::bits::lemma_u64_low_bits_mask_is_mod(p, 32);
        vstd::bits::lemma_low_bits_mask_values();
        vstd::arithmetic::power2::lemma2_to64();
        vstd::bits::lemma_u64_shr_is_div(p, 32);
    }

    /// The pattern of `h * 2^32 + l`, for a word `l`, has low word `l` and high word `h`
    /// modulo `2^32`.
    pub(super) proof fn lemma_halves(h: int, l: int)
        requires 0 <= l < 0x1_0000_0000
        ensures
            Self::pat(h * 0x1_0000_0000 + l) as int % 0x1_0000_0000 == l,
            Self::pat(h * 0x1_0000_0000 + l) as int / 0x1_0000_0000 == h % 0x1_0000_0000,
    {
        let q = h / 0x1_0000_0000;
        let m = h % 0x1_0000_0000;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(h, 0x1_0000_0000);
        vstd::arithmetic::div_mod::lemma_mod_bound(h, 0x1_0000_0000);
        let w = m * 0x1_0000_0000 + l;
        assert(h * 0x1_0000_0000 + l == 0x1_0000_0000_0000_0000 * q + w);
        vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(q, w, 0x1_0000_0000_0000_0000);
        vstd::arithmetic::div_mod::lemma_small_mod(w as nat, 0x1_0000_0000_0000_0000);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(w, 0x1_0000_0000, m, l);
    }

    /// A value of type `t` is what its pattern reads as, signed as `t` is, and one of an
    /// unsigned type narrower than 64 bits reads alike as signed.
    pub(super) proof fn lemma_unpat(&self, arch: Arch, ctx: Seq<PrimType>, data: &[u8], t: PrimType)
        requires self.of_type(arch, ctx, t)
        ensures
            Self::unpat(Self::pat(self.value(arch, ctx, data)), t.signed()) == self.value(arch, ctx, data),
            !t.signed() && t.bits(arch) < 64 ==> Self::pat(self.value(arch, ctx, data)) < 0x8000_0000_0000_0000,
    {
        let args = arch.interp_args(Event::of(data).args, ctx);
        match self {
            Expr::Var(i) => t.lemma_range(arch, args[*i as int]),
            Expr::Lit(c, cty) => t.lemma_range(arch, cty.to_bits(arch, *c as int)),
            Expr::Cast(e, cty) => t.lemma_range(arch, cty.to_bits(arch, e.value(arch, ctx, data))),
            Expr::BinOp(op, e1, e2) => {
                let ty = choose |ty: PrimType| self.of_type(arch, ctx, ty);
                self.lemma_type_unique(arch, ctx, ty, t);
                let v1 = e1.value(arch, ctx, data);
                let v2 = e2.value(arch, ctx, data);
                ty.lemma_range(arch, match op {
                    BinOp::Add => ty.to_bits(arch, v1 + v2),
                    BinOp::Sub => ty.to_bits(arch, v1 - v2),
                    _ => op.apply(ty.to_bits(arch, v1), ty.to_bits(arch, v2)),
                });
            }
        }
    }

    /// A binary operation's pattern, from its operands' patterns.
    pub(super) proof fn lemma_binary_pattern(&self, arch: Arch, ctx: Seq<PrimType>, data: &[u8], ty: PrimType)
        requires self is BinOp, self.typed(arch, ctx), self.shaped(arch, ctx, ty)
        ensures
            self.pattern(arch, ctx, data) == ty.norm(arch, self->BinOp_0.apply(
                self->BinOp_1.pattern(arch, ctx, data), self->BinOp_2.pattern(arch, ctx, data))),
    {
        match self {
            Expr::BinOp(op, e1, e2) => {
                let t = choose |t: PrimType| self.of_type(arch, ctx, t);
                t.lemma_same(ty, arch);
                let v1 = e1.value(arch, ctx, data);
                let v2 = e2.value(arch, ctx, data);
                let pl = Self::pat(v1);
                let pr = Self::pat(v2);
                let m = 0x1_0000_0000_0000_0000int;
                match op {
                    BinOp::Add => {
                        ty.lemma_norm_trunc(arch, v1 + v2);
                        vstd::arithmetic::div_mod::lemma_add_mod_noop(v1, v2, m);
                    }
                    BinOp::Sub => {
                        ty.lemma_norm_trunc(arch, v1 - v2);
                        vstd::arithmetic::div_mod::lemma_sub_mod_noop(v1, v2, m);
                    }
                    _ => {
                        t.lemma_to_bits(arch, v1);
                        t.lemma_to_bits(arch, v2);
                        let x1 = t.to_bits(arch, v1);
                        let x2 = t.to_bits(arch, v2);
                        let mask = t.mask(arch);
                        let x = op.apply(x1, x2);
                        let y = op.apply(pl, pr);
                        assert(x & mask == y & mask) by (bit_vector)
                            requires
                                x1 & mask == pl & mask,
                                x2 & mask == pr & mask,
                                (x == x1 & x2 && y == pl & pr) || (x == x1 | x2 && y == pl | pr)
                                    || (x == x1 ^ x2 && y == pl ^ pr);
                    }
                }
            }
            _ => {}
        }
    }
}

impl PrimType {
    /// A value of this type is what its pattern reads as, signed as this type is, and one
    /// of an unsigned type narrower than 64 bits reads alike as signed.
    pub(super) proof fn lemma_range(self, arch: Arch, x: u64)
        ensures
            Expr::unpat(Expr::pat(self.to_int(arch, x)), self.signed()) == self.to_int(arch, x),
            !self.signed() && self.bits(arch) < 64 ==> Expr::pat(self.to_int(arch, x)) < 0x8000_0000_0000_0000,
    {
        let mask = self.mask(arch);
        let p = x & mask;
        let v = self.to_int(arch, x);
        let half = mask >> 1u64;
        assert(p <= mask && half <= 0x7FFF_FFFF_FFFF_FFFF && mask - half <= 0x8000_0000_0000_0000) by (bit_vector)
            requires p == x & mask, half == mask >> 1u64;
        if self.signed() && p > half {
            vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(v, 0x1_0000_0000_0000_0000);
            vstd::arithmetic::div_mod::lemma_small_mod((v + 0x1_0000_0000_0000_0000) as nat, 0x1_0000_0000_0000_0000);
        } else {
            vstd::arithmetic::div_mod::lemma_small_mod(p as nat, 0x1_0000_0000_0000_0000);
        }
        if self.bits(arch) < 64 {
            let bits = self.bits(arch);
            self.lemma_mask(arch);
            assert(mask <= 0x7FFF_FFFF_FFFF_FFFF) by (bit_vector)
                requires bits < 64, mask == ((1u64 << bits) - 1) as u64;
        }
    }

    /// A 64-bit type reads a pattern as [`Expr::unpat`] does.
    pub(super) proof fn lemma_unpat_64(self, arch: Arch, p: u64)
        requires self.bits(arch) == 64
        ensures self.to_int(arch, p) == Expr::unpat(p, self.signed())
    {
        let mask = self.mask(arch);
        assert(p & mask == p && mask >> 1u64 == 0x7FFF_FFFF_FFFF_FFFF) by (bit_vector)
            requires mask == u64::MAX;
    }
}

impl AluOp {
    /// The ALU's wrapping arithmetic, as integers.
    pub(super) proof fn lemma_wrap(a: u32, b: u32)
        ensures
            AluOp::Add.eval(a, b) as int == (a + b) % 0x1_0000_0000,
            AluOp::Sub.eval(a, b) as int == (a - b) % 0x1_0000_0000,
    {
        vstd::bits::lemma_low_bits_mask_values();
        vstd::arithmetic::power2::lemma2_to64();
        let add = AluOp::Add.eval(a, b);
        let sub = AluOp::Sub.eval(a, b);
        let s = (a as u64 + b as u64) as u64;
        let d = (a as u64 + 0x1_0000_0000u64 - b as u64) as u64;
        assert(add as u64 == s & 0xFFFF_FFFF && sub as u64 == d & 0xFFFF_FFFF)
            by (bit_vector)
            requires
                add == (a + b) as u32,
                sub == (a - b) as u32,
                s == (a as u64 + b as u64) as u64,
                d == (a as u64 + 0x1_0000_0000u64 - b as u64) as u64;
        vstd::bits::lemma_u64_low_bits_mask_is_mod(s, 32);
        vstd::bits::lemma_u64_low_bits_mask_is_mod(d, 32);
        vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(a - b, 0x1_0000_0000);
    }
}

impl BinOp {
    /// This operation on 64-bit patterns, wrapping around.
    pub(super) open spec fn apply(self, x: u64, y: u64) -> u64 {
        match self {
            BinOp::Add => Expr::pat(x + y),
            BinOp::Sub => Expr::pat(x - y),
            BinOp::And => x & y,
            BinOp::Or => x | y,
            BinOp::Xor => x ^ y,
        }
    }

    /// The ALU operator that performs this operation on words.
    pub(super) open spec fn spec_alu(self) -> AluOp {
        match self {
            BinOp::Add => AluOp::Add,
            BinOp::Sub => AluOp::Sub,
            BinOp::And => AluOp::And,
            BinOp::Or => AluOp::Or,
            BinOp::Xor => AluOp::Xor,
        }
    }

    /// Executable version of [`BinOp::spec_alu`].
    #[verifier::when_used_as_spec(spec_alu)]
    fn alu(self) -> (res: AluOp)
        ensures res == self.spec_alu()
    {
        match self {
            BinOp::Add => AluOp::Add,
            BinOp::Sub => AluOp::Sub,
            BinOp::And => AluOp::And,
            BinOp::Or => AluOp::Or,
            BinOp::Xor => AluOp::Xor,
        }
    }

    /// The instructions [`BinOp::emit_pairs`] emits before normalizing, for a result more
    /// than 32 bits wide if `wide`.
    pub(super) open spec fn block(self, wide: bool, ls: u32, rs: u32, slot: u32) -> Seq<Instr> {
        if !wide {
            self.narrow_block(ls, rs, slot)
        } else {
            match self {
                BinOp::Add => Self::add_block(ls, rs, slot),
                BinOp::Sub => Self::sub_block(ls, rs, slot),
                _ => self.bitwise_block(ls, rs, slot),
            }
        }
    }

    /// The instructions [`BinOp::emit_pairs`] emits before normalizing a result at most
    /// 32 bits wide.
    pub(super) open spec fn narrow_block(self, ls: u32, rs: u32, slot: u32) -> Seq<Instr> {
        seq![Instr::LdxMem((2 * rs) as u32), Instr::LdMem((2 * ls) as u32), Instr::Alu(self.spec_alu(), Src::X),
            Instr::St((2 * slot) as u32)]
    }

    /// The instructions [`BinOp::emit_pairs`] emits before normalizing a wider bitwise result.
    pub(super) open spec fn bitwise_block(self, ls: u32, rs: u32, slot: u32) -> Seq<Instr> {
        seq![Instr::LdxMem((2 * rs) as u32), Instr::LdMem((2 * ls) as u32), Instr::Alu(self.spec_alu(), Src::X),
            Instr::St((2 * slot) as u32), Instr::LdxMem((2 * rs + 1) as u32), Instr::LdMem((2 * ls + 1) as u32),
            Instr::Alu(self.spec_alu(), Src::X), Instr::St((2 * slot + 1) as u32)]
    }

    /// The instructions [`BinOp::emit_pairs`] emits before normalizing a wider sum.
    pub(super) open spec fn add_block(ls: u32, rs: u32, slot: u32) -> Seq<Instr> {
        let (l0, l1, r0, r1) = ((2 * ls) as u32, (2 * ls + 1) as u32, (2 * rs) as u32, (2 * rs + 1) as u32);
        seq![Instr::LdxMem(l0), Instr::LdMem(r0), Instr::Alu(AluOp::Add, Src::X),
            Instr::Jmp { op: JmpOp::Ge, src: Src::X, jt: 2, jf: 0 },
            Instr::LdImm(1), Instr::Ja(1), Instr::LdImm(0),
            Instr::Tax, Instr::LdMem(l1), Instr::Alu(AluOp::Add, Src::X),
            Instr::LdxMem(r1), Instr::Alu(AluOp::Add, Src::X), Instr::St((2 * slot + 1) as u32),
            Instr::LdxMem(l0), Instr::LdMem(r0), Instr::Alu(AluOp::Add, Src::X), Instr::St((2 * slot) as u32)]
    }

    /// The instructions [`BinOp::emit_pairs`] emits before normalizing a wider difference.
    pub(super) open spec fn sub_block(ls: u32, rs: u32, slot: u32) -> Seq<Instr> {
        let (l0, l1, r0, r1) = ((2 * ls) as u32, (2 * ls + 1) as u32, (2 * rs) as u32, (2 * rs + 1) as u32);
        seq![Instr::LdxMem(r0), Instr::LdMem(l0),
            Instr::Jmp { op: JmpOp::Ge, src: Src::X, jt: 2, jf: 0 },
            Instr::LdImm(1), Instr::Ja(1), Instr::LdImm(0),
            Instr::Tax, Instr::LdMem(l1), Instr::Alu(AluOp::Sub, Src::X),
            Instr::LdxMem(r1), Instr::Alu(AluOp::Sub, Src::X), Instr::St((2 * slot + 1) as u32),
            Instr::LdxMem(r0), Instr::LdMem(l0), Instr::Alu(AluOp::Sub, Src::X), Instr::St((2 * slot) as u32)]
    }

    /// The low word of this operation's pattern is the ALU's result on the low words.
    proof fn lemma_low(self, pl: u64, pr: u64)
        ensures self.spec_alu().eval(pl as u32, pr as u32) == self.apply(pl, pr) as u32
    {
        if self is Add || self is Sub {
            let m32 = 0x1_0000_0000int;
            let m64 = 0x1_0000_0000_0000_0000int;
            let w = self.apply(pl, pr);
            Expr::lemma_words(pl);
            Expr::lemma_words(pr);
            Expr::lemma_words(w);
            AluOp::lemma_wrap(pl as u32, pr as u32);
            let v = if self is Add { pl + pr } else { pl - pr };
            vstd::arithmetic::div_mod::lemma_mod_bound(v, m64);
            vstd::arithmetic::div_mod::lemma_mod_mod(v, m32, m32);
            if self is Add {
                vstd::arithmetic::div_mod::lemma_add_mod_noop(pl as int, pr as int, m32);
            } else {
                vstd::arithmetic::div_mod::lemma_sub_mod_noop(pl as int, pr as int, m32);
            }
        } else {
            let (l0, r0) = (pl as u32, pr as u32);
            assert((pl & pr) as u32 == l0 & r0 && (pl | pr) as u32 == l0 | r0 && (pl ^ pr) as u32 == l0 ^ r0)
                by (bit_vector)
                requires l0 == pl as u32, r0 == pr as u32;
        }
    }

    /// The words of a sum's pattern, as [`BinOp::add_block`] computes them.
    proof fn lemma_add(pl: u64, pr: u64)
        ensures ({
            let (l0, l1, r0, r1) = (pl as u32, (pl >> 32u64) as u32, pr as u32, (pr >> 32u64) as u32);
            let lo = AluOp::Add.eval(r0, l0);
            let c: u32 = if lo >= l0 { 0 } else { 1 };
            &&& BinOp::Add.apply(pl, pr) as u32 == lo
            &&& (BinOp::Add.apply(pl, pr) >> 32u64) as u32 == AluOp::Add.eval(AluOp::Add.eval(l1, c), r1)
        })
    {
        let m32 = 0x1_0000_0000int;
        let (l0, l1, r0, r1) = (pl as u32, (pl >> 32u64) as u32, pr as u32, (pr >> 32u64) as u32);
        let lo = AluOp::Add.eval(r0, l0);
        let c: u32 = if lo >= l0 { 0 } else { 1 };
        let w = BinOp::Add.apply(pl, pr);
        Expr::lemma_words(pl);
        Expr::lemma_words(pr);
        Expr::lemma_words(w);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(pl as int, m32);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(pr as int, m32);
        AluOp::lemma_wrap(r0, l0);
        let carry: int = if l0 + r0 >= m32 { 1 } else { 0 };
        let low = l0 + r0 - carry * m32;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(r0 + l0, m32, carry, low);
        assert(c == carry);
        let t = AluOp::Add.eval(l1, c);
        AluOp::lemma_wrap(l1, c);
        AluOp::lemma_wrap(t, r1);
        vstd::arithmetic::div_mod::lemma_add_mod_noop(l1 + c, r1 as int, m32);
        vstd::arithmetic::div_mod::lemma_small_mod(r1 as nat, m32 as nat);
        vstd::arithmetic::div_mod::lemma_mod_twice(l1 + c, m32);
        assert(pl + pr == (l1 + r1 + carry) * m32 + low);
        Expr::lemma_halves(l1 + r1 + carry, low);
    }

    /// The words of a difference's pattern, as [`BinOp::sub_block`] computes them.
    proof fn lemma_sub(pl: u64, pr: u64)
        ensures ({
            let (l0, l1, r0, r1) = (pl as u32, (pl >> 32u64) as u32, pr as u32, (pr >> 32u64) as u32);
            let bw: u32 = if l0 >= r0 { 0 } else { 1 };
            &&& BinOp::Sub.apply(pl, pr) as u32 == AluOp::Sub.eval(l0, r0)
            &&& (BinOp::Sub.apply(pl, pr) >> 32u64) as u32 == AluOp::Sub.eval(AluOp::Sub.eval(l1, bw), r1)
        })
    {
        let m32 = 0x1_0000_0000int;
        let (l0, l1, r0, r1) = (pl as u32, (pl >> 32u64) as u32, pr as u32, (pr >> 32u64) as u32);
        let bw: u32 = if l0 >= r0 { 0 } else { 1 };
        let w = BinOp::Sub.apply(pl, pr);
        Expr::lemma_words(pl);
        Expr::lemma_words(pr);
        Expr::lemma_words(w);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(pl as int, m32);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(pr as int, m32);
        AluOp::lemma_wrap(l0, r0);
        let low = l0 - r0 + bw * m32;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(l0 - r0, m32, -bw, low);
        let t = AluOp::Sub.eval(l1, bw);
        AluOp::lemma_wrap(l1, bw);
        AluOp::lemma_wrap(t, r1);
        vstd::arithmetic::div_mod::lemma_sub_mod_noop(l1 - bw, r1 as int, m32);
        vstd::arithmetic::div_mod::lemma_small_mod(r1 as nat, m32 as nat);
        vstd::arithmetic::div_mod::lemma_mod_twice(l1 - bw, m32);
        assert(pl - pr == (l1 - r1 - bw) * m32 + low);
        Expr::lemma_halves(l1 - r1 - bw, low);
    }

    /// Running [`BinOp::block`] computes the words of the pattern the result reads.
    proof fn lemma_run(self, wide: bool, ls: u32, rs: u32, slot: u32, data: &[u8], t: Regs, pl: u64, pr: u64) -> (u: Regs)
        requires
            ls < 8, rs < 8, slot < 8, ls != rs, slot == ls || slot == rs,
            t.wf(), t.holds(ls as nat, pl), t.holds(rs as nat, pr),
        ensures
            Instr::exec_block(self.block(wide, ls, rs, slot), 0, data, t) == Some(u),
            u.wf(),
            u.keeps(t, 2 * slot as nat),
            u.mem[2 * slot as int] == Some(self.apply(pl, pr) as u32),
            wide ==> u.mem[2 * slot + 1] == Some((self.apply(pl, pr) >> 32u64) as u32),
    {
        if !wide {
            self.lemma_run_narrow(ls, rs, slot, data, t, pl, pr)
        } else {
            match self {
                BinOp::Add => Self::lemma_run_add(ls, rs, slot, data, t, pl, pr),
                BinOp::Sub => Self::lemma_run_sub(ls, rs, slot, data, t, pl, pr),
                _ => self.lemma_run_bitwise(ls, rs, slot, data, t, pl, pr),
            }
        }
    }

    /// Running [`BinOp::narrow_block`] computes the low word of the pattern.
    proof fn lemma_run_narrow(self, ls: u32, rs: u32, slot: u32, data: &[u8], t: Regs, pl: u64, pr: u64) -> (u: Regs)
        requires
            ls < 8, rs < 8, slot < 8, ls != rs, slot == ls || slot == rs,
            t.wf(), t.holds(ls as nat, pl), t.holds(rs as nat, pr),
        ensures
            Instr::exec_block(self.narrow_block(ls, rs, slot), 0, data, t) == Some(u),
            u.wf(),
            u.keeps(t, 2 * slot as nat),
            u.mem[2 * slot as int] == Some(self.apply(pl, pr) as u32),
    {
        self.lemma_low(pl, pr);
        reveal_with_fuel(Instr::exec_block, 5);
        Instr::exec_block(self.narrow_block(ls, rs, slot), 0, data, t)->Some_0
    }

    /// Running [`BinOp::add_block`] computes both words of the pattern of a sum.
    proof fn lemma_run_add(ls: u32, rs: u32, slot: u32, data: &[u8], t: Regs, pl: u64, pr: u64) -> (u: Regs)
        requires
            ls < 8, rs < 8, slot < 8, ls != rs, slot == ls || slot == rs,
            t.wf(), t.holds(ls as nat, pl), t.holds(rs as nat, pr),
        ensures
            Instr::exec_block(Self::add_block(ls, rs, slot), 0, data, t) == Some(u),
            u.wf(),
            u.keeps(t, 2 * slot as nat),
            u.mem[2 * slot as int] == Some(BinOp::Add.apply(pl, pr) as u32),
            u.mem[2 * slot + 1] == Some((BinOp::Add.apply(pl, pr) >> 32u64) as u32),
    {
        let (l0, l1, r0, r1) = (pl as u32, (pl >> 32u64) as u32, pr as u32, (pr >> 32u64) as u32);
        let lo = AluOp::Add.eval(r0, l0);
        let c: u32 = if lo >= l0 { 0 } else { 1 };
        Self::lemma_add_low(ls, rs, slot, data, t, l0, r0);
        let u = Self::lemma_add_high(ls, rs, slot, data, Regs { a: c, x: l0, mem: t.mem }, l0, l1, r0, r1);
        Self::lemma_add(pl, pr);
        u
    }

    /// The low words of [`BinOp::add_block`] leave the carry out of them in `A`.
    proof fn lemma_add_low(ls: u32, rs: u32, slot: u32, data: &[u8], t: Regs, l0: u32, r0: u32)
        requires ls < 8, rs < 8, t.wf(), t.mem[2 * ls as int] == Some(l0), t.mem[2 * rs as int] == Some(r0)
        ensures ({
            let lo = AluOp::Add.eval(r0, l0);
            let c: u32 = if lo >= l0 { 0 } else { 1 };
            Instr::exec_block(Self::add_block(ls, rs, slot), 0, data, t)
                == Instr::exec_block(Self::add_block(ls, rs, slot), 7, data, Regs { a: c, x: l0, mem: t.mem })
        })
    {
        reveal_with_fuel(Instr::exec_block, 8);
    }

    /// The high words of [`BinOp::add_block`] take in the carry, then the low words are
    /// summed again.
    proof fn lemma_add_high(ls: u32, rs: u32, slot: u32, data: &[u8], t: Regs, l0: u32, l1: u32, r0: u32, r1: u32) -> (u: Regs)
        requires
            ls < 8, rs < 8, slot < 8, ls != rs, slot == ls || slot == rs, t.wf(),
            t.mem[2 * ls as int] == Some(l0), t.mem[2 * ls + 1] == Some(l1),
            t.mem[2 * rs as int] == Some(r0), t.mem[2 * rs + 1] == Some(r1),
        ensures
            Instr::exec_block(Self::add_block(ls, rs, slot), 7, data, t) == Some(u),
            u.wf(),
            u.keeps(t, 2 * slot as nat),
            u.mem[2 * slot as int] == Some(AluOp::Add.eval(r0, l0)),
            u.mem[2 * slot + 1] == Some(AluOp::Add.eval(AluOp::Add.eval(l1, t.a), r1)),
    {
        reveal_with_fuel(Instr::exec_block, 11);
        Instr::exec_block(Self::add_block(ls, rs, slot), 7, data, t)->Some_0
    }

    /// Running [`BinOp::sub_block`] computes both words of the pattern of a difference.
    proof fn lemma_run_sub(ls: u32, rs: u32, slot: u32, data: &[u8], t: Regs, pl: u64, pr: u64) -> (u: Regs)
        requires
            ls < 8, rs < 8, slot < 8, ls != rs, slot == ls || slot == rs,
            t.wf(), t.holds(ls as nat, pl), t.holds(rs as nat, pr),
        ensures
            Instr::exec_block(Self::sub_block(ls, rs, slot), 0, data, t) == Some(u),
            u.wf(),
            u.keeps(t, 2 * slot as nat),
            u.mem[2 * slot as int] == Some(BinOp::Sub.apply(pl, pr) as u32),
            u.mem[2 * slot + 1] == Some((BinOp::Sub.apply(pl, pr) >> 32u64) as u32),
    {
        let (l0, l1, r0, r1) = (pl as u32, (pl >> 32u64) as u32, pr as u32, (pr >> 32u64) as u32);
        let bw: u32 = if l0 >= r0 { 0 } else { 1 };
        Self::lemma_sub_low(ls, rs, slot, data, t, l0, r0);
        let u = Self::lemma_sub_high(ls, rs, slot, data, Regs { a: bw, x: r0, mem: t.mem }, l0, l1, r0, r1);
        Self::lemma_sub(pl, pr);
        u
    }

    /// The low words of [`BinOp::sub_block`] leave the borrow out of them in `A`.
    proof fn lemma_sub_low(ls: u32, rs: u32, slot: u32, data: &[u8], t: Regs, l0: u32, r0: u32)
        requires ls < 8, rs < 8, t.wf(), t.mem[2 * ls as int] == Some(l0), t.mem[2 * rs as int] == Some(r0)
        ensures ({
            let bw: u32 = if l0 >= r0 { 0 } else { 1 };
            Instr::exec_block(Self::sub_block(ls, rs, slot), 0, data, t)
                == Instr::exec_block(Self::sub_block(ls, rs, slot), 6, data, Regs { a: bw, x: r0, mem: t.mem })
        })
    {
        reveal_with_fuel(Instr::exec_block, 7);
    }

    /// The high words of [`BinOp::sub_block`] take in the borrow, then the low words are
    /// subtracted again.
    proof fn lemma_sub_high(ls: u32, rs: u32, slot: u32, data: &[u8], t: Regs, l0: u32, l1: u32, r0: u32, r1: u32) -> (u: Regs)
        requires
            ls < 8, rs < 8, slot < 8, ls != rs, slot == ls || slot == rs, t.wf(),
            t.mem[2 * ls as int] == Some(l0), t.mem[2 * ls + 1] == Some(l1),
            t.mem[2 * rs as int] == Some(r0), t.mem[2 * rs + 1] == Some(r1),
        ensures
            Instr::exec_block(Self::sub_block(ls, rs, slot), 6, data, t) == Some(u),
            u.wf(),
            u.keeps(t, 2 * slot as nat),
            u.mem[2 * slot as int] == Some(AluOp::Sub.eval(l0, r0)),
            u.mem[2 * slot + 1] == Some(AluOp::Sub.eval(AluOp::Sub.eval(l1, t.a), r1)),
    {
        reveal_with_fuel(Instr::exec_block, 11);
        Instr::exec_block(Self::sub_block(ls, rs, slot), 6, data, t)->Some_0
    }

    /// Running [`BinOp::bitwise_block`] combines the two pairs word by word.
    proof fn lemma_run_bitwise(self, ls: u32, rs: u32, slot: u32, data: &[u8], t: Regs, pl: u64, pr: u64) -> (u: Regs)
        requires
            !(self is Add), !(self is Sub),
            ls < 8, rs < 8, slot < 8, ls != rs, slot == ls || slot == rs,
            t.wf(), t.holds(ls as nat, pl), t.holds(rs as nat, pr),
        ensures
            Instr::exec_block(self.bitwise_block(ls, rs, slot), 0, data, t) == Some(u),
            u.wf(),
            u.keeps(t, 2 * slot as nat),
            u.mem[2 * slot as int] == Some(self.apply(pl, pr) as u32),
            u.mem[2 * slot + 1] == Some((self.apply(pl, pr) >> 32u64) as u32),
    {
        let x = self.apply(pl, pr);
        let (l0, l1, r0, r1) = (pl as u32, (pl >> 32u64) as u32, pr as u32, (pr >> 32u64) as u32);
        assert(((pl & pr) as u32 == l0 & r0 && ((pl & pr) >> 32u64) as u32 == l1 & r1)
            && ((pl | pr) as u32 == l0 | r0 && ((pl | pr) >> 32u64) as u32 == l1 | r1)
            && ((pl ^ pr) as u32 == l0 ^ r0 && ((pl ^ pr) >> 32u64) as u32 == l1 ^ r1)) by (bit_vector)
            requires l0 == pl as u32, l1 == (pl >> 32u64) as u32, r0 == pr as u32, r1 == (pr >> 32u64) as u32;
        reveal_with_fuel(Instr::exec_block, 9);
        Instr::exec_block(self.bitwise_block(ls, rs, slot), 0, data, t)->Some_0
    }

    /// Emits code that combines the patterns in scratch pairs `ls` and `rs` into pair
    /// `slot`, as a value of type `ty`.
    ///
    /// ```text
    ///     ldx M[rs.lo]            ; result at most 32 bits wide
    ///     ld  M[ls.lo]
    ///     <op> x
    ///     st  M[slot.lo]
    ///
    ///     ldx M[ls.lo]            ; wider sum
    ///     ld  M[rs.lo]
    ///     add x
    ///     jge x -> nc
    ///     ld  #1
    ///     ja  carry
    /// nc: ld  #0
    /// carry:
    ///     tax
    ///     ld  M[ls.hi]
    ///     add x
    ///     ldx M[rs.hi]
    ///     add x
    ///     st  M[slot.hi]
    ///     ldx M[ls.lo]
    ///     ld  M[rs.lo]
    ///     add x
    ///     st  M[slot.lo]
    ///
    ///     ldx M[rs.lo]            ; wider difference
    ///     ld  M[ls.lo]
    ///     jge x -> nb
    ///     ld  #1
    ///     ja  borrow
    /// nb: ld  #0
    /// borrow:
    ///     tax
    ///     ld  M[ls.hi]
    ///     sub x
    ///     ldx M[rs.hi]
    ///     sub x
    ///     st  M[slot.hi]
    ///     ldx M[rs.lo]
    ///     ld  M[ls.lo]
    ///     sub x
    ///     st  M[slot.lo]
    ///
    ///     ldx M[rs.lo]            ; wider bitwise result
    ///     ld  M[ls.lo]
    ///     <op> x
    ///     st  M[slot.lo]
    ///     ldx M[rs.hi]
    ///     ld  M[ls.hi]
    ///     <op> x
    ///     st  M[slot.hi]
    ///
    ///     <normalize>
    /// ```
    fn emit_pairs(self, b: &mut Builder, arch: Arch, ty: PrimType, ls: u32, rs: u32, slot: u32)
        requires
            old(b).wf(), 0 < old(b).rev@.len(), ty.wf(),
            ls < 8, rs < 8, slot < 8, ls != rs, slot == ls || slot == rs,
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            forall |data: &[u8], t: Regs, pl: u64, pr: u64| t.wf() && t.holds(ls as nat, pl) && t.holds(rs as nat, pr)
                ==> #[trigger] Builder::stores(final(b).rev@, data, final(b).rev@.len(), t, old(b).rev@.len(),
                    slot as nat, ty.norm(arch, self.apply(pl, pr))),
    {
        let wide = ty.exec_bits(arch) > 32;
        let ghost base = b.rev@;
        ty.emit_norm(b, arch, slot);
        let ghost r_norm = b.rev@;
        let (l0, l1, r0, r1, d0, d1) = (2 * ls, 2 * ls + 1, 2 * rs, 2 * rs + 1, 2 * slot, 2 * slot + 1);
        if !wide {
            let block = [Instr::LdxMem(r0), Instr::LdMem(l0), Instr::Alu(self.alu(), Src::X), Instr::St(d0)];
            proof { reveal_with_fuel(Instr::fits_from, 5); }
            b.emit_block(&block);
            proof { assert(block@ == self.block(wide, ls, rs, slot)); }
        } else if self == BinOp::Add {
            let block = [Instr::LdxMem(l0), Instr::LdMem(r0), Instr::Alu(AluOp::Add, Src::X),
                Instr::Jmp { op: JmpOp::Ge, src: Src::X, jt: 2, jf: 0 },
                Instr::LdImm(1), Instr::Ja(1), Instr::LdImm(0),
                Instr::Tax, Instr::LdMem(l1), Instr::Alu(AluOp::Add, Src::X),
                Instr::LdxMem(r1), Instr::Alu(AluOp::Add, Src::X), Instr::St(d1),
                Instr::LdxMem(l0), Instr::LdMem(r0), Instr::Alu(AluOp::Add, Src::X), Instr::St(d0)];
            proof { reveal_with_fuel(Instr::fits_from, 18); }
            b.emit_block(&block);
            proof { assert(block@ == self.block(wide, ls, rs, slot)); }
        } else if self == BinOp::Sub {
            let block = [Instr::LdxMem(r0), Instr::LdMem(l0),
                Instr::Jmp { op: JmpOp::Ge, src: Src::X, jt: 2, jf: 0 },
                Instr::LdImm(1), Instr::Ja(1), Instr::LdImm(0),
                Instr::Tax, Instr::LdMem(l1), Instr::Alu(AluOp::Sub, Src::X),
                Instr::LdxMem(r1), Instr::Alu(AluOp::Sub, Src::X), Instr::St(d1),
                Instr::LdxMem(r0), Instr::LdMem(l0), Instr::Alu(AluOp::Sub, Src::X), Instr::St(d0)];
            proof { reveal_with_fuel(Instr::fits_from, 17); }
            b.emit_block(&block);
            proof { assert(block@ == self.block(wide, ls, rs, slot)); }
        } else {
            let op = self.alu();
            let block = [Instr::LdxMem(r0), Instr::LdMem(l0), Instr::Alu(op, Src::X), Instr::St(d0),
                Instr::LdxMem(r1), Instr::LdMem(l1), Instr::Alu(op, Src::X), Instr::St(d1)];
            proof { reveal_with_fuel(Instr::fits_from, 9); }
            b.emit_block(&block);
            proof { assert(block@ == self.block(wide, ls, rs, slot)); }
        }
        proof {
            assert forall |data: &[u8], t: Regs, pl: u64, pr: u64| t.wf() && t.holds(ls as nat, pl) && t.holds(rs as nat, pr)
                implies #[trigger] Builder::stores(b.rev@, data, b.rev@.len(), t, base.len(), slot as nat,
                    ty.norm(arch, self.apply(pl, pr))) by {
                let u = self.lemma_run(wide, ls, rs, slot, data, t, pl, pr);
                assert(Builder::goes(b.rev@, data, b.rev@.len(), t, r_norm.len(), u));
                assert(Builder::stores(r_norm, data, r_norm.len(), u, base.len(), slot as nat, ty.norm(arch, self.apply(pl, pr))));
                Builder::lemma_stores_then(r_norm, b.rev@, data, b.rev@.len(), t, r_norm.len(), u,
                    2 * slot as nat, base.len(), slot as nat, ty.norm(arch, self.apply(pl, pr)));
            }
        }
    }
}

} // verus!
