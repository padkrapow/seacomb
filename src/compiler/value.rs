//! Compiling expressions to code that leaves one 32-bit word of their values in `A`.

use vstd::prelude::*;
use vstd::pervasive::unreached;
use crate::spec::{policy::*, expr::*, cbpf::*};
use super::CompileError;
use super::builder::Builder;
use super::machine::Regs;

verus! {

impl Expr {
    /// The 64-bit two's complement pattern of `v`.
    pub(crate) open spec fn pat(v: int) -> u64 {
        (v % 0x1_0000_0000_0000_0000) as u64
    }

    /// The pattern of this expression's value on the event `data` describes.
    pub(super) open spec fn pattern(&self, arch: Arch, ctx: Seq<PrimType>, data: &[u8]) -> u64 {
        Self::pat(self.value(arch, ctx, data))
    }

    /// The low or high word of the pattern of this expression's value.
    pub(super) open spec fn word(&self, arch: Arch, ctx: Seq<PrimType>, data: &[u8], hi: bool) -> u32 {
        let p = self.pattern(arch, ctx, data);
        if hi { (p >> 32) as u32 } else { p as u32 }
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
    pub(crate) proof fn lemma_to_bits(self, arch: Arch, v: int)
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

    /// Returns the pattern of the literal `c` converted to this type.
    pub(crate) fn lit_pattern(self, arch: Arch, c: i64) -> (res: u64)
        ensures res == Expr::pat(self.trunc(arch, c as int))
    {
        // The 64-bit two's complement word of `c`.
        let q = if c >= 0 { c as u64 } else { u64::MAX - (-(c + 1)) as u64 };
        proof {
            assert(q == Expr::pat(c as int)) by {
                if c < 0 {
                    vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(c as int, 0x1_0000_0000_0000_0000);
                }
                vstd::arithmetic::div_mod::lemma_small_mod(q as nat, 0x1_0000_0000_0000_0000);
            }
            self.lemma_norm_trunc(arch, c as int);
        }
        self.exec_norm(arch, q)
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

    /// A 64-bit type reads every pattern as itself.
    proof fn lemma_norm_64(self, arch: Arch, q: u64)
        requires self.bits(arch) == 64
        ensures self.norm(arch, q) == q
    {
        self.lemma_norm(arch, q);
        assert(q & u64::MAX == q && q | !u64::MAX == q) by (bit_vector);
    }
}

impl Regs {
    /// Whether the scratch words below `n` are those of `r`.
    pub(super) open spec fn keeps(self, r: Regs, n: nat) -> bool {
        forall |k: int| 0 <= k < n ==> #[trigger] self.mem[k] == r.mem[k]
    }
}

impl Builder {
    /// Whether every extension of `rev`, entered at `from` with registers `r`, carries on
    /// at `to` with `A` holding `w` and the scratch words below `sp` as `r` has them.
    pub(super) open spec fn loads(rev: Seq<Instr>, data: &[u8], from: nat, r: Regs, to: nat, w: u32, sp: nat) -> bool {
        exists |t: Regs| t.wf() && t.a == w && t.keeps(r, sp)
            && #[trigger] Self::goes(rev, data, from, r, to, t)
    }

    /// Whether every extension of `rev`, entered at `from` with registers `r`, carries on
    /// at `to` with `A` holding `w`, `src` holding `v`, and the scratch words below `sp` as
    /// `r` has them.
    pub(super) open spec fn loads2(rev: Seq<Instr>, data: &[u8], from: nat, r: Regs, to: nat, w: u32, src: Src, v: u32, sp: nat) -> bool {
        exists |t: Regs| t.wf() && t.a == w && src.eval(t.at(0)) == v && t.keeps(r, sp)
            && #[trigger] Self::goes(rev, data, from, r, to, t)
    }
}

impl PrimType {
    /// Emits code that turns the low word of `q` in `A` into the low word of the pattern
    /// this type reads `q` as.
    ///
    /// ```text
    ///     and #mask               ; bits < 32
    ///     xor #sign               ; bits < 32, signed only
    ///     sub #sign               ; bits < 32, signed only
    ///
    ///                             ; 32 and 64 bits emit nothing
    /// ```
    pub(super) fn emit_norm(self, b: &mut Builder, arch: Arch)
        requires self.wf(), old(b).wf(), 0 < old(b).rev@.len()
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            forall |data: &[u8], r: Regs, q: u64| r.a == q as u32 ==>
                #[trigger] Builder::goes(final(b).rev@, data, final(b).rev@.len(), r,
                    old(b).rev@.len(), Regs { a: self.norm(arch, q) as u32, ..r }),
    {
        let ghost base = b.rev@;
        let bits = self.exec_bits(arch);
        if bits >= 32 {
            proof {
                assert forall |data: &[u8], r: Regs, q: u64| r.a == q as u32 implies
                    #[trigger] Builder::goes(b.rev@, data, b.rev@.len(), r, base.len(),
                        Regs { a: self.norm(arch, q) as u32, ..r }) by {
                    if bits == 32 {
                        self.lemma_mask(arch);
                        self.lemma_norm(arch, q);
                        assert(((1u64 << 32u64) - 1) as u64 == 0xFFFF_FFFFu64) by (bit_vector);
                        Self::lemma_norm_word(q, self.signed());
                    } else {
                        self.lemma_norm_64(arch, q);
                    }
                    assert(Builder::goes(b.rev@, data, b.rev@.len(), r, base.len(), r));
                }
            }
            return;
        }
        let mask = self.exec_mask(arch);
        proof { assert(mask >> 1u64 < u64::MAX) by (bit_vector); }
        let m0 = mask as u32;
        let s0 = ((mask >> 1) + 1) as u32;
        let block: &[Instr] = if self.exec_signed() {
            &[Instr::Alu(AluOp::And, Src::K(m0)), Instr::Alu(AluOp::Xor, Src::K(s0)),
                Instr::Alu(AluOp::Sub, Src::K(s0))]
        } else {
            &[Instr::Alu(AluOp::And, Src::K(m0))]
        };
        proof { reveal_with_fuel(Instr::fits_from, 4); }
        b.emit_block(block);
        proof {
            assert forall |data: &[u8], r: Regs, q: u64| r.a == q as u32 implies
                #[trigger] Builder::goes(b.rev@, data, b.rev@.len(), r, base.len(),
                    Regs { a: self.norm(arch, q) as u32, ..r }) by {
                self.lemma_mask(arch);
                self.lemma_norm(arch, q);
                Self::lemma_norm_narrow(q, mask, self.bits(arch), self.signed());
                reveal_with_fuel(Instr::exec_block, 4);
                assert(Instr::exec_block(block@, 0, data, r) == Some(Regs { a: self.norm(arch, q) as u32, ..r }));
            }
        }
    }
}

impl Arch {
    /// Returns the offsets in `seccomp_data` of the low and high words of argument `n` of a
    /// syscall with signature `sig`.
    fn arg_offsets(self, sig: &[PrimType], n: usize) -> (res: Result<(u32, u32), CompileError>)
        requires n < sig@.len()
        ensures res matches Ok((lo, hi)) ==> {
            &&& lo % 4 == 0 && lo + 4 <= 64
            &&& hi % 4 == 0 && hi + 4 <= 64
            &&& forall |data: &[u8]| Event::parse(data) is Some ==> #[trigger] Builder::word(data, lo)
                == self.interp_args(Event::of(data).args, sig@)[n as int] as u32
            &&& forall |data: &[u8]| Event::parse(data) is Some ==> #[trigger] Builder::word(data, hi)
                == (self.interp_args(Event::of(data).args, sig@)[n as int] >> 32) as u32
        }
    {
        let at = self.arg_slot(sig, n)?;
        let lo = Event::OFFSET_ARGS + 8 * at;
        let hi = if self.exec_splits(sig[n]) { lo + 8 } else { lo + 4 };
        proof {
            assert forall |data: &[u8]|
                #![trigger Builder::word(data, lo)]
                #![trigger Builder::word(data, hi)]
                Event::parse(data) is Some implies {
                let raw = self.interp_args(Event::of(data).args, sig@)[n as int];
                &&& Builder::word(data, lo) == raw as u32
                &&& Builder::word(data, hi) == (raw >> 32) as u32
            } by {
                let ev = Event::of(data);
                Event::lemma_image(data);
                let raw = self.raw(ev.args, sig@[n as int], at as nat);
                assert(self.interp_args(ev.args, sig@)[n as int] == raw);
                self.lemma_raw_words(ev.args, sig@[n as int], at as nat);
                let lv = ev.args[at as int];
                assert((lv & 0xFFFF_FFFF) as u32 == lv as u32) by (bit_vector);
                assert(Builder::word(data, (Event::OFFSET_ARGS + 8 * at) as u32)
                    == (ev.args[at as int] & 0xFFFF_FFFF) as u32);
                if self.splits(sig@[n as int]) {
                    let hv = ev.args[at + 1 as int];
                    assert((hv & 0xFFFF_FFFF) as u32 == hv as u32) by (bit_vector);
                    assert(Builder::word(data, (Event::OFFSET_ARGS + 8 * (at + 1)) as u32)
                        == (ev.args[at + 1 as int] & 0xFFFF_FFFF) as u32);
                } else {
                    assert(Builder::word(data, (Event::OFFSET_ARGS + 8 * at + 4) as u32)
                        == (ev.args[at as int] >> 32) as u32);
                }
            }
        }
        Ok((lo, hi))
    }
}

impl Expr {
    /// Whether this expression has a type.
    pub(crate) open spec fn typed(&self, arch: Arch, ctx: Seq<PrimType>) -> bool {
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
    pub(crate) proof fn lemma_operands_typed(&self, arch: Arch, ctx: Seq<PrimType>)
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

    /// Where an operation reads this expression's low or high word, flipped by `bias`, as
    /// its right operand: as an immediate if it is a literal, and from `X` otherwise.
    pub(super) open spec fn spec_src(&self, arch: Arch, hi: bool, bias: u32) -> Src {
        match *self {
            Expr::Lit(c, ty) => {
                let p = Self::pat(ty.trunc(arch, c as int));
                Src::K((if hi { (p >> 32) as u32 } else { p as u32 }) ^ bias)
            }
            _ => Src::X,
        }
    }

    /// Executable version of [`Expr::spec_src`].
    #[verifier::when_used_as_spec(spec_src)]
    pub(super) fn src(&self, arch: Arch, hi: bool, bias: u32) -> (res: Src)
        ensures res == self.spec_src(arch, hi, bias)
    {
        match self {
            Expr::Lit(c, ty) => {
                let p = ty.lit_pattern(arch, *c);
                Src::K((if hi { (p >> 32) as u32 } else { p as u32 }) ^ bias)
            }
            _ => Src::X,
        }
    }

    /// Emits code that leaves the low word of this expression's pattern in `A`.
    ///
    /// ```text
    ///     ld  [arg.lo]            ; argument
    ///     <normalize>
    ///
    ///     ld  #lo                 ; literal
    ///
    ///     <operand's low word>    ; conversion
    ///     <normalize>
    ///
    ///     <operands' low words>   ; binary operation
    ///     <op> src
    ///     <normalize>
    /// ```
    pub(super) fn emit_lo(&self, b: &mut Builder, arch: Arch, sig: &[PrimType], sp: u32)
        -> (res: Result<(), CompileError>)
        requires old(b).wf(), 0 < old(b).rev@.len(), sp <= 16, self.typed(arch, sig@)
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf() ==>
                #[trigger] Builder::loads(final(b).rev@, data, final(b).rev@.len(), st,
                    old(b).rev@.len(), self.word(arch, sig@, data, false), sp as nat),
        decreases self.size(), 0nat
    {
        proof { self.lemma_operands_typed(arch, sig@); }
        let ghost base = b.rev@;
        match self {
            Expr::Var(i) => {
                let ty = sig[*i as usize];
                let (lo, _) = arch.arg_offsets(sig, *i as usize)?;
                ty.emit_norm(b, arch);
                let ghost r_norm = b.rev@;
                b.emit(Instr::LdAbs(lo));
                proof {
                    Builder::lemma_ld(b.rev@, lo);
                    assert forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf() implies
                        #[trigger] Builder::loads(b.rev@, data, b.rev@.len(), st, base.len(),
                            self.word(arch, sig@, data, false), sp as nat) by {
                        let raw = arch.interp_args(Event::of(data).args, sig@)[*i as int];
                        let t1 = Regs { a: Builder::word(data, lo), ..st };
                        let t2 = Regs { a: ty.norm(arch, raw) as u32, ..t1 };
                        assert(Builder::goes(b.rev@, data, b.rev@.len(), st, r_norm.len(), t1));
                        assert(Builder::goes(r_norm, data, r_norm.len(), t1, base.len(), t2));
                        Builder::lemma_goes_trans(r_norm, b.rev@, data, b.rev@.len(), st, r_norm.len(), t1,
                            base.len(), t2);
                    }
                }
            }
            Expr::Lit(c, ty) => {
                let p = ty.lit_pattern(arch, *c);
                let block = [Instr::LdImm(p as u32)];
                proof { reveal_with_fuel(Instr::fits_from, 2); }
                b.emit_block(&block);
                proof {
                    assert forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf() implies
                        #[trigger] Builder::loads(b.rev@, data, b.rev@.len(), st, base.len(),
                            self.word(arch, sig@, data, false), sp as nat) by {
                        reveal_with_fuel(Instr::exec_block, 2);
                        assert(Instr::exec_block(block@, 0, data, st) == Some(Regs { a: p as u32, ..st }));
                    }
                }
            }
            Expr::Cast(e, ty) => {
                ty.emit_norm(b, arch);
                let ghost r_norm = b.rev@;
                e.emit_lo(b, arch, sig, sp)?;
                proof {
                    assert forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf() implies
                        #[trigger] Builder::loads(b.rev@, data, b.rev@.len(), st, base.len(),
                            self.word(arch, sig@, data, false), sp as nat) by {
                        let we = e.word(arch, sig@, data, false);
                        ty.lemma_norm_trunc(arch, e.value(arch, sig@, data));
                        assert(Builder::loads(b.rev@, data, b.rev@.len(), st, r_norm.len(), we, sp as nat));
                        let t1 = choose |t1: Regs| t1.wf() && t1.a == we && t1.keeps(st, sp as nat)
                            && #[trigger] Builder::goes(b.rev@, data, b.rev@.len(), st, r_norm.len(), t1);
                        let t2 = Regs { a: ty.norm(arch, e.pattern(arch, sig@, data)) as u32, ..t1 };
                        assert(Builder::goes(r_norm, data, r_norm.len(), t1, base.len(), t2));
                        Builder::lemma_goes_trans(r_norm, b.rev@, data, b.rev@.len(), st, r_norm.len(), t1,
                            base.len(), t2);
                    }
                }
            }
            Expr::BinOp(op, l, r) => {
                let ty = self.ty(arch, sig);
                ty.emit_norm(b, arch);
                let ghost r_norm = b.rev@;
                let src = r.src(arch, false, 0);
                let block = [Instr::Alu(op.alu(), src)];
                proof { reveal_with_fuel(Instr::fits_from, 2); }
                b.emit_block(&block);
                let ghost r_op = b.rev@;
                l.emit_operands(r, b, arch, sig, false, 0, sp)?;
                proof {
                    assert forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf() implies
                        #[trigger] Builder::loads(b.rev@, data, b.rev@.len(), st, base.len(),
                            self.word(arch, sig@, data, false), sp as nat) by {
                        let pl = l.pattern(arch, sig@, data);
                        let pr = r.pattern(arch, sig@, data);
                        let (wl, wr) = (l.word(arch, sig@, data, false), r.word(arch, sig@, data, false));
                        self.lemma_binary_pattern(arch, sig@, data, ty);
                        op.lemma_low(pl, pr);
                        assert(wl ^ 0u32 == wl && wr ^ 0u32 == wr) by (bit_vector);
                        assert(Builder::loads2(b.rev@, data, b.rev@.len(), st, r_op.len(), wl ^ 0, src,
                            wr ^ 0, sp as nat));
                        let t1 = choose |t1: Regs| t1.wf() && t1.a == wl ^ 0 && src.eval(t1.at(0)) == wr ^ 0
                            && t1.keeps(st, sp as nat)
                            && #[trigger] Builder::goes(b.rev@, data, b.rev@.len(), st, r_op.len(), t1);
                        let t2 = Regs { a: op.spec_alu().eval(wl, wr), ..t1 };
                        reveal_with_fuel(Instr::exec_block, 2);
                        assert(Instr::exec_block(block@, 0, data, t1) == Some(t2));
                        let t3 = Regs { a: ty.norm(arch, op.apply(pl, pr)) as u32, ..t2 };
                        assert(Builder::goes(r_norm, data, r_norm.len(), t2, base.len(), t3));
                        Builder::lemma_goes_trans(r_op, b.rev@, data, b.rev@.len(), st, r_op.len(), t1,
                            r_norm.len(), t2);
                        Builder::lemma_goes_trans(r_norm, b.rev@, data, b.rev@.len(), st, r_norm.len(), t2,
                            base.len(), t3);
                    }
                }
            }
        }
        Ok(())
    }

    /// Emits code that leaves the high word of this expression's pattern in `A`.
    ///
    /// ```text
    ///     <sign extension>        ; at most 32 bits
    ///
    ///     ld  [arg.hi]            ; argument
    ///
    ///     ld  #hi                 ; literal
    ///
    ///     <operand's high word>   ; conversion
    ///
    ///     <operands' high words>  ; and, or, xor
    ///     <op> src
    ///
    ///     <carry>                 ; add, sub
    /// ```
    pub(super) fn emit_hi(&self, b: &mut Builder, arch: Arch, sig: &[PrimType], sp: u32)
        -> (res: Result<(), CompileError>)
        requires old(b).wf(), 0 < old(b).rev@.len(), sp <= 16, self.typed(arch, sig@)
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf() ==>
                #[trigger] Builder::loads(final(b).rev@, data, final(b).rev@.len(), st,
                    old(b).rev@.len(), self.word(arch, sig@, data, true), sp as nat),
        decreases self.size(), 2nat
    {
        proof { self.lemma_operands_typed(arch, sig@); }
        let ghost base = b.rev@;
        let ghost t = choose |t: PrimType| self.of_type(arch, sig@, t);
        let ty = self.ty(arch, sig);
        if ty.exec_bits(arch) <= 32 {
            return self.emit_sext(b, arch, sig, ty, sp);
        }
        match self {
            Expr::Var(i) => {
                let (_, hi) = arch.arg_offsets(sig, *i as usize)?;
                b.emit(Instr::LdAbs(hi));
                proof {
                    Builder::lemma_ld(b.rev@, hi);
                    assert forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf() implies
                        #[trigger] Builder::loads(b.rev@, data, b.rev@.len(), st, base.len(),
                            self.word(arch, sig@, data, true), sp as nat) by {
                        t.lemma_norm_64(arch, arch.interp_args(Event::of(data).args, sig@)[*i as int]);
                        assert(Builder::goes(b.rev@, data, b.rev@.len(), st, base.len(),
                            Regs { a: Builder::word(data, hi), ..st }));
                    }
                }
            }
            Expr::Lit(c, cty) => {
                let p = cty.lit_pattern(arch, *c);
                let block = [Instr::LdImm((p >> 32) as u32)];
                proof { reveal_with_fuel(Instr::fits_from, 2); }
                b.emit_block(&block);
                proof {
                    assert forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf() implies
                        #[trigger] Builder::loads(b.rev@, data, b.rev@.len(), st, base.len(),
                            self.word(arch, sig@, data, true), sp as nat) by {
                        reveal_with_fuel(Instr::exec_block, 2);
                        assert(Instr::exec_block(block@, 0, data, st) == Some(Regs { a: (p >> 32) as u32, ..st }));
                    }
                }
            }
            Expr::Cast(e, _) => {
                e.emit_hi(b, arch, sig, sp)?;
                proof {
                    let cty = self->Cast_1;
                    assert forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf() implies
                        #[trigger] Builder::loads(b.rev@, data, b.rev@.len(), st, base.len(),
                            self.word(arch, sig@, data, true), sp as nat) by {
                        cty.lemma_norm_trunc(arch, e.value(arch, sig@, data));
                        cty.lemma_norm_64(arch, e.pattern(arch, sig@, data));
                        assert(Builder::loads(b.rev@, data, b.rev@.len(), st, base.len(),
                            e.word(arch, sig@, data, true), sp as nat));
                    }
                }
            }
            Expr::BinOp(op, l, r) => {
                if !matches!(op, BinOp::Add | BinOp::Sub) {
                    let src = r.src(arch, true, 0);
                    let block = [Instr::Alu(op.alu(), src)];
                    proof { reveal_with_fuel(Instr::fits_from, 2); }
                    b.emit_block(&block);
                    let ghost r_op = b.rev@;
                    l.emit_operands(r, b, arch, sig, true, 0, sp)?;
                    proof {
                        assert forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf() implies
                            #[trigger] Builder::loads(b.rev@, data, b.rev@.len(), st, base.len(),
                                self.word(arch, sig@, data, true), sp as nat) by {
                            let pl = l.pattern(arch, sig@, data);
                            let pr = r.pattern(arch, sig@, data);
                            let (hl, hr) = (l.word(arch, sig@, data, true), r.word(arch, sig@, data, true));
                            self.lemma_binary_pattern(arch, sig@, data, ty);
                            ty.lemma_norm_64(arch, op.apply(pl, pr));
                            op.lemma_high(pl, pr);
                            assert(hl ^ 0u32 == hl && hr ^ 0u32 == hr) by (bit_vector);
                            assert(Builder::loads2(b.rev@, data, b.rev@.len(), st, r_op.len(), hl ^ 0, src,
                                hr ^ 0, sp as nat));
                            let t1 = choose |t1: Regs| t1.wf() && t1.a == hl ^ 0 && src.eval(t1.at(0)) == hr ^ 0
                                && t1.keeps(st, sp as nat)
                                && #[trigger] Builder::goes(b.rev@, data, b.rev@.len(), st, r_op.len(), t1);
                            let t2 = Regs { a: op.spec_alu().eval(hl, hr), ..t1 };
                            reveal_with_fuel(Instr::exec_block, 2);
                            assert(Instr::exec_block(block@, 0, data, t1) == Some(t2));
                            Builder::lemma_goes_trans(r_op, b.rev@, data, b.rev@.len(), st, r_op.len(), t1,
                                base.len(), t2);
                        }
                    }
                } else {
                    return self.emit_carry(b, arch, sig, Ghost(ty), sp);
                }
            }
        }
        Ok(())
    }

    /// Emits code that leaves the high word of this expression's pattern in `A`, when its type
    /// `ty` is at most 32 bits wide.
    ///
    /// ```text
    ///     ld  #0                  ; unsigned
    ///
    ///     <low word>              ; signed
    ///     rsh #31
    ///     neg
    /// ```
    fn emit_sext(&self, b: &mut Builder, arch: Arch, sig: &[PrimType], ty: PrimType, sp: u32)
        -> (res: Result<(), CompileError>)
        requires
            old(b).wf(), 0 < old(b).rev@.len(), sp <= 16, self.typed(arch, sig@),
            self.shaped(arch, sig@, ty), ty.bits(arch) <= 32,
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf() ==>
                #[trigger] Builder::loads(final(b).rev@, data, final(b).rev@.len(), st,
                    old(b).rev@.len(), self.word(arch, sig@, data, true), sp as nat),
        decreases self.size(), 1nat
    {
        let ghost base = b.rev@;
        let ghost t = choose |t: PrimType| self.of_type(arch, sig@, t);
        if ty.exec_signed() {
            let block = [Instr::Alu(AluOp::Rsh, Src::K(31)), Instr::Neg];
            proof { reveal_with_fuel(Instr::fits_from, 3); }
            b.emit_block(&block);
            let ghost r_sign = b.rev@;
            self.emit_lo(b, arch, sig, sp)?;
            proof {
                assert forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf() implies
                    #[trigger] Builder::loads(b.rev@, data, b.rev@.len(), st, base.len(),
                        self.word(arch, sig@, data, true), sp as nat) by {
                    let lo = self.word(arch, sig@, data, false);
                    self.lemma_unpat(arch, sig@, data, t);
                    assert(Builder::loads(b.rev@, data, b.rev@.len(), st, r_sign.len(), lo, sp as nat));
                    let t1 = choose |t1: Regs| t1.wf() && t1.a == lo && t1.keeps(st, sp as nat)
                        && #[trigger] Builder::goes(b.rev@, data, b.rev@.len(), st, r_sign.len(), t1);
                    let t2 = Regs { a: (-((lo >> 31u32) as int)) as u32, ..t1 };
                    reveal_with_fuel(Instr::exec_block, 3);
                    assert(Instr::exec_block(block@, 0, data, t1) == Some(t2));
                    Builder::lemma_goes_trans(r_sign, b.rev@, data, b.rev@.len(), st, r_sign.len(), t1,
                        base.len(), t2);
                }
            }
        } else {
            let block = [Instr::LdImm(0)];
            proof { reveal_with_fuel(Instr::fits_from, 2); }
            b.emit_block(&block);
            proof {
                assert forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf() implies
                    #[trigger] Builder::loads(b.rev@, data, b.rev@.len(), st, base.len(),
                        self.word(arch, sig@, data, true), sp as nat) by {
                    self.lemma_unpat(arch, sig@, data, t);
                    reveal_with_fuel(Instr::exec_block, 2);
                    assert(Instr::exec_block(block@, 0, data, st) == Some(Regs { a: 0, ..st }));
                }
            }
        }
        Ok(())
    }

    /// Emits code that leaves the high word of this sum's or difference's pattern in `A`,
    /// when its type `ty` is wider than 32 bits.
    ///
    /// ```text
    ///     <operands' low words>   ; add
    ///     add src
    ///     jge src -> nc           ; no carry out of the low words
    ///     ld  #1
    ///     ja  carry
    /// nc: ld  #0
    /// carry:
    ///     st  M[sp]
    ///     <operands' high words>  ; with sp + 1
    ///     add src
    ///     ldx M[sp]
    ///     add x
    ///
    ///     <operands' low words>   ; sub
    ///     jge src -> nb           ; no borrow out of the low words
    ///     ld  #1
    ///     ja  borrow
    /// nb: ld  #0
    /// borrow:
    ///     st  M[sp]
    ///     <operands' high words>  ; with sp + 1
    ///     sub src
    ///     ldx M[sp]
    ///     sub x
    /// ```
    fn emit_carry(&self, b: &mut Builder, arch: Arch, sig: &[PrimType], Ghost(ty): Ghost<PrimType>, sp: u32)
        -> (res: Result<(), CompileError>)
        requires
            old(b).wf(), 0 < old(b).rev@.len(), sp <= 16, self.typed(arch, sig@),
            self is BinOp, self->BinOp_0 is Add || self->BinOp_0 is Sub,
            self.shaped(arch, sig@, ty), ty.wf(), ty.bits(arch) > 32,
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf() ==>
                #[trigger] Builder::loads(final(b).rev@, data, final(b).rev@.len(), st,
                    old(b).rev@.len(), self.word(arch, sig@, data, true), sp as nat),
        decreases self.size(), 1nat
    {
        if sp >= 16 {
            return Err(CompileError::ScratchOverflow);
        }
        let (op, l, r) = match self {
            Expr::BinOp(op, l, r) => (*op, l, r),
            _ => unreached(),
        };
        proof { self.lemma_operands_typed(arch, sig@); }
        let ghost base = b.rev@;
        let alu = op.alu();
        let hsrc = r.src(arch, true, 0);
        let high = [Instr::Alu(alu, hsrc), Instr::LdxMem(sp), Instr::Alu(alu, Src::X)];
        proof { reveal_with_fuel(Instr::fits_from, 4); }
        b.emit_block(&high);
        let ghost r_high = b.rev@;
        l.emit_operands(r, b, arch, sig, true, 0, sp + 1)?;
        let ghost r_hops = b.rev@;
        let lsrc = r.src(arch, false, 0);
        let carry = [Instr::Jmp { op: JmpOp::Ge, src: lsrc, jt: 2, jf: 0 }, Instr::LdImm(1),
            Instr::Ja(1), Instr::LdImm(0), Instr::St(sp)];
        proof { reveal_with_fuel(Instr::fits_from, 6); }
        b.emit_block(&carry);
        let ghost r_carry = b.rev@;
        let add: &[Instr] = if op == BinOp::Add { &[Instr::Alu(AluOp::Add, lsrc)] } else { &[] };
        proof { reveal_with_fuel(Instr::fits_from, 2); }
        b.emit_block(add);
        let ghost r_add = b.rev@;
        l.emit_operands(r, b, arch, sig, false, 0, sp)?;
        proof {
            assert forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf() implies
                #[trigger] Builder::loads(b.rev@, data, b.rev@.len(), st, base.len(),
                    self.word(arch, sig@, data, true), sp as nat) by {
                let pl = l.pattern(arch, sig@, data);
                let pr = r.pattern(arch, sig@, data);
                let (l0, l1) = (l.word(arch, sig@, data, false), l.word(arch, sig@, data, true));
                let (r0, r1) = (r.word(arch, sig@, data, false), r.word(arch, sig@, data, true));
                self.lemma_binary_pattern(arch, sig@, data, ty);
                ty.lemma_norm_64(arch, op.apply(pl, pr));
                if op == BinOp::Add {
                    BinOp::lemma_add(pl, pr);
                } else {
                    BinOp::lemma_sub(pl, pr);
                }
                assert(l0 ^ 0u32 == l0 && r0 ^ 0u32 == r0 && l1 ^ 0u32 == l1 && r1 ^ 0u32 == r1)
                    by (bit_vector);
                reveal_with_fuel(Instr::exec_block, 6);
                // The low words, and the carry or borrow out of them.
                assert(Builder::loads2(b.rev@, data, b.rev@.len(), st, r_add.len(), l0 ^ 0, lsrc,
                    r0 ^ 0, sp as nat));
                let t1 = choose |t1: Regs| t1.wf() && t1.a == l0 ^ 0 && lsrc.eval(t1.at(0)) == r0 ^ 0
                    && t1.keeps(st, sp as nat)
                    && #[trigger] Builder::goes(b.rev@, data, b.rev@.len(), st, r_add.len(), t1);
                let t2 = Regs { a: if op == BinOp::Add { AluOp::Add.eval(l0, r0) } else { l0 }, ..t1 };
                assert(Instr::exec_block(add@, 0, data, t1) == Some(t2));
                let c: u32 = if t2.a >= r0 { 0 } else { 1 };
                let t3 = Regs { a: c, mem: t2.mem.update(sp as int, Some(c)), ..t2 };
                assert(Instr::exec_block(carry@, 0, data, t2) == Some(t3));
                // The high words, and the carry or borrow into them.
                assert(Builder::loads2(r_hops, data, r_hops.len(), t3, r_high.len(), l1 ^ 0, hsrc,
                    r1 ^ 0, (sp + 1) as nat));
                let t4 = choose |t4: Regs| t4.wf() && t4.a == l1 ^ 0 && hsrc.eval(t4.at(0)) == r1 ^ 0
                    && t4.keeps(t3, (sp + 1) as nat)
                    && #[trigger] Builder::goes(r_hops, data, r_hops.len(), t3, r_high.len(), t4);
                assert(t4.mem[sp as int] == Some(c));
                let t5 = Regs { a: alu.eval(alu.eval(l1, r1), c), x: c, mem: t4.mem };
                assert(Instr::exec_block(high@, 0, data, t4) == Some(t5));
                Builder::lemma_goes_trans(r_add, b.rev@, data, b.rev@.len(), st, r_add.len(), t1,
                    r_carry.len(), t2);
                Builder::lemma_goes_trans(r_carry, b.rev@, data, b.rev@.len(), st, r_carry.len(), t2,
                    r_hops.len(), t3);
                Builder::lemma_goes_trans(r_hops, b.rev@, data, b.rev@.len(), st, r_hops.len(), t3,
                    r_high.len(), t4);
                Builder::lemma_goes_trans(r_high, b.rev@, data, b.rev@.len(), st, r_high.len(), t4,
                    base.len(), t5);
                assert(t5.keeps(st, sp as nat));
            }
        }
        Ok(())
    }

    /// Emits code that leaves this expression's low or high word, flipped by `bias`, in `A`.
    ///
    /// ```text
    ///     <word>
    ///     xor #bias               ; bias != 0
    /// ```
    pub(super) fn emit_word(&self, b: &mut Builder, arch: Arch, sig: &[PrimType], hi: bool, bias: u32, sp: u32)
        -> (res: Result<(), CompileError>)
        requires old(b).wf(), 0 < old(b).rev@.len(), sp <= 16, self.typed(arch, sig@)
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf() ==>
                #[trigger] Builder::loads(final(b).rev@, data, final(b).rev@.len(), st,
                    old(b).rev@.len(), self.word(arch, sig@, data, hi) ^ bias, sp as nat),
        decreases self.size(), 3nat
    {
        let ghost base = b.rev@;
        if bias != 0 {
            b.emit(Instr::Alu(AluOp::Xor, Src::K(bias)));
            proof { Builder::lemma_alu(b.rev@, AluOp::Xor, bias); }
        }
        let ghost r_xor = b.rev@;
        if hi {
            self.emit_hi(b, arch, sig, sp)?;
        } else {
            self.emit_lo(b, arch, sig, sp)?;
        }
        proof {
            assert forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf() implies
                #[trigger] Builder::loads(b.rev@, data, b.rev@.len(), st, base.len(),
                    self.word(arch, sig@, data, hi) ^ bias, sp as nat) by {
                let w = self.word(arch, sig@, data, hi);
                assert(Builder::loads(b.rev@, data, b.rev@.len(), st, r_xor.len(), w, sp as nat));
                let t1 = choose |t1: Regs| t1.wf() && t1.a == w && t1.keeps(st, sp as nat)
                    && #[trigger] Builder::goes(b.rev@, data, b.rev@.len(), st, r_xor.len(), t1);
                let t2 = Regs { a: AluOp::Xor.eval(w, bias), ..t1 };
                if bias == 0 {
                    assert(w ^ 0u32 == w) by (bit_vector);
                    assert(t2 == t1);
                }
                assert(Builder::goes(r_xor, data, r_xor.len(), t1, base.len(), t2));
                Builder::lemma_goes_trans(r_xor, b.rev@, data, b.rev@.len(), st, r_xor.len(), t1,
                    base.len(), t2);
            }
        }
        Ok(())
    }

    /// Emits code that leaves this expression's low or high word in `A` and `other`'s where
    /// [`Expr::src`] reads it, both flipped by `bias`.
    ///
    /// ```text
    ///     <word>                  ; other is a literal, read as an immediate
    ///
    ///     <other's word>          ; otherwise, read from X
    ///     st  M[sp]
    ///     <word>                  ; with sp + 1
    ///     ldx M[sp]
    /// ```
    #[allow(clippy::too_many_arguments)]
    pub(super) fn emit_operands(&self, other: &Expr, b: &mut Builder, arch: Arch, sig: &[PrimType],
        hi: bool, bias: u32, sp: u32) -> (res: Result<(), CompileError>)
        requires
            old(b).wf(), 0 < old(b).rev@.len(), sp <= 16,
            self.typed(arch, sig@), other.typed(arch, sig@),
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf() ==>
                #[trigger] Builder::loads2(final(b).rev@, data, final(b).rev@.len(), st, old(b).rev@.len(),
                    self.word(arch, sig@, data, hi) ^ bias, other.src(arch, hi, bias),
                    other.word(arch, sig@, data, hi) ^ bias, sp as nat),
        decreases self.size() + other.size(), 2nat
    {
        let ghost base = b.rev@;
        if let Expr::Lit(..) = other {
            self.emit_word(b, arch, sig, hi, bias, sp)?;
            proof {
                assert forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf() implies
                    #[trigger] Builder::loads2(b.rev@, data, b.rev@.len(), st, base.len(),
                        self.word(arch, sig@, data, hi) ^ bias, other.src(arch, hi, bias),
                        other.word(arch, sig@, data, hi) ^ bias, sp as nat) by {
                    let w = self.word(arch, sig@, data, hi) ^ bias;
                    assert(Builder::loads(b.rev@, data, b.rev@.len(), st, base.len(), w, sp as nat));
                    let t = choose |t: Regs| t.wf() && t.a == w && t.keeps(st, sp as nat)
                        && #[trigger] Builder::goes(b.rev@, data, b.rev@.len(), st, base.len(), t);
                    assert(other.src(arch, hi, bias).eval(t.at(0)) == other.word(arch, sig@, data, hi) ^ bias);
                }
            }
            return Ok(());
        }
        if sp >= 16 {
            return Err(CompileError::ScratchOverflow);
        }
        let restore = [Instr::LdxMem(sp)];
        proof { reveal_with_fuel(Instr::fits_from, 2); }
        b.emit_block(&restore);
        let ghost r_ldx = b.rev@;
        self.emit_word(b, arch, sig, hi, bias, sp + 1)?;
        let ghost r_word = b.rev@;
        let save = [Instr::St(sp)];
        proof { reveal_with_fuel(Instr::fits_from, 2); }
        b.emit_block(&save);
        let ghost r_st = b.rev@;
        other.emit_word(b, arch, sig, hi, bias, sp)?;
        proof {
            assert forall |data: &[u8], st: Regs| Event::parse(data) is Some && st.wf() implies
                #[trigger] Builder::loads2(b.rev@, data, b.rev@.len(), st, base.len(),
                    self.word(arch, sig@, data, hi) ^ bias, other.src(arch, hi, bias),
                    other.word(arch, sig@, data, hi) ^ bias, sp as nat) by {
                let w = self.word(arch, sig@, data, hi) ^ bias;
                let v = other.word(arch, sig@, data, hi) ^ bias;
                assert(Builder::loads(b.rev@, data, b.rev@.len(), st, r_st.len(), v, sp as nat));
                let t1 = choose |t1: Regs| t1.wf() && t1.a == v && t1.keeps(st, sp as nat)
                    && #[trigger] Builder::goes(b.rev@, data, b.rev@.len(), st, r_st.len(), t1);
                reveal_with_fuel(Instr::exec_block, 2);
                let t2 = Regs { mem: t1.mem.update(sp as int, Some(v)), ..t1 };
                assert(Instr::exec_block(save@, 0, data, t1) == Some(t2));
                assert(Builder::loads(r_word, data, r_word.len(), t2, r_ldx.len(), w, (sp + 1) as nat));
                let t3 = choose |t3: Regs| t3.wf() && t3.a == w && t3.keeps(t2, (sp + 1) as nat)
                    && #[trigger] Builder::goes(r_word, data, r_word.len(), t2, r_ldx.len(), t3);
                assert(t3.mem[sp as int] == Some(v));
                let t4 = Regs { x: v, ..t3 };
                assert(Instr::exec_block(restore@, 0, data, t3) == Some(t4));
                Builder::lemma_goes_trans(r_st, b.rev@, data, b.rev@.len(), st, r_st.len(), t1,
                    r_word.len(), t2);
                Builder::lemma_goes_trans(r_word, b.rev@, data, b.rev@.len(), st, r_word.len(), t2,
                    r_ldx.len(), t3);
                Builder::lemma_goes_trans(r_ldx, b.rev@, data, b.rev@.len(), st, r_ldx.len(), t3,
                    base.len(), t4);
                assert(t4.keeps(st, sp as nat));
            }
        }
        Ok(())
    }
}

impl Expr {
    /// The value a pattern stands for, read as signed or not.
    pub(super) open spec fn unpat(p: u64, signed: bool) -> int {
        if signed && p >= 0x8000_0000_0000_0000 { p - 0x1_0000_0000_0000_0000 } else { p as int }
    }

    /// The value a word stands for, read as signed or not.
    pub(super) open spec fn unword(w: u32, signed: bool) -> int {
        if signed && w >= 0x8000_0000 { w - 0x1_0000_0000 } else { w as int }
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

    /// A value of type `t` is what its pattern, or its low word if `t` is at most 32 bits
    /// wide, reads as, signed as `t` is, and one of an unsigned type narrower than that reads
    /// alike as signed.
    pub(super) proof fn lemma_unpat(&self, arch: Arch, ctx: Seq<PrimType>, data: &[u8], t: PrimType)
        requires self.of_type(arch, ctx, t)
        ensures
            Self::unpat(Self::pat(self.value(arch, ctx, data)), t.signed()) == self.value(arch, ctx, data),
            !t.signed() && t.bits(arch) < 64 ==> Self::pat(self.value(arch, ctx, data)) < 0x8000_0000_0000_0000,
            t.bits(arch) <= 32 ==> self.value(arch, ctx, data)
                == Self::unword(self.word(arch, ctx, data, false), t.signed()),
            t.bits(arch) <= 32 ==> self.word(arch, ctx, data, true) == if t.signed() {
                (-((self.word(arch, ctx, data, false) >> 31u32) as int)) as u32
            } else { 0 },
            !t.signed() && t.bits(arch) < 32 ==> self.word(arch, ctx, data, false) < 0x8000_0000,
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

    /// A word of a bitwise and is zero exactly when its operands' words share no bit within
    /// the same word of its type's mask.
    pub(super) proof fn lemma_and_word(&self, arch: Arch, ctx: Seq<PrimType>, data: &[u8], ty: PrimType, hi: bool)
        requires
            self is BinOp, self->BinOp_0 is And,
            self.typed(arch, ctx), self.shaped(arch, ctx, ty), ty.wf(),
            hi ==> ty.bits(arch) == 64,
        ensures ({
            let mw: u32 = if hi { (ty.mask(arch) >> 32u64) as u32 } else { ty.mask(arch) as u32 };
            (self.word(arch, ctx, data, hi) == 0) == (self->BinOp_1.word(arch, ctx, data, hi)
                & (self->BinOp_2.word(arch, ctx, data, hi) & mw) == 0)
        })
    {
        self.lemma_binary_pattern(arch, ctx, data, ty);
        let pl = self->BinOp_1.pattern(arch, ctx, data);
        let pr = self->BinOp_2.pattern(arch, ctx, data);
        let q = pl & pr;
        let mask = ty.mask(arch);
        let b = ty.bits(arch);
        ty.lemma_mask(arch);
        ty.lemma_norm(arch, q);
        let p = q & mask;
        if b == 64 {
            ty.lemma_norm_64(arch, q);
            assert((q as u32 == 0) == ((pl as u32) & ((pr as u32) & (mask as u32)) == 0)
                && (((q >> 32u64) as u32 == 0)
                    == (((pl >> 32u64) as u32) & (((pr >> 32u64) as u32) & ((mask >> 32u64) as u32)) == 0)))
                by (bit_vector)
                requires q == pl & pr, mask == u64::MAX;
        } else if ty.signed() && p > mask >> 1u64 {
            // Below 32 bits the copied sign sets bits of the low word; from 32 on, the low word is `p`'s.
            assert((((p | !mask) as u32) == 0) == ((pl as u32) & ((pr as u32) & (mask as u32)) == 0))
                by (bit_vector)
                requires mask == ((1u64 << b) - 1) as u64, 8 <= b < 64, p == (pl & pr) & mask, p > mask >> 1u64;
        } else {
            assert(((p as u32) == 0) == ((pl as u32) & ((pr as u32) & (mask as u32)) == 0))
                by (bit_vector)
                requires p == (pl & pr) & mask;
        }
    }
}

impl PrimType {
    /// A value of this type is what its pattern, or its pattern's low word if the type is at
    /// most 32 bits wide, reads as, signed as this type is, and one of an unsigned type
    /// narrower than that reads alike as signed.
    pub(super) proof fn lemma_range(self, arch: Arch, x: u64)
        ensures
            Expr::unpat(Expr::pat(self.to_int(arch, x)), self.signed()) == self.to_int(arch, x),
            !self.signed() && self.bits(arch) < 64 ==> Expr::pat(self.to_int(arch, x)) < 0x8000_0000_0000_0000,
            self.bits(arch) <= 32 ==> self.to_int(arch, x)
                == Expr::unword(Expr::pat(self.to_int(arch, x)) as u32, self.signed()),
            self.bits(arch) <= 32 ==> (Expr::pat(self.to_int(arch, x)) >> 32) as u32 == if self.signed() {
                (-(((Expr::pat(self.to_int(arch, x)) as u32) >> 31u32) as int)) as u32
            } else { 0 },
            !self.signed() && self.bits(arch) < 32 ==> (Expr::pat(self.to_int(arch, x)) as u32) < 0x8000_0000,
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
        if self.bits(arch) <= 32 {
            let bits = self.bits(arch);
            self.lemma_mask(arch);
            assert(mask <= 0xFFFF_FFFF && mask - half <= 0x8000_0000 && half < 0x8000_0000
                && (bits < 32 ==> mask < 0x8000_0000)) by (bit_vector)
                requires bits <= 32, mask == ((1u64 << bits) - 1) as u64, half == mask >> 1u64;
            let pv = Expr::pat(v);
            let lo = pv as u32;
            Expr::lemma_words(pv);
            if v < 0 {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(pv as int, 0x1_0000_0000,
                    0xFFFF_FFFF, v + 0x1_0000_0000);
            } else {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(pv as int, 0x1_0000_0000, 0, v);
            }
            assert(lo < 0x8000_0000 ==> (-((lo >> 31u32) as int)) as u32 == 0) by (bit_vector);
            assert(lo >= 0x8000_0000 ==> (-((lo >> 31u32) as int)) as u32 == 0xFFFF_FFFF) by (bit_vector);
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

    /// The high word of this bitwise operation's pattern is the ALU's result on the high
    /// words.
    proof fn lemma_high(self, pl: u64, pr: u64)
        requires !(self is Add), !(self is Sub)
        ensures self.spec_alu().eval((pl >> 32u64) as u32, (pr >> 32u64) as u32) == (self.apply(pl, pr) >> 32u64) as u32
    {
        let (l1, r1) = ((pl >> 32u64) as u32, (pr >> 32u64) as u32);
        assert(((pl & pr) >> 32u64) as u32 == l1 & r1 && ((pl | pr) >> 32u64) as u32 == l1 | r1
            && ((pl ^ pr) >> 32u64) as u32 == l1 ^ r1) by (bit_vector)
            requires l1 == (pl >> 32u64) as u32, r1 == (pr >> 32u64) as u32;
    }

    /// The high word of a sum's pattern adds the high words and the carry out of the low
    /// words.
    proof fn lemma_add(pl: u64, pr: u64)
        ensures ({
            let (l0, l1, r0, r1) = (pl as u32, (pl >> 32u64) as u32, pr as u32, (pr >> 32u64) as u32);
            let c: u32 = if AluOp::Add.eval(l0, r0) >= r0 { 0 } else { 1 };
            (BinOp::Add.apply(pl, pr) >> 32u64) as u32 == AluOp::Add.eval(AluOp::Add.eval(l1, r1), c)
        })
    {
        let m32 = 0x1_0000_0000int;
        let (l0, l1, r0, r1) = (pl as u32, (pl >> 32u64) as u32, pr as u32, (pr >> 32u64) as u32);
        let lo = AluOp::Add.eval(l0, r0);
        let c: u32 = if lo >= r0 { 0 } else { 1 };
        let w = BinOp::Add.apply(pl, pr);
        Expr::lemma_words(pl);
        Expr::lemma_words(pr);
        Expr::lemma_words(w);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(pl as int, m32);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(pr as int, m32);
        AluOp::lemma_wrap(l0, r0);
        let carry: int = if l0 + r0 >= m32 { 1 } else { 0 };
        let low = l0 + r0 - carry * m32;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(l0 + r0, m32, carry, low);
        assert(c == carry);
        let t = AluOp::Add.eval(l1, r1);
        AluOp::lemma_wrap(l1, r1);
        AluOp::lemma_wrap(t, c);
        vstd::arithmetic::div_mod::lemma_add_mod_noop(l1 + r1, c as int, m32);
        vstd::arithmetic::div_mod::lemma_small_mod(c as nat, m32 as nat);
        vstd::arithmetic::div_mod::lemma_mod_twice(l1 + r1, m32);
        assert(pl + pr == (l1 + r1 + carry) * m32 + low);
        Expr::lemma_halves(l1 + r1 + carry, low);
    }

    /// The high word of a difference's pattern takes the borrow out of the low words from
    /// the difference of the high words.
    proof fn lemma_sub(pl: u64, pr: u64)
        ensures ({
            let (l0, l1, r0, r1) = (pl as u32, (pl >> 32u64) as u32, pr as u32, (pr >> 32u64) as u32);
            let bw: u32 = if l0 >= r0 { 0 } else { 1 };
            (BinOp::Sub.apply(pl, pr) >> 32u64) as u32 == AluOp::Sub.eval(AluOp::Sub.eval(l1, r1), bw)
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
        let low = l0 - r0 + bw * m32;
        let t = AluOp::Sub.eval(l1, r1);
        AluOp::lemma_wrap(l1, r1);
        AluOp::lemma_wrap(t, bw);
        vstd::arithmetic::div_mod::lemma_sub_mod_noop(l1 - r1, bw as int, m32);
        vstd::arithmetic::div_mod::lemma_small_mod(bw as nat, m32 as nat);
        vstd::arithmetic::div_mod::lemma_mod_twice(l1 - r1, m32);
        assert(pl - pr == (l1 - r1 - bw) * m32 + low);
        Expr::lemma_halves(l1 - r1 - bw, low);
    }
}

} // verus!
