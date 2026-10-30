-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegAttKeyKit.lean: the arrays of the attention segment as affine forms (over the algebra of
Cm/SegAlg.lean), and tools for its families.

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean). A trace is a function on the names of cells (`Raw`,
Inst/Model/Att/Trace.lean); `Raw.Valid` says which names are cells.

Main names:
  `tAtt g A`: the cell c is the entry of the matrices A at the place of its owner (`ownAtt`,
    Cm/SegLayout.lean; qry, out, key, val are in the feed-forward segment of the group).
  `cr0` to `cval`: the arrays of Inst/Model/Att/Trace.lean (`AttSeg.r0`, .., `AttSeg.valV`) as
    forms, each with its value (simp) and with "it reads places of valid cells" (`InAtt`), at
    indices in range.
  `Agree t t'`: two traces agree on the valid names; the arrays at valid indices then agree
    (`r0_agree`, ..).
  `bOf`, `yOf`: a vertex B = b · 2^l + y; it is live if b is one of the 20 pairs (layer, number of
    the query head among those of its key/value head: `AttSeg.Dim.nb`).
  `iff_of_val`: for nb ≤ 2^a live numbers b and a set S that has the padding value, from "the value
    at B is K b y if B is live and the padding value if not" to "all values on the cube are in S ⇔
    all K b y are".
Terms: lean/GLOSSARY.md.
-/
import Cm.SegHeadExp
import Cm.SegLayoutProofs
import Inst.Model.Att.Trace

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Inst.Model Inst.Model.All Finset
open Inst.Model.AttSeg (Raw Reg)

/-- the sizes of the attention segment at u0 live rows of the exponential; all sizes but u0 are the
reference sizes -/
abbrev DU (u0 : ℕ) : AttSeg.Dim := AttSeg.Dim.refK u0

section Forms
variable {E : Type} [Field E] (g : ℕ)

/-- The matrices, read as a trace of the attention segment of group g. -/
def tAtt (A : ℕ → ℕ → ℕ → E) : Raw → E := fun c =>
  A (ownAtt g c).place.1 (ownAtt g c).place.2.1 (ownAtt g c).place.2.2

/-- one cell -/
def cRaw (c : Raw) : CForm E := cAt (ownAtt g c).place

def cr0 (ρ : Reg) (b x : ℕ) : CForm E := cRaw g (.c ρ 0 b x) + cK 128
def cr1 (ρ : Reg) (b x : ℕ) : CForm E := cRaw g (.c ρ 1 b x) + cK 128
def cfl (ρ : Reg) (b x : ℕ) : CForm E := cRaw g (.c ρ 2 b x)
def cw0 (ρ : Reg) (b x : ℕ) : CForm E := cRaw g (.c ρ 3 b x) + cK 128
def cw1 (ρ : Reg) (b x : ℕ) : CForm E := cRaw g (.c ρ 4 b x)
def crm (ρ : Reg) (b x : ℕ) : CForm E := cr0 g ρ b x + (256 : E) • cr1 g ρ b x
def cwt (ρ : Reg) (b x : ℕ) : CForm E := cw0 g ρ b x + (256 : E) • cw1 g ρ b x
def cmx (b h i : ℕ) : CForm E := cSum 4 fun k => ((256 : E) ^ k) • cRaw g (.mx k b h i)
def cden (b h i : ℕ) : CForm E := cSum 4 fun k => ((256 : E) ^ k) • cRaw g (.den k b h i)
def cib (k b h i : ℕ) : CForm E := cRaw g (.ib k b h i)
def cqh (b h i n : ℕ) : CForm E := cRaw g (.qh b h i n) + cK 128
def cqh' (b h i n : ℕ) : CForm E := cRaw g (.qh' b h i n) + cK 128
def cqry (b h i n : ℕ) : CForm E := cSum 2 fun k => ((256 : E) ^ k) • cRaw g (.qry k b h i n)
def cout (b h i n : ℕ) : CForm E := cSum 2 fun k => ((256 : E) ^ k) • cRaw g (.out k b h i n)
def ckey (lam h j n : ℕ) : CForm E := cSum 2 fun k => ((256 : E) ^ k) • cRaw g (.key k lam h j n)
def cval (lam h j n : ℕ) : CForm E := cSum 2 fun k => ((256 : E) ^ k) • cRaw g (.val k lam h j n)

variable (A : ℕ → ℕ → ℕ → E)

@[simp] theorem val_cRaw (c : Raw) : (cRaw g c : CForm E).val A = tAtt g A c := val_cAt A _
@[simp] theorem val_cr0 (ρ : Reg) (b x : ℕ) :
    (cr0 g ρ b x : CForm E).val A = AttSeg.r0 (tAtt g A) ρ b x := by
  simp [cr0, AttSeg.r0]
@[simp] theorem val_cr1 (ρ : Reg) (b x : ℕ) :
    (cr1 g ρ b x : CForm E).val A = AttSeg.r1 (tAtt g A) ρ b x := by
  simp [cr1, AttSeg.r1]
@[simp] theorem val_cfl (ρ : Reg) (b x : ℕ) :
    (cfl g ρ b x : CForm E).val A = AttSeg.flV (tAtt g A) ρ b x := by
  simp [cfl, AttSeg.flV]
@[simp] theorem val_cw0 (ρ : Reg) (b x : ℕ) :
    (cw0 g ρ b x : CForm E).val A = AttSeg.w0 (tAtt g A) ρ b x := by
  simp [cw0, AttSeg.w0]
@[simp] theorem val_cw1 (ρ : Reg) (b x : ℕ) :
    (cw1 g ρ b x : CForm E).val A = AttSeg.w1 (tAtt g A) ρ b x := by
  simp [cw1, AttSeg.w1]
@[simp] theorem val_crm (ρ : Reg) (b x : ℕ) :
    (crm g ρ b x : CForm E).val A = AttSeg.rm (tAtt g A) ρ b x := by
  simp [crm, AttSeg.rm]
@[simp] theorem val_cwt (ρ : Reg) (b x : ℕ) :
    (cwt g ρ b x : CForm E).val A = AttSeg.wtV (tAtt g A) ρ b x := by
  simp [cwt, AttSeg.wtV]
@[simp] theorem val_cmx (b h i : ℕ) :
    (cmx g b h i : CForm E).val A = AttSeg.mxV (tAtt g A) b h i := by
  simp [cmx, AttSeg.mxV]
@[simp] theorem val_cden (b h i : ℕ) :
    (cden g b h i : CForm E).val A = AttSeg.denV (tAtt g A) b h i := by
  simp [cden, AttSeg.denV]
@[simp] theorem val_cib (k b h i : ℕ) :
    (cib g k b h i : CForm E).val A = AttSeg.ibV (tAtt g A) k b h i := by
  simp [cib, AttSeg.ibV]
@[simp] theorem val_cqh (b h i n : ℕ) :
    (cqh g b h i n : CForm E).val A = AttSeg.qhV (tAtt g A) b h i n := by
  simp [cqh, AttSeg.qhV]
@[simp] theorem val_cqh' (b h i n : ℕ) :
    (cqh' g b h i n : CForm E).val A = AttSeg.qhV' (tAtt g A) b h i n := by
  simp [cqh', AttSeg.qhV']
@[simp] theorem val_cqry (b h i n : ℕ) :
    (cqry g b h i n : CForm E).val A = AttSeg.qryV (tAtt g A) b h i n := by
  simp [cqry, AttSeg.qryV]
@[simp] theorem val_cout (b h i n : ℕ) :
    (cout g b h i n : CForm E).val A = AttSeg.outV (tAtt g A) b h i n := by
  simp [cout, AttSeg.outV]
@[simp] theorem val_ckey (lam h j n : ℕ) :
    (ckey g lam h j n : CForm E).val A = AttSeg.keyV (tAtt g A) lam h j n := by
  simp [ckey, AttSeg.keyV]
@[simp] theorem val_cval (lam h j n : ℕ) :
    (cval g lam h j n : CForm E).val A = AttSeg.valV (tAtt g A) lam h j n := by
  simp [cval, AttSeg.valV]

/-- the place of a valid cell that the attention segment of group g reads -/
def IsAtt (p : Cb.Place) : Prop := ∃ c : Raw, c.Valid DA ∧ p = (ownAtt g c).place
abbrev InAtt (f : CForm E) : Prop := AllPl (IsAtt g) f

theorem isAtt_reads (h : Hd) (hg : g < nGr) {p : Cb.Place} (hp : IsAtt g p) :
    p ∈ reads h (2 * g + 1) := by
  obtain ⟨c, hc, rfl⟩ := hp
  exact Or.inr (Or.inl ⟨g, c, rfl, hg, hc, rfl⟩)

theorem inAtt_cRaw {c : Raw} (hc : c.Valid DA) : InAtt g (cRaw g c : CForm E) :=
  AllPl.cAt ⟨c, hc, rfl⟩

section
variable {ρ : Reg} {b x h i n k lam j : ℕ}
theorem inAtt_cr0 (hb : b < DA.nb) (hx : x < 2 ^ DA.lReg ρ) : InAtt g (cr0 g ρ b x : CForm E) :=
  (inAtt_cRaw g (c := .c ρ 0 b x) ⟨by norm_num, hb, hx⟩).add (.cK _)
theorem inAtt_cr1 (hb : b < DA.nb) (hx : x < 2 ^ DA.lReg ρ) : InAtt g (cr1 g ρ b x : CForm E) :=
  (inAtt_cRaw g (c := .c ρ 1 b x) ⟨by norm_num, hb, hx⟩).add (.cK _)
theorem inAtt_cfl (hb : b < DA.nb) (hx : x < 2 ^ DA.lReg ρ) : InAtt g (cfl g ρ b x : CForm E) :=
  inAtt_cRaw g (c := .c ρ 2 b x) ⟨by norm_num, hb, hx⟩
theorem inAtt_cw0 (hb : b < DA.nb) (hx : x < 2 ^ DA.lReg ρ) : InAtt g (cw0 g ρ b x : CForm E) :=
  (inAtt_cRaw g (c := .c ρ 3 b x) ⟨by norm_num, hb, hx⟩).add (.cK _)
theorem inAtt_cw1 (hb : b < DA.nb) (hx : x < 2 ^ DA.lReg ρ) : InAtt g (cw1 g ρ b x : CForm E) :=
  inAtt_cRaw g (c := .c ρ 4 b x) ⟨by norm_num, hb, hx⟩
theorem inAtt_crm (hb : b < DA.nb) (hx : x < 2 ^ DA.lReg ρ) : InAtt g (crm g ρ b x : CForm E) :=
  (inAtt_cr0 g hb hx).add ((inAtt_cr1 g hb hx).smul _)
theorem inAtt_cwt (hb : b < DA.nb) (hx : x < 2 ^ DA.lReg ρ) : InAtt g (cwt g ρ b x : CForm E) :=
  (inAtt_cw0 g hb hx).add ((inAtt_cw1 g hb hx).smul _)
theorem inAtt_cmx (hb : b < DA.nb) (hh : h < DA.nG) (hi : i < DA.T) :
    InAtt g (cmx g b h i : CForm E) :=
  AllPl.cSum fun _ hk => (inAtt_cRaw g (c := .mx _ b h i) ⟨hk, hb, hh, hi⟩).smul _
theorem inAtt_cden (hb : b < DA.nb) (hh : h < DA.nG) (hi : i < DA.T) :
    InAtt g (cden g b h i : CForm E) :=
  AllPl.cSum fun _ hk => (inAtt_cRaw g (c := .den _ b h i) ⟨hk, hb, hh, hi⟩).smul _
theorem inAtt_cib (hk : k < DA.lT) (hb : b < DA.nb) (hh : h < DA.nG) (hi : i < DA.T) :
    InAtt g (cib g k b h i : CForm E) :=
  inAtt_cRaw g (c := .ib k b h i) ⟨hk, hb, hh, hi⟩
theorem inAtt_cqh (hb : b < DA.nb) (hh : h < DA.nG) (hi : i < DA.T) (hn : n < DA.ch) :
    InAtt g (cqh g b h i n : CForm E) :=
  (inAtt_cRaw g (c := .qh b h i n) ⟨hb, hh, hi, hn⟩).add (.cK _)
theorem inAtt_cqh' (hb : b < DA.nb) (hh : h < DA.nG) (hi : i < DA.T) (hn : n < DA.ch) :
    InAtt g (cqh' g b h i n : CForm E) :=
  (inAtt_cRaw g (c := .qh' b h i n) ⟨hb, hh, hi, hn⟩).add (.cK _)
theorem inAtt_cqry (hb : b < DA.nb) (hh : h < DA.nG) (hi : i < DA.T) (hn : n < DA.ch) :
    InAtt g (cqry g b h i n : CForm E) :=
  AllPl.cSum fun _ hk => (inAtt_cRaw g (c := .qry _ b h i n) ⟨hk, hb, hh, hi, hn⟩).smul _
theorem inAtt_cout (hb : b < DA.nb) (hh : h < DA.nG) (hi : i < DA.T) (hn : n < DA.ch) :
    InAtt g (cout g b h i n : CForm E) :=
  AllPl.cSum fun _ hk => (inAtt_cRaw g (c := .out _ b h i n) ⟨hk, hb, hh, hi, hn⟩).smul _
theorem inAtt_ckey (hl : lam < DA.nl) (hh : h < DA.nG) (hj : j < DA.T) (hn : n < DA.ch) :
    InAtt g (ckey g lam h j n : CForm E) :=
  AllPl.cSum fun _ hk => (inAtt_cRaw g (c := .key _ lam h j n) ⟨hk, hl, hh, hj, hn⟩).smul _
theorem inAtt_cval (hl : lam < DA.nl) (hh : h < DA.nG) (hj : j < DA.T) (hn : n < DA.ch) :
    InAtt g (cval g lam h j n : CForm E) :=
  AllPl.cSum fun _ hk => (inAtt_cRaw g (c := .val _ lam h j n) ⟨hk, hl, hh, hj, hn⟩).smul _
end

end Forms

/-! ## Traces that agree on the valid names -/

section Agree
variable {R : Type} [CommRing R] {t t' : Raw → R}

/-- two traces agree on the valid names -/
def Agree (t t' : Raw → R) : Prop := ∀ c : Raw, c.Valid DA → t c = t' c

variable (H : Agree t t') {ρ : Reg} {b x h i n k lam j : ℕ}
include H
theorem r0_agree (hb : b < DA.nb) (hx : x < 2 ^ DA.lReg ρ) :
    AttSeg.r0 t ρ b x = AttSeg.r0 t' ρ b x := by
  unfold AttSeg.r0; rw [H (.c ρ 0 b x) ⟨by norm_num, hb, hx⟩]
theorem r1_agree (hb : b < DA.nb) (hx : x < 2 ^ DA.lReg ρ) :
    AttSeg.r1 t ρ b x = AttSeg.r1 t' ρ b x := by
  unfold AttSeg.r1; rw [H (.c ρ 1 b x) ⟨by norm_num, hb, hx⟩]
theorem fl_agree (hb : b < DA.nb) (hx : x < 2 ^ DA.lReg ρ) :
    AttSeg.flV t ρ b x = AttSeg.flV t' ρ b x :=
  H (.c ρ 2 b x) ⟨by norm_num, hb, hx⟩
theorem w0_agree (hb : b < DA.nb) (hx : x < 2 ^ DA.lReg ρ) :
    AttSeg.w0 t ρ b x = AttSeg.w0 t' ρ b x := by
  unfold AttSeg.w0; rw [H (.c ρ 3 b x) ⟨by norm_num, hb, hx⟩]
theorem w1_agree (hb : b < DA.nb) (hx : x < 2 ^ DA.lReg ρ) :
    AttSeg.w1 t ρ b x = AttSeg.w1 t' ρ b x :=
  H (.c ρ 4 b x) ⟨by norm_num, hb, hx⟩
theorem rm_agree (hb : b < DA.nb) (hx : x < 2 ^ DA.lReg ρ) :
    AttSeg.rm t ρ b x = AttSeg.rm t' ρ b x := by
  unfold AttSeg.rm; rw [r0_agree H hb hx, r1_agree H hb hx]
theorem wt_agree (hb : b < DA.nb) (hx : x < 2 ^ DA.lReg ρ) :
    AttSeg.wtV t ρ b x = AttSeg.wtV t' ρ b x := by
  unfold AttSeg.wtV; rw [w0_agree H hb hx, w1_agree H hb hx]
theorem mx_agree (hb : b < DA.nb) (hh : h < DA.nG) (hi : i < DA.T) :
    AttSeg.mxV t b h i = AttSeg.mxV t' b h i :=
  sum_congr rfl fun k hk => by rw [H (.mx k b h i) ⟨mem_range.1 hk, hb, hh, hi⟩]
theorem den_agree (hb : b < DA.nb) (hh : h < DA.nG) (hi : i < DA.T) :
    AttSeg.denV t b h i = AttSeg.denV t' b h i :=
  sum_congr rfl fun k hk => by rw [H (.den k b h i) ⟨mem_range.1 hk, hb, hh, hi⟩]
theorem ib_agree (hk : k < DA.lT) (hb : b < DA.nb) (hh : h < DA.nG) (hi : i < DA.T) :
    AttSeg.ibV t k b h i = AttSeg.ibV t' k b h i :=
  H (.ib k b h i) ⟨hk, hb, hh, hi⟩
theorem qh_agree (hb : b < DA.nb) (hh : h < DA.nG) (hi : i < DA.T) (hn : n < DA.ch) :
    AttSeg.qhV t b h i n = AttSeg.qhV t' b h i n := by
  unfold AttSeg.qhV; rw [H (.qh b h i n) ⟨hb, hh, hi, hn⟩]
theorem qh'_agree (hb : b < DA.nb) (hh : h < DA.nG) (hi : i < DA.T) (hn : n < DA.ch) :
    AttSeg.qhV' t b h i n = AttSeg.qhV' t' b h i n := by
  unfold AttSeg.qhV'; rw [H (.qh' b h i n) ⟨hb, hh, hi, hn⟩]
theorem qry_agree (hb : b < DA.nb) (hh : h < DA.nG) (hi : i < DA.T) (hn : n < DA.ch) :
    AttSeg.qryV t b h i n = AttSeg.qryV t' b h i n :=
  sum_congr rfl fun k hk => by rw [H (.qry k b h i n) ⟨mem_range.1 hk, hb, hh, hi, hn⟩]
theorem out_agree (hb : b < DA.nb) (hh : h < DA.nG) (hi : i < DA.T) (hn : n < DA.ch) :
    AttSeg.outV t b h i n = AttSeg.outV t' b h i n :=
  sum_congr rfl fun k hk => by rw [H (.out k b h i n) ⟨mem_range.1 hk, hb, hh, hi, hn⟩]
theorem key_agree (hl : lam < DA.nl) (hh : h < DA.nG) (hj : j < DA.T) (hn : n < DA.ch) :
    AttSeg.keyV t lam h j n = AttSeg.keyV t' lam h j n :=
  sum_congr rfl fun k hk => by rw [H (.key k lam h j n) ⟨mem_range.1 hk, hl, hh, hj, hn⟩]
theorem val_agree (hl : lam < DA.nl) (hh : h < DA.nG) (hj : j < DA.T) (hn : n < DA.ch) :
    AttSeg.valV t lam h j n = AttSeg.valV t' lam h j n :=
  sum_congr rfl fun k hk => by rw [H (.val k lam h j n) ⟨mem_range.1 hk, hl, hh, hj, hn⟩]

end Agree

/-! ## Vertices B = b · 2^l + y -/

/-- the pair b and the inner index y of a vertex -/
def bOf (l B : ℕ) : ℕ := B / 2 ^ l
def yOf (l B : ℕ) : ℕ := B % 2 ^ l

theorem yOf_lt (l B : ℕ) : yOf l B < 2 ^ l := Nat.mod_lt _ (Nat.two_pow_pos l)
theorem bOf_enc {l b y : ℕ} (hy : y < 2 ^ l) : bOf l (b * 2 ^ l + y) = b :=
  (AttSeg.Dim.div_step (Nat.two_pow_pos l) hy).1
theorem yOf_enc {l b y : ℕ} (hy : y < 2 ^ l) : yOf l (b * 2 ^ l + y) = y :=
  (AttSeg.Dim.div_step (Nat.two_pow_pos l) hy).2
theorem enc_lt {a l b y : ℕ} (hb : b < 2 ^ a) (hy : y < 2 ^ l) : b * 2 ^ l + y < 2 ^ (a + l) := by
  rw [pow_add]
  nlinarith [Nat.two_pow_pos l]

/-- From the values at the vertices to the condition on the cube. nb ≤ 2^a of the numbers b are
live. (not all hypotheses are named here: see the statement below) -/
theorem iff_of_val {E : Type} {a l nb : ℕ} (hnb : nb ≤ 2 ^ a) (f : ℕ → E) (K : ℕ → ℕ → E)
    (pad : E) (hf : ∀ B, f B = if bOf l B < nb then K (bOf l B) (yOf l B) else pad)
    (S : Set E) (hS : pad ∈ S) :
    (∀ B < 2 ^ (a + l), f B ∈ S) ↔ ∀ b < nb, ∀ y < 2 ^ l, K b y ∈ S := by
  constructor
  · intro h b hb y hy
    have h1 := h _ (enc_lt (lt_of_lt_of_le hb hnb) hy)
    rw [hf, bOf_enc hy, yOf_enc hy, if_pos hb] at h1
    exact h1
  · intro h B _
    rw [hf]
    split_ifs with hb
    · exact h _ hb _ (yOf_lt l B)
    · exact hS

/-- a sum over w further variables, written through the parts of the vertex number -/
theorem sum_dec {M : Type} [AddCommMonoid M] (w B : ℕ) (F : ℕ → ℕ → M) :
    ∑ j ∈ range (2 ^ w), F (bOf w (B * 2 ^ w + j)) (yOf w (B * 2 ^ w + j)) =
      ∑ j ∈ range (2 ^ w), F B j :=
  sum_congr rfl fun j hj => by rw [bOf_enc (mem_range.1 hj), yOf_enc (mem_range.1 hj)]

/-- a double sum as one sum -/
theorem sum_pair {M : Type} [AddCommMonoid M] (w : ℕ) (F : ℕ → ℕ → M) :
    ∀ n : ℕ,
      ∑ J ∈ range (n * 2 ^ w), F (bOf w J) (yOf w J) = ∑ a ∈ range n, ∑ j ∈ range (2 ^ w), F a j
  | 0 => by simp
  | n + 1 => by
    rw [Nat.succ_mul, sum_range_add, sum_pair w F n, sum_range_succ]
    congr 1
    exact sum_congr rfl fun j hj => by rw [bOf_enc (mem_range.1 hj), yOf_enc (mem_range.1 hj)]

end Cm.Seg
