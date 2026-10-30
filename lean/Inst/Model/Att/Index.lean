-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/Att/Index.lean: index arithmetic of an attention segment: its sizes, and the two
  regions in which the causal pairs of positions are arranged.

  An attention segment is one of the 25 segments of a slot's front reduction
  (slot, front: lean/GLOSSARY.md). It proves the attention step of its layers: scores,
  weights and weighted sums. Its sizes are a parameter, `Dim`, so that small instances can be
  evaluated. `Dim.ref` are the reference parameters: 8 key/value heads, 5 query heads for each, 4
  layers in a segment, 16 blocks of 64 positions, 128 channels.

  The input shift sh of the exponential is not a size. `D.sh` is written as if it were a field, but
  it is read from the table of scales of the segment (Inst/Model/Scl.lean: the field sh of the
  segment's first layer), which is passed along silently as `[scl : Scl]`. So no type, shape or
  count that is made from D can depend on it. The number u0 of live rows of the table Exp is a field
  of D.

  Only the pairs of blocks (I, J) with J ≤ I contain pairs of positions j ≤ i.
  * Region M holds the pairs with J < I, arranged as a rectangle of pairs (P, s), P < hP, s < 2 hP:
    (P, s) represents (I, J) = (P, s) if s < P and (2 hP - 1 - P, s - P) if P ≤ s < 2 hP - 1. The
    pairs with s = 2 hP - 1 represent no blocks: their entries are the empty entries.
  * Region D holds the diagonal pairs J = I. Its entries with j' > i' are the masked entries.
  An entry of a region is a tuple (g | P | s | i' | j') in M or (g | I | i' | j') in D. `codeM` and
  `codeD` write it as a number, most significant part first. In this file's Lean names (`slotP`,
  `blk_of_slot`) a slot is a pair (P, s).

  Difference from the implementation: a segment has one shift sh; the implementation allows several.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Inst.Model.Scl

set_option autoImplicit false

namespace Inst.Model.AttSeg

open Finset

/-- The sizes of an attention segment. lg, lP, lB, ln are numbers of bits. -/
structure Dim where
  /-- 2^lg key/value heads -/
  lg : ℕ
  /-- 2^lP rows P of region M; there are 2^(lP+1) blocks of positions -/
  lP : ℕ
  /-- 2^lB positions in a block -/
  lB : ℕ
  /-- 2^ln channels of a head -/
  ln : ℕ
  /-- query heads for each key/value head -/
  na : ℕ
  /-- layers in a segment -/
  nl : ℕ
  /-- the number of live rows of the table Exp: at a gap of 2^sh u0 or more the weight is 0 -/
  u0 : ℕ

/-- the reference parameters; the table Exp has 2,307 live rows -/
def Dim.ref : Dim := ⟨3, 3, 6, 7, 5, 4, 2307⟩

/-- the input shift of the exponential: 2^sh units of a score are one step of the table Exp. There
is one value for the layers of a segment: that of its first layer in the scales. It does not depend
on D -/
abbrev Dim.sh [scl : Scl] (_D : Dim) : ℕ := (scl.κ 0).sh

/-- the parameters of layer l of the segment: the reference sizes, with the scales of that layer -/
abbrev refP [scl : Scl] (l : ℕ) : Params := ppref.at (scl.κ l)

namespace Dim
variable (D : Dim)

/-- key/value heads g -/
def nG : ℕ := 2 ^ D.lg
/-- rows P of region M -/
def hP : ℕ := 2 ^ D.lP
/-- blocks I, J of positions; s also runs below nBlk -/
def nBlk : ℕ := 2 * D.hP
/-- positions i', j' in a block -/
def B : ℕ := 2 ^ D.lB
/-- positions i, j -/
def T : ℕ := D.nBlk * D.B
/-- channels n -/
def ch : ℕ := 2 ^ D.ln
/-- pairs b = na λ + a of a layer λ of the segment and the number a of a query head among those of
its key/value head -/
def nb : ℕ := D.nl * D.na
/-- bits of a position -/
def lT : ℕ := D.lP + 1 + D.lB
/-- λ(b) -/
def lamOf (b : ℕ) : ℕ := b / D.na
/-- a(b) -/
def aOf (b : ℕ) : ℕ := b % D.na
/-- the query head h = na g + a(b) that reads key/value head g -/
def head (g b : ℕ) : ℕ := D.na * g + D.aOf b

theorem T_eq : D.T = 2 ^ D.lT := by
  unfold T nBlk hP B lT
  rw [pow_add, pow_add]
  ring

theorem hP_pos : 0 < D.hP := Nat.two_pow_pos _
theorem B_pos : 0 < D.B := Nat.two_pow_pos _

/-! ## Region M: pairs (P, s) and pairs of blocks -/

/-- I(P, s) -/
def rowBlk (P s : ℕ) : ℕ := if s < P then P else D.nBlk - 1 - P
/-- J(P, s) -/
def colBlk (_D : Dim) (P s : ℕ) : ℕ := if s < P then s else s - P
/-- the P of the pair (P, s) that represents the pair of blocks (I, J), J < I -/
def slotP (I : ℕ) : ℕ := if I < D.hP then I else D.nBlk - 1 - I
/-- the s of that pair -/
def slotS (I J : ℕ) : ℕ := if I < D.hP then J else J + (D.nBlk - 1 - I)

/-- A pair (P, s) with P < hP and s < 2 hP - 1 represents a pair of blocks with J < I < nBlk, and
`slotP`, `slotS` give (P, s) back. -/
theorem blk_of_slot {P s : ℕ} (hP : P < D.hP) (hs : s < D.nBlk - 1) :
    D.colBlk P s < D.rowBlk P s ∧
    D.rowBlk P s < D.nBlk ∧
    D.slotP (D.rowBlk P s) = P ∧
    D.slotS (D.rowBlk P s) (D.colBlk P s) = s := by
  unfold colBlk rowBlk slotP slotS nBlk at *
  generalize D.hP = h at *
  refine ⟨?_, ?_, ?_, ?_⟩ <;> split_ifs <;> omega

/-- Every pair of blocks with J < I < nBlk is represented by the pair (`slotP`, `slotS`), which has
P < hP and s < 2 hP - 1. -/
theorem slot_of_blk {I J : ℕ} (hJ : J < I) (hI : I < D.nBlk) :
    D.slotP I < D.hP ∧
    D.slotS I J < D.nBlk - 1 ∧
    D.rowBlk (D.slotP I) (D.slotS I J) = I ∧
    D.colBlk (D.slotP I) (D.slotS I J) = J := by
  unfold colBlk rowBlk slotP slotS nBlk at *
  generalize D.hP = h at *
  refine ⟨?_, ?_, ?_, ?_⟩ <;> split_ifs <;> omega

/-- For I < nBlk: the sum, over the pairs (P, s) with s < 2 hP - 1 whose row block is I, of a
function of the column block is the sum over the blocks J < I. -/
theorem sum_slots {M : Type} [AddCommMonoid M] {I : ℕ} (hI : I < D.nBlk) (G : ℕ → M) :
    (∑ P ∈ range D.hP, ∑ s ∈ range (D.nBlk - 1), if D.rowBlk P s = I then G (D.colBlk P s) else 0) =
      ∑ J ∈ range I, G J := by
  rw [← sum_product', ← sum_filter]
  refine sum_nbij' (fun x => D.colBlk x.1 x.2) (fun J => (D.slotP I, D.slotS I J)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_filter, mem_product, mem_range, mem_range] at hx
    have h := D.blk_of_slot hx.1.1 hx.1.2
    rw [mem_range, ← hx.2]
    exact h.1
  · intro J hJ
    have h := D.slot_of_blk (mem_range.mp hJ) hI
    rw [mem_filter, mem_product, mem_range, mem_range]
    exact ⟨⟨h.1, h.2.1⟩, h.2.2.1⟩
  · intro x hx
    rw [mem_filter, mem_product, mem_range, mem_range] at hx
    have h := D.blk_of_slot hx.1.1 hx.1.2
    rw [hx.2] at h
    exact Prod.ext h.2.2.1 h.2.2.2
  · intro J hJ
    exact (D.slot_of_blk (mem_range.mp hJ) hI).2.2.2
  · intro x _
    rfl

/-- `sum_slots` for a function of the pair (P, s) itself: for I < nBlk it is summed at the pairs
that represent (I, J), J < I. -/
theorem sum_slots2 {M : Type} [AddCommMonoid M] {I : ℕ} (hI : I < D.nBlk) (G : ℕ → ℕ → M) :
    (∑ P ∈ range D.hP, ∑ s ∈ range (D.nBlk - 1), if D.rowBlk P s = I then G P s else 0) =
      ∑ J ∈ range I, G (D.slotP I) (D.slotS I J) := by
  rw [← sum_product', ← sum_filter]
  refine sum_nbij' (fun x => D.colBlk x.1 x.2) (fun J => (D.slotP I, D.slotS I J)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_filter, mem_product, mem_range, mem_range] at hx
    have h := D.blk_of_slot hx.1.1 hx.1.2
    rw [mem_range, ← hx.2]
    exact h.1
  · intro J hJ
    have h := D.slot_of_blk (mem_range.mp hJ) hI
    rw [mem_filter, mem_product, mem_range, mem_range]
    exact ⟨⟨h.1, h.2.1⟩, h.2.2.1⟩
  · intro x hx
    rw [mem_filter, mem_product, mem_range, mem_range] at hx
    have h := D.blk_of_slot hx.1.1 hx.1.2
    rw [hx.2] at h
    exact Prod.ext h.2.2.1 h.2.2.2
  · intro J hJ
    exact (D.slot_of_blk (mem_range.mp hJ) hI).2.2.2
  · intro x hx
    rw [mem_filter, mem_product, mem_range, mem_range] at hx
    have h := D.blk_of_slot hx.1.1 hx.1.2
    rw [hx.2] at h
    show G x.1 x.2 = G (D.slotP I) (D.slotS I (D.colBlk x.1 x.2))
    rw [h.2.2.1, h.2.2.2]

/-- A sum over blocks and positions in a block is a sum over positions. -/
theorem sum_blocks {M : Type} [AddCommMonoid M] (F : ℕ → M) : ∀ n : ℕ,
    (∑ J ∈ range n, ∑ j' ∈ range D.B, F (D.B * J + j')) = ∑ j ∈ range (D.B * n), F j
  | 0 => by simp
  | n + 1 => by
    rw [sum_range_succ, sum_blocks F n, Nat.mul_succ, sum_range_add]

/-- `sum_blocks` for a function of the block and of the position in the block. -/
theorem sum_blocks2 {M : Type} [AddCommMonoid M] (f : ℕ → ℕ → M) (n : ℕ) :
    (∑ J ∈ range n, ∑ j' ∈ range D.B, f J j') = ∑ j ∈ range (D.B * n), f (j / D.B) (j % D.B) := by
  rw [← D.sum_blocks (fun j => f (j / D.B) (j % D.B)) n]
  refine sum_congr rfl fun J _ => sum_congr rfl fun j' hj => ?_
  have hj' := mem_range.mp hj
  rw [Nat.mul_add_div D.B_pos, Nat.div_eq_of_lt hj', Nat.add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt hj']

/-- The entries of a row. For a position in block I < nBlk: the sum over the entries of regions M
(empty ones excluded) and D (masked ones included) in the row, of a function of the column position,
is the sum over all positions j < B (I + 1). -/
theorem sum_row {M : Type} [AddCommMonoid M] {I : ℕ} (hI : I < D.nBlk) (F : ℕ → M) :
    (∑ P ∈ range D.hP, ∑ s ∈ range (D.nBlk - 1), if D.rowBlk P s = I then
            ∑ j' ∈ range D.B, F (D.B * D.colBlk P s + j')
          else 0) +
        ∑ j' ∈ range D.B, F (D.B * I + j') =
      ∑ j ∈ range (D.B * (I + 1)), F j := by
  rw [D.sum_slots hI fun J => ∑ j' ∈ range D.B, F (D.B * J + j'),
    ← sum_range_succ (fun J => ∑ j' ∈ range D.B, F (D.B * J + j')) I]
  exact D.sum_blocks F (I + 1)

/-! ## Entries as numbers -/

/-- bits of an entry of M -/
def lM : ℕ := D.lg + D.lP + (D.lP + 1) + D.lB + D.lB
/-- bits of an entry of D -/
def lD : ℕ := D.lg + (D.lP + 1) + D.lB + D.lB

/-- the entry (g | P | s | i' | j') of region M -/
def codeM (g P s i' j' : ℕ) : ℕ := (((g * D.hP + P) * D.nBlk + s) * D.B + i') * D.B + j'
/-- the entry (g | I | i' | j') of region D -/
def codeD (g I i' j' : ℕ) : ℕ := ((g * D.nBlk + I) * D.B + i') * D.B + j'

/-- the part j' of an entry, of M or of D -/
def mJ (x : ℕ) : ℕ := x % D.B
/-- the part i' of an entry, of M or of D -/
def mI (x : ℕ) : ℕ := x / D.B % D.B
/-- the part s of an entry of M -/
def mS (x : ℕ) : ℕ := x / D.B / D.B % D.nBlk
/-- the part P of an entry of M -/
def mP (x : ℕ) : ℕ := x / D.B / D.B / D.nBlk % D.hP
/-- the part g of an entry of M -/
def mG (x : ℕ) : ℕ := x / D.B / D.B / D.nBlk / D.hP
/-- the part I of an entry of D -/
def dI (x : ℕ) : ℕ := x / D.B / D.B % D.nBlk
/-- the part g of an entry of D -/
def dG (x : ℕ) : ℕ := x / D.B / D.B / D.nBlk

theorem nBlk_pos : 0 < D.nBlk := Nat.mul_pos (by norm_num) D.hP_pos

theorem div_step {a r n : ℕ} (hn : 0 < n) (hr : r < n) :
    (a * n + r) / n = a ∧ (a * n + r) % n = r := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hr, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

theorem parts_codeM {g P s i' j' : ℕ} (hP : P < D.hP) (hs : s < D.nBlk)
    (hi : i' < D.B) (hj : j' < D.B) :
    D.mG (D.codeM g P s i' j') = g ∧
    D.mP (D.codeM g P s i' j') = P ∧
    D.mS (D.codeM g P s i' j') = s ∧
    D.mI (D.codeM g P s i' j') = i' ∧
    D.mJ (D.codeM g P s i' j') = j' := by
  unfold mG mP mS mI mJ codeM
  rw [(div_step D.B_pos hj).1, (div_step D.B_pos hj).2, (div_step D.B_pos hi).1,
    (div_step D.B_pos hi).2, (div_step D.nBlk_pos hs).1, (div_step D.nBlk_pos hs).2,
    (div_step D.hP_pos hP).1, (div_step D.hP_pos hP).2]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem parts_codeD {g I i' j' : ℕ} (hI : I < D.nBlk) (hi : i' < D.B) (hj : j' < D.B) :
    D.dG (D.codeD g I i' j') = g ∧
    D.dI (D.codeD g I i' j') = I ∧
    D.mI (D.codeD g I i' j') = i' ∧
    D.mJ (D.codeD g I i' j') = j' := by
  unfold dG dI mI mJ codeD
  rw [(div_step D.B_pos hj).1, (div_step D.B_pos hj).2, (div_step D.B_pos hi).1,
    (div_step D.B_pos hi).2, (div_step D.nBlk_pos hI).1, (div_step D.nBlk_pos hI).2]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem codeM_parts (x : ℕ) : D.codeM (D.mG x) (D.mP x) (D.mS x) (D.mI x) (D.mJ x) = x := by
  unfold mG mP mS mI mJ codeM
  rw [Nat.div_add_mod' (x / D.B / D.B / D.nBlk) D.hP, Nat.div_add_mod' (x / D.B / D.B) D.nBlk,
    Nat.div_add_mod' (x / D.B) D.B, Nat.div_add_mod' x D.B]

theorem codeD_parts (x : ℕ) : D.codeD (D.dG x) (D.dI x) (D.mI x) (D.mJ x) = x := by
  unfold dG dI mI mJ codeD
  rw [Nat.div_add_mod' (x / D.B / D.B) D.nBlk,
    Nat.div_add_mod' (x / D.B) D.B, Nat.div_add_mod' x D.B]

theorem two_pow_lM : 2 ^ D.lM = D.nG * D.hP * D.nBlk * D.B * D.B := by
  unfold lM nG hP nBlk hP B
  rw [pow_add, pow_add, pow_add, pow_add, pow_add]
  ring

theorem two_pow_lD : 2 ^ D.lD = D.nG * D.nBlk * D.B * D.B := by
  unfold lD nG nBlk hP B
  rw [pow_add, pow_add, pow_add, pow_add]
  ring

theorem codeM_lt {g P s i' j' : ℕ} (hg : g < D.nG) (hP : P < D.hP) (hs : s < D.nBlk)
    (hi : i' < D.B) (hj : j' < D.B) :
    D.codeM g P s i' j' < 2 ^ D.lM := by
  rw [two_pow_lM]
  unfold codeM
  have h1 : g * D.hP + P + 1 ≤ D.nG * D.hP := by nlinarith
  have h2 : (g * D.hP + P) * D.nBlk + s + 1 ≤ D.nG * D.hP * D.nBlk := by nlinarith
  have h3 : ((g * D.hP + P) * D.nBlk + s) * D.B + i' + 1 ≤ D.nG * D.hP * D.nBlk * D.B := by
    nlinarith
  nlinarith

theorem codeD_lt {g I i' j' : ℕ} (hg : g < D.nG) (hI : I < D.nBlk) (hi : i' < D.B) (hj : j' < D.B) :
    D.codeD g I i' j' < 2 ^ D.lD := by
  rw [two_pow_lD]
  unfold codeD
  have h1 : g * D.nBlk + I + 1 ≤ D.nG * D.nBlk := by nlinarith
  have h2 : (g * D.nBlk + I) * D.B + i' + 1 ≤ D.nG * D.nBlk * D.B := by nlinarith
  nlinarith

/-- The part g of an entry of M below 2^lM is the number of a key/value head. -/
theorem mG_lt {x : ℕ} (hx : x < 2 ^ D.lM) : D.mG x < D.nG := by
  unfold mG
  rw [two_pow_lM] at hx
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  exact Nat.div_lt_of_lt_mul (by nlinarith)

theorem dG_lt {x : ℕ} (hx : x < 2 ^ D.lD) : D.dG x < D.nG := by
  unfold dG
  rw [two_pow_lD] at hx
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  exact Nat.div_lt_of_lt_mul (by nlinarith)

/-! ## The positions of an entry; empty and masked entries -/

/-- An entry of M is empty if s = 2 hP - 1. -/
def EmptyM (x : ℕ) : Prop := D.mS x = D.nBlk - 1
instance (x : ℕ) : Decidable (D.EmptyM x) := inferInstanceAs (Decidable (_ = _))
/-- An entry of D is masked if j' > i'. -/
def MaskedD (x : ℕ) : Prop := D.mI x < D.mJ x
instance (x : ℕ) : Decidable (D.MaskedD x) := inferInstanceAs (Decidable (_ < _))

/-- i(x) for an entry of M that is not empty -/
def iM (x : ℕ) : ℕ := D.B * D.rowBlk (D.mP x) (D.mS x) + D.mI x
/-- j(x) for an entry of M that is not empty -/
def jM (x : ℕ) : ℕ := D.B * D.colBlk (D.mP x) (D.mS x) + D.mJ x
/-- i(x) for an entry of D -/
def iD (x : ℕ) : ℕ := D.B * D.dI x + D.mI x
/-- j(x) for an entry of D -/
def jD (x : ℕ) : ℕ := D.B * D.dI x + D.mJ x

end Dim

/-! ## The reference parameters -/

theorem ref_sizes :
    Dim.ref.nG = 8 ∧ Dim.ref.hP = 8 ∧ Dim.ref.nBlk = 16 ∧ Dim.ref.B = 64 ∧ Dim.ref.T = 1024 ∧
    Dim.ref.ch = 128 ∧ Dim.ref.nb = 20 ∧ Dim.ref.lT = 10 ∧ Dim.ref.lM = 22 ∧ Dim.ref.lD = 19 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

end Inst.Model.AttSeg
