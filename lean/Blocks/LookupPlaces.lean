-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/LookupPlaces.lean: where the pads of a lookup argument are in one pad vector.

A lookup argument (`Lk`, Blocks/LookupBlock.lean) takes thirteen maps that name the pads of its
masked scalars. Here the pads are the entries of one pad vector, and the maps are formulas, from a
base index a.

The order from a: Z_θ; Y_(θ,π); the layers of the key side; the layers of the table side; the leaf
layer; the bit layer; U; V; the rounds of the root test. A product layer has a range of indices: two
for each round, then two for v0, v1. All layers of a side have ranges of one width, enough for every
layer of the side (`LkAllot.wK`, `LkAllot.wT`), so some indices are not used. Pads are sent that
mask nothing, so nPads, and with it the length of the pad vector, is larger than the number of
masked scalars.
 * `LkAllot.plZ`, .., `LkAllot.plR`: the maps; `LkAllot.nPads`: the number of indices taken.
 * `Lk.PlacedAt` L hn a: the maps of L are these; by `rfl` if L is built from them.
 * `Lk.PlacedAt.padsOK`, `allPads_sub` (under `Lk.PlacedAt` L hn a and a + nPads ≤ n): `Lk.PadsOK`
   holds, and all pads are in `region` hn a (a + nPads) (Blocks/Allot.lean).

Notation:
 * D, σ, r, lp, NT: natural numbers, fields of `LkPar`: 2^D keys in a tree, NT trees, tables with
   2^r entries, 2^lp bits for a multiplicity; σ: the number of bits of a tree's index
   (Blocks/LookupRel.lean; σ: the head of Blocks/LookupWhole.lean).
 * gT: `LkPar.gT` = r + σ + lp: the number of variables of the leaves of the table side; Pm:
   `LkPar.Pm` = 2^lp - 1: the number of the highest plane (Blocks/LookupRel.lean).
 * Z_θ, Y_(θ,π): the tree products of the key side and of the table side (`LkPar.Zt`, `LkPar.Yt`;
   the head of Blocks/LookupRel.lean); U, V: the arrays U_π[θ], V_π[θ] of the root test (the head of
   Blocks/LookupRA.lean).
 * v0, v1: of a product layer: the two masked scalars v0, v1 that the prover sends (the head of
   Blocks/ProductBlock.lean).
-/
import Blocks.LookupStage
import Blocks.Allot

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks

open Iop Prob

/-! ## 1. Numbers -/

namespace LkAllot

theorem pair_inj {B x y x' y' : ℕ} (hy : y < B) (hy' : y' < B) (h : x * B + y = x' * B + y') :
    x = x' ∧ y = y' := by
  have hB : 0 < B := by omega
  have h1 : (x * B + y) / B = x := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hy, Nat.zero_add]
  have h2 : (x' * B + y') / B = x' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hy', Nat.zero_add]
  have h3 : x = x' := by rw [← h1, h, h2]
  subst h3
  exact ⟨rfl, by omega⟩

theorem pair_lt {A B x y : ℕ} (hx : x < A) (hy : y < B) : x * B + y < A * B :=
  calc x * B + y < x * B + B := by omega
    _ = (x + 1) * B := by ring
    _ ≤ A * B := Nat.mul_le_mul_right _ hx

variable {E : Type} (P : LkPar E) (a : ℕ)

/-- The widths of the ranges of indices of a layer of the key side, and of a layer of the table side
(also of the leaf layer and the bit layer): two scalars for each round, and v0, v1. Every layer of a
side has a range of the same width, enough for every layer of the side. -/
def wK : ℕ := 2 * (P.D + P.σ) + 2
def wT : ℕ := 2 * P.gT + 2

/-- The first indices of the groups, from the base a: Z, Y, key side, table side, leaf layer, bit
layer, U, V, rounds of the root test; and the first index after them. -/
def oY : ℕ := a + P.NT
def oK : ℕ := oY P a + P.NT * 2 ^ P.lp
def oT : ℕ := oK P a + P.D * wK P
def oL : ℕ := oT P a + P.r * wT P
def oB : ℕ := oL P a + wT P
def oU : ℕ := oB P a + wT P
def oV : ℕ := oU P a + P.Pm * P.NT
def oR : ℕ := oV P a + P.Pm * P.NT
def oEnd : ℕ := oR P a + 2 * P.σ

/-- The number of indices that a lookup argument takes. -/
def nPads : ℕ :=
  P.NT + P.NT * 2 ^ P.lp + P.D * wK P + P.r * wT P + 2 * wT P + 2 * (P.Pm * P.NT) + 2 * P.σ

theorem oEnd_eq : oEnd P a = a + nPads P := by
  unfold oEnd oR oV oU oB oL oT oK oY nPads
  omega

variable {n : ℕ} (hn : 0 < n)

/-- The thirteen maps to pads, from the base a. -/
def plZ (θ : ℕ) : Fin n := allot hn (a + θ)
def plY (θ π : ℕ) : Fin n := allot hn (oY P a + (θ * 2 ^ P.lp + π))
def plK (l t : ℕ) (j : Fin 2) : Fin n := allot hn (oK P a + l * wK P + 2 * t + j.val)
def plKv (l : ℕ) (b : Bool) : Fin n := allot hn (oK P a + l * wK P + 2 * (P.D + P.σ) + b.toNat)
def plT (l t : ℕ) (j : Fin 2) : Fin n := allot hn (oT P a + l * wT P + 2 * t + j.val)
def plTv (l : ℕ) (b : Bool) : Fin n := allot hn (oT P a + l * wT P + 2 * P.gT + b.toNat)
def plL (t : ℕ) (j : Fin 2) : Fin n := allot hn (oL P a + 2 * t + j.val)
def plLv (b : Bool) : Fin n := allot hn (oL P a + 2 * P.gT + b.toNat)
def plB (t : ℕ) (j : Fin 2) : Fin n := allot hn (oB P a + 2 * t + j.val)
def plBv (b : Bool) : Fin n := allot hn (oB P a + 2 * P.gT + b.toNat)
def plU (π θ : ℕ) : Fin n := allot hn (oU P a + (π * P.NT + θ))
def plV (π θ : ℕ) : Fin n := allot hn (oV P a + (π * P.NT + θ))
def plR (t : ℕ) (j : Fin 2) : Fin n := allot hn (oR P a + 2 * t + j.val)

end LkAllot

/-! ## 2. One range of indices -/

section Slot

variable {E Y N Ξ : Type} [Field E] [Fintype E] [DecidableEq E] [Fintype N]
  [DecidableEq N] {n : ℕ} (hn : 0 < n)

omit [Fintype E] [DecidableEq E] in
/-- The pads of the rounds of a sumcheck with two scalars in a round, from the index c: under the
hypotheses below each is used once, and all are in the region from c to c + 2 G. -/
theorem placesOnce_of_allot {Ξ' : Type} (S : SC E Y (Fin n) Ξ' ℕ) (he : ∀ i, S.e i = 1)
    (c G : ℕ) (l : List ℕ) (hl : ∀ v ∈ l, v < G)
    (hidx : ∀ t j, S.idx t j = allot hn (c + 2 * t + j.val)) (hle : c + 2 * G ≤ n) :
    S.PlacesOnceOn l ∧ S.padsOf l ⊆ region hn c (c + 2 * G) := by
  constructor
  · rintro ⟨t, j⟩ ht ⟨t', j'⟩ ht' heq
    have h1 : S.idx t j = S.idx t' j' := heq
    have hj : j.val < 2 := by have h := j.2; have h' := he t; omega
    have hj' : j'.val < 2 := by have h := j'.2; have h' := he t'; omega
    have ht1 : t < G := hl t ht
    have ht2 : t' < G := hl t' ht'
    rw [hidx, hidx] at h1
    have h2 := allot_inj hn (by omega) (by omega) h1
    have h3 : t = t' := by omega
    have h4 : j.val = j'.val := by omega
    subst h3
    exact Sigma.ext rfl (heq_of_eq (Fin.ext h4))
  · intro q hq
    obtain ⟨v, hv, j, rfl⟩ := S.mem_padsOf.mp hq
    have hj : j.val < 2 := by have h := j.2; have h' := he v; omega
    have hv' := hl v hv
    rw [hidx]
    exact mem_region hn (by omega) (by omega)

/-- A product layer in a range from the index c, of the width 2 G + 2: under the hypotheses below
each pad is used once, within that region. -/
theorem layerOK_of_allot (Q : PL E Y (Fin n) N Ξ) (c G : ℕ) (hg : Q.g ≤ G)
    (hidx : ∀ t j, Q.idx t j = allot hn (c + 2 * t + j.val))
    (hpv : ∀ b, Q.pv b = allot hn (c + 2 * G + b.toNat)) (hle : c + 2 * G + 2 ≤ n) :
    Q.LayerOK ∧ Q.pads ⊆ region hn c (c + 2 * G + 2) := by
  obtain ⟨h1, h2⟩ := placesOnce_of_allot hn Q.sc (fun _ => rfl) c G (PL.vars Q.g)
    (fun v hv => lt_of_lt_of_le (PL.mem_vars.mp hv) hg) hidx (by omega)
  have hb : ∀ b : Bool, b.toNat < 2 := fun b => by cases b <;> simp
  have h3 : Set.range Q.pv ⊆ region hn (c + 2 * G) (c + 2 * G + 2) := by
    rintro _ ⟨b, rfl⟩
    rw [hpv]
    exact mem_region hn (by omega) (by have := hb b; omega)
  refine ⟨⟨h1, fun b b' hbb => ?_, (region_disjoint hn le_rfl hle).mono h2 h3⟩,
    Set.union_subset (h2.trans (region_mono hn le_rfl (by omega)))
      (h3.trans (region_mono hn (by omega) le_rfl))⟩
  rw [hpv, hpv] at hbb
  have h4 := allot_inj hn (by have := hb b; omega) (by have := hb b'; omega) hbb
  cases b <;> cases b' <;> simp at h4 ⊢

end Slot

/-! ## 3. The argument -/

namespace Lk

open LkAllot

variable {E Y N : Type} [Field E] [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] {n : ℕ}
  (L : Lk E Y (Fin n) N) (hn : 0 < n) (a : ℕ)

/-- The thirteen maps to pads of the argument are those of this file, from the base a. -/
structure PlacedAt : Prop where
  pZ : L.pZ = LkAllot.plZ a hn
  pY : L.pY = LkAllot.plY L.par a hn
  pK : L.pK = LkAllot.plK L.par a hn
  pKv : L.pKv = LkAllot.plKv L.par a hn
  pT : L.pT = LkAllot.plT L.par a hn
  pTv : L.pTv = LkAllot.plTv L.par a hn
  pL : L.pL = LkAllot.plL L.par a hn
  pLv : L.pLv = LkAllot.plLv L.par a hn
  pB : L.pB = LkAllot.plB L.par a hn
  pBv : L.pBv = LkAllot.plBv L.par a hn
  pU : L.pU = LkAllot.plU L.par a hn
  pV : L.pV = LkAllot.plV L.par a hn
  pR : L.pR = LkAllot.plR L.par a hn

/-- The interval of indices of a group. -/
def lo : Grp → ℕ
  | .zy => a
  | .k l => oK L.par a + l * wK L.par
  | .t l => oT L.par a + l * wT L.par
  | .lf => oL L.par a
  | .bt => oB L.par a
  | .uv => oU L.par a
  | .rt => oR L.par a
def hi : Grp → ℕ
  | .zy => oK L.par a
  | .k l => oK L.par a + l * wK L.par + wK L.par
  | .t l => oT L.par a + l * wT L.par + wT L.par
  | .lf => oB L.par a
  | .bt => oU L.par a
  | .uv => oR L.par a
  | .rt => oEnd L.par a

omit [Field E] [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] in
private theorem slot_le {l A w : ℕ} (h : l < A) : l * w + w ≤ A * w :=
  calc l * w + w = (l + 1) * w := by ring
    _ ≤ A * w := Nat.mul_le_mul_right _ h

omit [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] in
/-- The interval of a group that occurs is between the first index of its kind and the first index
of the next kind. -/
theorem lo_hi {g : Grp} (hg : L.GOK g) :
    (match g with
      | .zy => a | .k _ => oK L.par a | .t _ => oT L.par a | .lf => oL L.par a | .bt => oB L.par a | .uv => oU L.par a | .rt => oR L.par a) ≤ L.lo a g ∧
    L.lo a g ≤ L.hi a g ∧
    L.hi a g ≤ (match g with
      | .zy => oK L.par a | .k _ => oT L.par a | .t _ => oL L.par a | .lf => oB L.par a
      | .bt => oU L.par a | .uv => oR L.par a | .rt => oEnd L.par a) := by
  cases g with
  | zy => exact ⟨le_rfl, by show a ≤ oK L.par a; unfold oK oY; omega, le_rfl⟩
  | k l =>
    have h := slot_le (w := wK L.par) (show l < L.par.D from hg)
    exact ⟨Nat.le_add_right _ _,
      Nat.le_add_right _ _,
      by show oK L.par a + l * wK L.par + wK L.par ≤ oK L.par a + L.par.D * wK L.par; omega⟩
  | t l =>
    have h := slot_le (w := wT L.par) (show l < L.par.r from hg)
    exact ⟨Nat.le_add_right _ _,
      Nat.le_add_right _ _,
      by show oT L.par a + l * wT L.par + wT L.par ≤ oT L.par a + L.par.r * wT L.par; omega⟩
  | lf => exact ⟨le_rfl, Nat.le_add_right _ _, le_rfl⟩
  | bt => exact ⟨le_rfl, Nat.le_add_right _ _, le_rfl⟩
  | uv => exact ⟨le_rfl, by show oU L.par a ≤ oU L.par a + _ + _; omega, le_rfl⟩
  | rt => exact ⟨le_rfl, Nat.le_add_right _ _, le_rfl⟩

omit [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] in
/-- The first indices of the kinds are in order. -/
theorem chain_le :
    a ≤ oK L.par a ∧ oK L.par a ≤ oT L.par a ∧ oT L.par a ≤ oL L.par a ∧ oL L.par a ≤ oB L.par a ∧
    oB L.par a ≤ oU L.par a ∧ oU L.par a ≤ oR L.par a ∧ oR L.par a ≤ oEnd L.par a :=
  ⟨by unfold oK oY; omega, Nat.le_add_right _ _, Nat.le_add_right _ _, Nat.le_add_right _ _,
    Nat.le_add_right _ _, by unfold oR oV; omega, Nat.le_add_right _ _⟩

omit [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] in
/-- The intervals of two different groups that occur do not overlap. -/
theorem sep {g g' : Grp} (hg : L.GOK g) (hg' : L.GOK g') (hne : g ≠ g') :
    L.hi a g ≤ L.lo a g' ∨ L.hi a g' ≤ L.lo a g := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := L.chain_le a
  have h := L.lo_hi a hg
  have h' := L.lo_hi a hg'
  cases g <;> cases g' <;> simp only at h h' <;> first
    | exact absurd rfl hne
    | (left; omega)
    | (right; omega)
    | skip
  · -- two layers of the key side
    rename_i l l'
    have hll : l ≠ l' := fun e => hne (by rw [e])
    rcases Nat.lt_or_gt_of_ne hll with hlt | hlt
    · left
      have := slot_le (w := wK L.par) hlt
      show oK L.par a + l * wK L.par + wK L.par ≤ oK L.par a + l' * wK L.par
      omega
    · right
      have := slot_le (w := wK L.par) hlt
      show oK L.par a + l' * wK L.par + wK L.par ≤ oK L.par a + l * wK L.par
      omega
  · -- two layers of the table side
    rename_i l l'
    have hll : l ≠ l' := fun e => hne (by rw [e])
    rcases Nat.lt_or_gt_of_ne hll with hlt | hlt
    · left
      have := slot_le (w := wT L.par) hlt
      show oT L.par a + l * wT L.par + wT L.par ≤ oT L.par a + l' * wT L.par
      omega
    · right
      have := slot_le (w := wT L.par) hlt
      show oT L.par a + l' * wT L.par + wT L.par ≤ oT L.par a + l * wT L.par
      omega

end Lk

namespace Lk

open LkAllot

variable {E Y N : Type} [Field E] [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] {n : ℕ}
  {L : Lk E Y (Fin n) N} {hn : 0 < n} {a : ℕ}

/-- Under hn, h, hle, hl: each layer of the key side uses every pad once, within its range; likewise
below for the other layers. -/
theorem PlacedAt.layerK (h : L.PlacedAt hn a) (hle : oEnd L.par a ≤ n) {l : ℕ} (hl : l < L.par.D) :
    (L.plK l).LayerOK ∧ L.grp (.k l) ⊆ region hn (L.lo a (.k l)) (L.hi a (.k l)) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := L.chain_le a
  have h1 := (L.lo_hi a (g := .k l) hl).2.2
  have h2 : oK L.par a + l * wK L.par + wK L.par ≤ oT L.par a := h1
  refine layerOK_of_allot hn (L.plK l) (oK L.par a + l * wK L.par) (L.par.D + L.par.σ)
    (by show l + L.par.σ ≤ _; omega) (fun t j => ?_) (fun b => ?_) ?_
  · show L.pK l t j = _
    rw [h.pK]
    rfl
  · show L.pKv l b = _
    rw [h.pKv]
    rfl
  · have : wK L.par = 2 * (L.par.D + L.par.σ) + 2 := rfl
    omega

theorem PlacedAt.layerT (h : L.PlacedAt hn a) (hle : oEnd L.par a ≤ n) {l : ℕ} (hl : l < L.par.r) :
    (L.plT l).LayerOK ∧ L.grp (.t l) ⊆ region hn (L.lo a (.t l)) (L.hi a (.t l)) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := L.chain_le a
  have h1 := (L.lo_hi a (g := .t l) hl).2.2
  have h2 : oT L.par a + l * wT L.par + wT L.par ≤ oL L.par a := h1
  refine layerOK_of_allot hn (L.plT l) (oT L.par a + l * wT L.par) L.par.gT
    (by show l + (L.par.σ + L.par.lp) ≤ L.par.r + (L.par.σ + L.par.lp); omega)
    (fun t j => ?_) (fun b => ?_) ?_
  · show L.pT l t j = _
    rw [h.pT]
    rfl
  · show L.pTv l b = _
    rw [h.pTv]
    rfl
  · have : wT L.par = 2 * L.par.gT + 2 := rfl
    omega

theorem PlacedAt.layerL (h : L.PlacedAt hn a) (hle : oEnd L.par a ≤ n) :
    L.plL.LayerOK ∧ L.grp .lf ⊆ region hn (L.lo a .lf) (L.hi a .lf) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := L.chain_le a
  have hw : oB L.par a = oL L.par a + (2 * L.par.gT + 2) := rfl
  refine layerOK_of_allot hn L.plL (oL L.par a) L.par.gT le_rfl (fun t j => ?_)
    (fun b => ?_) (by omega)
  · show L.pL t j = _
    rw [h.pL]
    rfl
  · show L.pLv b = _
    rw [h.pLv]
    rfl

theorem PlacedAt.layerB (h : L.PlacedAt hn a) (hle : oEnd L.par a ≤ n) :
    L.plB.LayerOK ∧ L.grp .bt ⊆ region hn (L.lo a .bt) (L.hi a .bt) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := L.chain_le a
  have hw : oU L.par a = oB L.par a + (2 * L.par.gT + 2) := rfl
  refine layerOK_of_allot hn L.plB (oB L.par a) L.par.gT le_rfl (fun t j => ?_)
    (fun b => ?_) (by omega)
  · show L.pB t j = _
    rw [h.pB]
    rfl
  · show L.pBv b = _
    rw [h.pBv]
    rfl

theorem PlacedAt.rounds (h : L.PlacedAt hn a) (hle : oEnd L.par a ≤ n) :
    L.scR.PlacesOnceOn (lkVars L.par.σ) ∧ L.grp .rt ⊆ region hn (L.lo a .rt) (L.hi a .rt) :=
  placesOnce_of_allot hn L.scR (fun _ => rfl) (oR L.par a) L.par.σ
    (lkVars L.par.σ) (fun _ hv => mem_lkVars.mp hv)
    (fun t j => by
      show L.pR t j = _
      rw [h.pR]
      rfl) hle

/-- The indices of Z, Y, and of the arrays U, V. -/
def numZY (L : Lk E Y (Fin n) N) (a : ℕ) : L.KZY → ℕ
  | .inl θ => a + θ.val
  | .inr (θ, π) => oY L.par a + (θ.val * 2 ^ L.par.lp + π.val)
def numUV (L : Lk E Y (Fin n) N) (a : ℕ) : L.KUV → ℕ
  | .inl (π, θ) => oU L.par a + (π.val * L.par.NT + θ.val)
  | .inr (π, θ) => oV L.par a + (π.val * L.par.NT + θ.val)

theorem numZY_mem (k : L.KZY) : a ≤ numZY L a k ∧ numZY L a k < oK L.par a := by
  rcases k with θ | ⟨θ, π⟩
  · have := θ.2
    exact ⟨Nat.le_add_right _ _, by show a + θ.val < a + L.par.NT + _; omega⟩
  · have := pair_lt θ.2 π.2
    exact ⟨by show a ≤ a + L.par.NT + _; omega, by show oY L.par a + _ < oY L.par a + _; omega⟩

theorem numZY_inj : Function.Injective (numZY L a) := by
  rintro (θ | ⟨θ, π⟩) (θ' | ⟨θ', π'⟩) he
  · have h1 : a + θ.val = a + θ'.val := he
    exact congrArg Sum.inl (Fin.ext (by omega))
  · have h1 : a + θ.val = a + L.par.NT + (θ'.val * 2 ^ L.par.lp + π'.val) := he
    have := θ.2
    omega
  · have h1 : a + L.par.NT + (θ.val * 2 ^ L.par.lp + π.val) = a + θ'.val := he
    have := θ'.2
    omega
  · have h1 : oY L.par a + (θ.val * 2 ^ L.par.lp + π.val) =
        oY L.par a + (θ'.val * 2 ^ L.par.lp + π'.val) := he
    obtain ⟨h2, h3⟩ := pair_inj π.2 π'.2 (Nat.add_left_cancel h1)
    exact congrArg Sum.inr (Prod.ext (Fin.ext h2) (Fin.ext h3))

theorem numUV_mem (k : L.KUV) : oU L.par a ≤ numUV L a k ∧ numUV L a k < oR L.par a := by
  rcases k with ⟨π, θ⟩ | ⟨π, θ⟩
  · have := pair_lt π.2 θ.2
    exact ⟨Nat.le_add_right _ _, by show oU L.par a + _ < oU L.par a + _ + _; omega⟩
  · have := pair_lt π.2 θ.2
    exact ⟨by show oU L.par a ≤ oU L.par a + _ + _; omega,
      by show oV L.par a + _ < oV L.par a + _; omega⟩

theorem numUV_inj : Function.Injective (numUV L a) := by
  rintro (⟨π, θ⟩ | ⟨π, θ⟩) (⟨π', θ'⟩ | ⟨π', θ'⟩) he
  · have h1 : oU L.par a + (π.val * L.par.NT + θ.val) = oU L.par a + (π'.val * L.par.NT + θ'.val) :=
      he
    obtain ⟨h2, h3⟩ := pair_inj θ.2 θ'.2 (Nat.add_left_cancel h1)
    exact congrArg Sum.inl (Prod.ext (Fin.ext h2) (Fin.ext h3))
  · have h1 : oU L.par a + (π.val * L.par.NT + θ.val) =
        oU L.par a + L.par.Pm * L.par.NT + (π'.val * L.par.NT + θ'.val) := he
    have := pair_lt π.2 θ.2
    omega
  · have h1 : oU L.par a + L.par.Pm * L.par.NT + (π.val * L.par.NT + θ.val) =
        oU L.par a + (π'.val * L.par.NT + θ'.val) := he
    have := pair_lt π'.2 θ'.2
    omega
  · have h1 : oV L.par a + (π.val * L.par.NT + θ.val) = oV L.par a + (π'.val * L.par.NT + θ'.val) :=
      he
    obtain ⟨h2, h3⟩ := pair_inj θ.2 θ'.2 (Nat.add_left_cancel h1)
    exact congrArg Sum.inr (Prod.ext (Fin.ext h2) (Fin.ext h3))

theorem PlacedAt.idxZY (h : L.PlacedAt hn a) (k : L.KZY) : L.idxZY k = allot hn (numZY L a k) := by
  rcases k with θ | ⟨θ, π⟩
  · show L.pZ θ = _
    rw [h.pZ]
    rfl
  · show L.pY θ π = _
    rw [h.pY]
    rfl

theorem PlacedAt.idxUV (h : L.PlacedAt hn a) (k : L.KUV) : L.idxUV k = allot hn (numUV L a k) := by
  rcases k with ⟨π, θ⟩ | ⟨π, θ⟩
  · show L.pU π θ = _
    rw [h.pU]
    rfl
  · show L.pV π θ = _
    rw [h.pV]
    rfl

/-- Under hn, h, hle: every group that occurs is in the region of its interval. -/
theorem PlacedAt.grp_sub (h : L.PlacedAt hn a) (hle : oEnd L.par a ≤ n) {g : Grp} (hg : L.GOK g) :
    L.grp g ⊆ region hn (L.lo a g) (L.hi a g) := by
  cases g with
  | zy =>
    rintro _ ⟨k, rfl⟩
    rw [h.idxZY]
    exact mem_region hn (numZY_mem k).1 (numZY_mem k).2
  | k l => exact (h.layerK hle hg).2
  | t l => exact (h.layerT hle hg).2
  | lf => exact (h.layerL hle).2
  | bt => exact (h.layerB hle).2
  | uv =>
    rintro _ ⟨k, rfl⟩
    rw [h.idxUV]
    exact mem_region hn (numUV_mem k).1 (numUV_mem k).2
  | rt => exact (h.rounds hle).2

/-- The interval of a group that occurs is between a and the first index after the argument. -/
theorem lo_hi_all (L : Lk E Y (Fin n) N) (a : ℕ) {g : Grp} (hg : L.GOK g) :
    a ≤ L.lo a g ∧ L.hi a g ≤ oEnd L.par a := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := L.chain_le a
  have h := L.lo_hi a hg
  cases g <;> simp only at h <;> constructor <;> omega

/-- Under hn, h, hle: every pad is used for one masked scalar only. -/
theorem PlacedAt.padsOK (h : L.PlacedAt hn a) (hle : a + nPads L.par ≤ n) : L.PadsOK := by
  rw [← oEnd_eq] at hle
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := L.chain_le a
  refine ⟨fun k k' he => ?_, fun k k' he => ?_, fun l hl => (h.layerK hle hl).1,
    fun l hl => (h.layerT hle hl).1, (h.layerL hle).1, (h.layerB hle).1,
    (h.rounds hle).1, fun g g' hg hg' hne => ?_⟩
  · rw [h.idxZY, h.idxZY] at he
    exact numZY_inj
      (allot_inj hn (by have := (numZY_mem (a := a) k).2; omega)
        (by have := (numZY_mem (a := a) k').2; omega) he)
  · rw [h.idxUV, h.idxUV] at he
    exact numUV_inj
      (allot_inj hn (by have := (numUV_mem (a := a) k).2; omega)
        (by have := (numUV_mem (a := a) k').2; omega) he)
  · rcases L.sep a hg hg' hne with hs | hs
    · exact (region_disjoint hn hs ((L.lo_hi_all a hg').2.trans hle)).mono
        (h.grp_sub hle hg) (h.grp_sub hle hg')
    · exact ((region_disjoint hn hs ((L.lo_hi_all a hg).2.trans hle)).mono
        (h.grp_sub hle hg') (h.grp_sub hle hg)).symm

/-- Under hn, h, hle: all pads of the argument are in one region of nPads indices, from a. -/
theorem PlacedAt.allPads_sub (h : L.PlacedAt hn a) (hle : a + nPads L.par ≤ n) :
    L.allPads ⊆ region hn a (a + nPads L.par) := by
  rw [← oEnd_eq] at hle ⊢
  rintro q ⟨g, hg, hq⟩
  exact region_mono hn (L.lo_hi_all a hg).1 (L.lo_hi_all a hg).2 (h.grp_sub hle hg hq)

end Lk

end Blocks
