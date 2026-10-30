-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Tab/RingG.lean:
the products in a key of the layers' calls commute with a map of rings; and the seated reader of
cells is a reader in the base field, lifted. Theorems without a hypothesis, and two definitions with
code.

Terms. Honest/K3/GLOSSARY.md. In this file: φ is a map of commutative rings R →+* R'; a reading is a
function cell : NameG → R (OnBytes/Tie/Pv/Lookup/Ends/G.lean); the reading "φ of cell" is
fun n => φ (cell n).

Why. The library's formulas for a key of the layers' calls are written over any commutative ring.
The honest side's cells and weights are elements of the base field, lifted into the extension field.
A product there is written with eleven products in the base field (the product of `Cubic`,
Code/Field.lean). By the theorems here the products in a key can be computed in the base field and
lifted once.

After. Johnson/HonestTrace/CountsAttentionMap.lean, which shows the like for attention's calls, and
Johnson/HonestTrace/CountsHeadMap.lean for the head's: the names and the form of the statements are
theirs.

What is shown. One theorem a definition, from the leaves up, each of the form ‹the definition› at
the reading "φ of cell" = φ (‹the definition› at cell):
  `sumN_map` (a sum: φ of the sum is the sum of φ of the summand), `ten_map`, `xb_map`, `xs_map`,
    `dig_map`, `recip_map`, `wt_map`, `attO_map`, `gated_map`, `accDense_map`, `accRouted_map`,
    `accD_map`, `accQK_map`, `rotQK_map`, `selLr_map`;
  `gamG_map`: the main theorem: the products in a segment's key.

What is defined. `atOwnF`, `ownGF`: the text of `atOwn` and `ownG` (Honest/K3/WitOwner.lean) without
the lift: the cell in the base field.
  `ownG_lift`: `ownG` is `ownGF`, lifted.
  `gamG_own`: so the products in a key at the seated reading are those at `ownGF`, lifted.

Imported. Honest/K3/WitOwner.lean and what stands beneath it.

Users. Honest/K3/Tab/RingGKey.lean [not in this library], Honest/K3/Tab/TabG.lean,
Honest/K3/Tab/TabALaw.lean and Honest/K3/Tab/TabHSeat.lean import this file.

Limits. Of `affG`, the part of a key that is affine in the cells, and of a whole key:
Honest/K3/Tab/RingGKey.lean [not in this library]. Nothing says how long anything takes.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.WitOwner

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.TabG
open OnBytes.Model OnBytes.Ends.G

section Ring

variable {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')

/-- A map of rings commutes with G.sumN. -/
theorem sumN_map (n : ℕ) (f : ℕ → R) : φ (sumN n f) = sumN n fun k => φ (f k) := by
  have h : ∀ (l : List ℕ) (a : R),
      φ (l.foldl (fun s k => s + f k) a) = l.foldl (fun s k => s + φ (f k)) (φ a) := by
    intro l
    induction l with
    | nil => intro a; rfl
    | cons x xs ih => intro a; rw [List.foldl_cons, List.foldl_cons, ih, map_add]
  unfold sumN
  rw [h, map_zero]

variable (P : Layer.Pub) (g : ℕ) (cell : NameG → R)

/-- A tensor's entry at the reading "φ of cell" is φ of the entry at cell. -/
theorem ten_map (nm : String) (inst x i : ℕ) :
    ten P (fun n => φ (cell n)) nm inst x i = φ (ten P cell nm inst x i) := by
  unfold ten
  cases P.y.T_ nm with
  | none => exact (map_zero φ).symm
  | some X => simp only [sumN_map, map_mul, map_pow, map_ofNat]

/-- The like for a channel of a stream's matrix. -/
theorem xb_map (M0 x i : ℕ) : xb P (fun n => φ (cell n)) M0 x i = φ (xb P cell M0 x i) := by
  simp only [xb, sumN_map, map_mul, map_pow, map_ofNat]

/-- The like for the residual stream. -/
theorem xs_map (s x i : ℕ) : xs P (fun n => φ (cell n)) s x i = φ (xs P cell s x i) := by
  unfold xs
  split_ifs
  · exact xb_map φ P cell _ x i
  · exact xb_map φ P cell _ x i
  · exact ten_map φ P cell _ _ x i

/-- The like for a digit of a norm's row. -/
theorem dig_map (ν j i : ℕ) : dig P (fun n => φ (cell n)) ν j i = φ (dig P cell ν j i) := by
  simp only [dig, map_add, ten_map, map_ofNat]

/-- The like for a norm's reciprocal. -/
theorem recip_map (ν i : ℕ) : recip P (fun n => φ (cell n)) ν i = φ (recip P cell ν i) := by
  simp only [recip, sumN_map, map_mul, map_pow, map_ofNat, dig_map]

/-- The like for a weight. -/
theorem wt_map (X l : ℕ) (idx : List ℕ) :
    wt P (fun n => φ (cell n)) X l idx = φ (wt P cell X l idx) := by
  unfold wt
  cases (P.wsLay.unitOf X l).bind (fun ui => P.wsLay.U[ui]?) with
  | none => exact (map_zero φ).symm
  | some u => simp only [sumN_map, map_mul, map_pow, map_ofNat]

/-- The like for the attention output. -/
theorem attO_map (lam k2 i : ℕ) :
    attO P g (fun n => φ (cell n)) lam k2 i = φ (attO P g cell lam k2 i) := by
  unfold attO
  split_ifs
  · exact ten_map φ P cell _ _ _ _
  · exact (map_intCast φ _).symm

/-- The like for the gated product. -/
theorem gated_map (lam k i : ℕ) :
    gated P (fun n => φ (cell n)) lam k i = φ (gated P cell lam k i) := by
  simp only [gated, map_mul, ten_map]

/-- The like for the accumulator of the gate or the up product, not routed. -/
theorem accDense_map (up : Bool) (lam x i : ℕ) :
    accDense P g (fun n => φ (cell n)) up lam x i = φ (accDense P g cell up lam x i) := by
  simp only [accDense, sumN_map, map_mul, ten_map, wt_map]

/-- The like for the same, routed. -/
theorem accRouted_map (up : Bool) (lam x i : ℕ) :
    accRouted P g (fun n => φ (cell n)) up lam x i = φ (accRouted P g cell up lam x i) := by
  simp only [accRouted, sumN_map, map_mul, ten_map, wt_map]

/-- The like for the down product's accumulator. -/
theorem accD_map (lam x i : ℕ) :
    accD P g (fun n => φ (cell n)) lam x i = φ (accD P g cell lam x i) := by
  unfold accD
  split_ifs <;> simp only [map_add, map_zero, sumN_map, map_mul, ten_map, wt_map, gated_map]

/-- The like for a coordinate of q and k before the rotation. -/
theorem accQK_map (lam hd cd i : ℕ) :
    accQK P g (fun n => φ (cell n)) lam hd cd i = φ (accQK P g cell lam hd cd i) := by
  simp only [accQK, sumN_map, map_mul, ten_map, wt_map]

/-- The like for an entry of q and k after the rotation. -/
theorem rotQK_map (lam x i : ℕ) :
    rotQK P g (fun n => φ (cell n)) lam x i = φ (rotQK P g cell lam x i) := by
  unfold rotQK
  simp only []
  split_ifs <;> simp only [map_add, map_sub, map_mul, map_intCast, accQK_map]

/-- The like for the chosen expert's logit. -/
theorem selLr_map (lam i : ℕ) :
    selLr P (fun n => φ (cell n)) lam i = φ (selLr P cell lam i) := by
  simp only [selLr, sumN_map, map_mul, ten_map]

/-- **The products in a segment's key commute with a map of rings.** -/
theorem gamG_map (sn : String) (lam x i : ℕ) :
    gamG P g (fun n => φ (cell n)) sn lam x i = φ (gamG P g cell sn lam x i) := by
  unfold gamG
  simp only [apply_ite φ, map_zero, map_mul, map_pow, map_ofNat, sumN_map, ten_map, wt_map,
    attO_map, accRouted_map, accDense_map, accD_map, recip_map, xs_map, rotQK_map, selLr_map]

end Ring

/-! ## The seated reading -/

/-- `atOwn` without the lift. -/
def atOwnF (X : OnBytes.Model.Verify.Public) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F)
    (link a r c : ℕ) : Cb.Gl.F :=
  match (tlOf X link).mats[a]? with
  | some M => cell (ownerOf X link M).1 (ownerOf X link M).2 r (M.ttOff + c)
  | none => 0

/-- `ownG` without the lift. -/
def ownGF (X : OnBytes.Model.Verify.Public) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F)
    (entry : ℕ → ℕ → Cb.Gl.F) (link : ℕ) : NameG → Cb.Gl.F
  | .cell a r c => atOwnF X cell link a r c
  | .w r c => entry r c

/-- **The seated reading is the reading in the base field, lifted.** -/
theorem ownG_lift (X : OnBytes.Model.Verify.Public) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F)
    (entry : ℕ → ℕ → Cb.Gl.F) (link : ℕ) :
    ownG X cell entry link = fun n => algebraMap Cb.Gl.F Cb.Gl.E (ownGF X cell entry link n) := by
  funext n
  cases n with
  | w r c => rfl
  | cell a r c =>
    show atOwn X cell link a r c = algebraMap Cb.Gl.F Cb.Gl.E (atOwnF X cell link a r c)
    unfold atOwn atOwnF
    cases (tlOf X link).mats[a]? with
    | none => exact (map_zero _).symm
    | some M => rfl

/-- **The products in a key at the seated reading are those in the base field, lifted.** -/
theorem gamG_own (X : OnBytes.Model.Verify.Public) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F)
    (entry : ℕ → ℕ → Cb.Gl.F) (link : ℕ) (P : Layer.Pub) (g : ℕ) (sn : String) (lam x i : ℕ) :
    gamG P g (ownG X cell entry link) sn lam x i =
      algebraMap Cb.Gl.F Cb.Gl.E (gamG P g (ownGF X cell entry link) sn lam x i) := by
  rw [ownG_lift, gamG_map]

end ProofFile.Honest.K3.TabG

#print axioms ProofFile.Honest.K3.TabG.sumN_map
#print axioms ProofFile.Honest.K3.TabG.ten_map
#print axioms ProofFile.Honest.K3.TabG.xb_map
#print axioms ProofFile.Honest.K3.TabG.xs_map
#print axioms ProofFile.Honest.K3.TabG.dig_map
#print axioms ProofFile.Honest.K3.TabG.recip_map
#print axioms ProofFile.Honest.K3.TabG.wt_map
#print axioms ProofFile.Honest.K3.TabG.attO_map
#print axioms ProofFile.Honest.K3.TabG.gated_map
#print axioms ProofFile.Honest.K3.TabG.accDense_map
#print axioms ProofFile.Honest.K3.TabG.accRouted_map
#print axioms ProofFile.Honest.K3.TabG.accD_map
#print axioms ProofFile.Honest.K3.TabG.accQK_map
#print axioms ProofFile.Honest.K3.TabG.rotQK_map
#print axioms ProofFile.Honest.K3.TabG.selLr_map
#print axioms ProofFile.Honest.K3.TabG.gamG_map
#print axioms ProofFile.Honest.K3.TabG.ownG_lift
#print axioms ProofFile.Honest.K3.TabG.gamG_own
