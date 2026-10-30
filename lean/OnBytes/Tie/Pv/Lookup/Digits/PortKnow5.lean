-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Digits/PortKnow5.lean: three statements of
OnBytes/Tie/Pv/Lookup/Digits/PortKnow.lean at the layout `digL5`
(OnBytes/Tie/Pv/Lookup/Digits/PortEnds.lean), so that one layout carries the knowledge soundness of
the lookup on the digits and its output claim.

Main names:
  `forIn_dig5`: `forIn` at `digL5` is "R0, and every low digit lies in [0, 2^t2D0), every high digit
    in [0, 2^t2D1)", under `shapeTest2`: `forIn` reads the layout through K alone, and the K of
    `digL5` is that of `digL`.
  `forA5_bAt`: the places of the planes in `forA` at `digL5` are those of `portQJ tl en`, for every
    joint row u < 2^d, under `PortOK tl` (OnBytes/Tie/Pv/Lookup/Digits/PortSeam.lean).
  `forA5_pads`: the padding in `forA` at `digL5` is that of `portQJ tl en`.
Limits: from 2^d on nothing is stated of the cell of `digL5`. `holeD_dig`
(OnBytes/Tie/Pv/Lookup/Digits/PortKnow.lean) reads no layout and stands as it is. Knowledge
soundness at `digL5` itself is not here: it is `Fo.holeD_port5`
(OnBytes/Tie/Pv/Lookup/Forest/FoDig5.lean).

-/
import OnBytes.Tie.Pv.Lookup.Digits.PortEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.DgP
open OnBytes OnBytes.Model CbQ Cb.LdLkp Cb.Lkp Cb.Fo Iop IOR TWhole

variable {J₀ : Type} {E : Type} [Field E] {tl : HTailF2}

/-- The block's own joint before, at `digL5`, in the digits' words. -/
theorem forIn_dig5 {pp : ℕ} (h : shapeTest2 tl pp = true) (en : Ent3 → J₀) (mk : ℕ → J₀) (jLK : ℕ)
    {St₀ Kc M Wp : Type} {Ex : ExtSpec}
    (R0 : Rels Kc St₀ Ex (M × Wp)) (msg₀ : M → J₀ → E) :
    Cb.Fo.forIn E tl.f9 (digL5 E tl en mk jLK St₀) R0 msg₀ =
      ⟨fun x y w => R0.rel x y w ∧ DigIn tl en (msg₀ w.1), fun a w => R0.relR a w ∧ DigIn tl en
          (msg₀ w.1), R0.on, R0.core⟩ :=
  forIn_dig h en mk jLK R0 msg₀

variable [Fintype E] [Fintype J₀] [DecidableEq J₀]

/-- The places of the planes in `forA` at `digL5` are those of the record of the digits, below 2^d.
-/
theorem forA5_bAt (hP : PortOK tl) (en : Ent3 → J₀) (mk : ℕ → J₀) (jLK : ℕ) (St₀ : Type) {u : ℕ} (hu
    : u < 2 ^ tl.f9.d) (j : ℕ) :
    (forA E tl.f9 (digL5 E tl en mk jLK St₀)).bAt u j = some ((portQJ tl en).bAt u j) := by
  have hlt : u % 2 ^ tl.f9.cK < tl.f9.NC := by
    rw [← hP.full]
    exact Nat.mod_lt _ (by positivity)
  have hu' : u < 2 ^ (tl.f9.kT + tl.f9.cK) := hu
  have ht : u / 2 ^ tl.f9.cK < 2 ^ tl.f9.kT := by
    refine Nat.div_lt_of_lt_mul ?_
    rw [← pow_add, Nat.add_comm]
    exact hu'
  show (FoNums.cellOf tl.f9 u j).map (fun x => (digL5 E tl en mk jLK St₀).bc x.1 x.2.1 x.2.2) = _
  unfold FoNums.cellOf
  rw [if_pos hlt]
  show some ((digL5 E tl en mk jLK St₀).bc (u / 2 ^ tl.f9.cK) (u % 2 ^ tl.f9.cK) j) = _
  rw [digL5_bc en mk jLK St₀ ht, dgP_bcJ]

/-- The padding in `forA` at `digL5` is that of the record of the digits. -/
theorem forA5_pads (en : Ent3 → J₀) (mk : ℕ → J₀) (jLK : ℕ) (St₀ : Type) :
    (forA E tl.f9 (digL5 E tl en mk jLK St₀)).pads = (portQJ tl en).pads := rfl

#print axioms forIn_dig5
#print axioms forA5_bAt
#print axioms forA5_pads

end OnBytes.DgP
