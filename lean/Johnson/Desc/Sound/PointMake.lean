-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PointMake.lean: TWO OF THE FOUR STEPS AT "LIN point" (Johnson/Desc/Sound/PointTie.lean), PAID BY MAKE. Two statements written as def … : Prop, and their proofs.

  PointRiders = (S5): no mark and the two pins of the slot's own ride back over the block, to the witness that the table's extractor lays. FROM: what was handed to the chain stays (the seat's make) · the slot's pins read the
    oracles through their tenant's tree alone (a condition on the letter pin₁) · W's and the index masks' trees lie below the block's base (two comparisons of numbers: NumbersS.sorted with "the base is from lo on") · the
    extractor keeps both pins (it lays the cells; a pin reads its member's own components alone).
  PointProm = (S0): the table's promise behind the block. FROM: the promise in front · what was handed stays · the slot's own condition reads below lo (OcReadsBelow, Johnson/Desc/Sound/OcRides.lean) · AND THE TWO SHARED CLAUSES BEHIND
    (the promise on the table; the book-keeping at border 2), which stay the block's files' to show: asked at the acting part's value behind the block, under the same two in front.
By cellStays, colStays (Johnson/Desc/Sound/StringsStay.lean), out_behind (SendLaw.lean), ocRides: CALLED.

Limits. Rules under letters. The conditions on letters are owed at the fillings.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PointTie
import Johnson.Desc.Sound.OcRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared

/-- **(S5): what rides back over the point.** -/
def PointRiders : Prop :=
  ∀ (P₁ S₂ Cl Wt : Type) (C : CK) (Fr : Frame) (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
    (pt : Piece C Fr (P₁ × S₂) Cl Wt) (E : (P₁ × S₂) × Fr.E.Str → Wt → Wt),
    (∀ a τ b, pt.ior.red.out a τ = some b → b.1.1 = a.1.1) →
    (∀ j t p (y y' : Strs) w, (∀ x, y'.col j x = y.col j x) → Mg.pin₁ j t p y w → Mg.pin₁ j t p y' w) →
    N.w.1 < pt.base → N.index.1 < pt.base →
    (∀ a p y w, Mg.pin₁ N.w.1 N.w.2 p y w → Mg.pin₁ N.w.1 N.w.2 p y (E a w)) →
    (∀ a p y w, Mg.pin₁ N.index.1 N.index.2 p y w → Mg.pin₁ N.index.1 N.index.2 p y (E a w)) →
    ∀ a τ b w i, i ∈ [ItemS.unmarked1, .pinI, .pinV] → pt.ior.red.out a τ = some b →
      ownItem N Mg i b w → ownItem N Mg i a (E a w)

/-- **(S0): the promise behind the point.** -/
def PointProm : Prop :=
  ∀ (P₁ S₂ Cl Wt : Type) (C : CK) (Fr : Frame) (N : NumbersS) (Pm : PromMeaning S₂)
    (Oc : P₁ → Strs → Prop) (split : Bool) (lo : ℕ)
    (f pt : Piece C Fr (P₁ × S₂) Cl Wt) (r : List (Piece C Fr (P₁ × S₂) Cl Wt)),
    (∀ a τ b, pt.ior.red.out a τ = some b → b.1.1 = a.1.1) →
    OcReadsBelow lo Oc → lo ≤ pt.base →
    (∀ a τ b, promQ N Pm split f (pt :: r) 1 ((actQ N f (pt :: r) 1).2 a) →
      pt.ior.red.out a τ = some b → promQ N Pm split f (pt :: r) 2 ((actQ N f (pt :: r) 2).2 b)) →
    ∀ a τ b, onQ₂ N Pm Oc split f (pt :: r) 1 a → pt.ior.red.out a τ = some b →
      onQ₂ N Pm Oc split f (pt :: r) 2 b

theorem pointRiders : PointRiders := by
  intro P₁ S₂ Cl Wt C Fr N Mg pt E hK hR hw hi hEw hEi a τ b w i hmem hb h
  have e := hK a τ b hb
  have e2 := out_behind pt a b τ hb
  have back : ∀ j, j < pt.base → ∀ x, (strsOf Fr a.2).col j x = (strsOf Fr b.2).col j x := by
    intro j hj x
    rw [e2]
    exact (colStays C Fr pt.base pt.ds a.2 τ j x hj).symm
  rcases List.mem_cons.1 hmem with rfl | hmem
  · have h' : Mg.unmarked1 b.1.1 := h
    rw [e] at h'
    exact h'
  rcases List.mem_cons.1 hmem with rfl | hmem
  · have h' : Mg.pin₁ N.index.1 N.index.2 b.1.1 (strsOf Fr b.2) w := h
    rw [e] at h'
    exact hEi a _ _ _ (hR _ _ _ _ _ _ (back _ hi) h')
  · obtain rfl := List.mem_singleton.1 hmem
    have h' : Mg.pin₁ N.w.1 N.w.2 b.1.1 (strsOf Fr b.2) w := h
    rw [e] at h'
    exact hEw a _ _ _ (hR _ _ _ _ _ _ (back _ hw) h')

theorem pointProm : PointProm := by
  intro P₁ S₂ Cl Wt C Fr N Pm Oc split lo f pt r hK hOc hlo hP a τ b ha hb
  exact ⟨hP a τ b ha.1 hb,
    ocRides (P₁ × S₂) P₁ Cl Wt C Fr Prod.fst lo Oc pt hOc hlo hK a τ b ha.2 hb⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.pointRiders
#print axioms VerifiableInference.Desc.Sound.pointProm
