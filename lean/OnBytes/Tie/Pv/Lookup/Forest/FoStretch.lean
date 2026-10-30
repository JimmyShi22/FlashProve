-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoStretch.lean.
A relation between two states of a sub-proof: the next n slots are taken and filled. It is made for
the stretches of the byte-level verifier's lookup routine; no statement of this file speaks of a
routine's run.

States:
  Stretch F G n: from F to G the next n slots are taken and filled, and nothing else is turned: G
    differs from F with n more slots taken at most in what lies under the slots; a slot is filled
    in G if and only if it was filled in F or is one of the n; what lies under every other slot,
    free or filled, stays.
  Stretch.refl, Stretch.trans, Stretch.next.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoTieKit
import OnBytes.Tie.Pv.Psc.PscRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- The next n slots are taken and filled; nothing else is turned. -/
structure Stretch (F G : Fork) (n : ℕ) : Prop where
  same : Same (took F n) G
  filled : ∀ j, Filled G j ↔ Filled F j ∨ (F.next ≤ j ∧ j < F.next + n)
  out : ∀ j, (j < F.next ∨ F.next + n ≤ j) →
    G.vp.getD j zeroE = F.vp.getD j zeroE ∧ G.mf.getD j zeroE = F.mf.getD j zeroE

theorem Stretch.refl (F : Fork) : Stretch F F 0 :=
  ⟨rfl, fun j => ⟨Or.inl, fun h => h.elim id fun hh => absurd hh.2 (by omega)⟩,
    fun _ _ => ⟨rfl, rfl⟩⟩

theorem Stretch.next {F G : Fork} {n : ℕ} (h : Stretch F G n) : G.next = F.next + n :=
  h.same.next

theorem Stretch.trans {F G H : Fork} {n m : ℕ} (h1 : Stretch F G n) (h2 : Stretch G H m) :
    Stretch F H (n + m) where
  same := by
    have := (same_took h1.same m).trans h2.same
    rwa [took_took] at this
  filled := fun j => by
    rw [h2.filled, h1.filled, h1.next]
    constructor
    · rintro ((hj | hj) | hj)
      · exact Or.inl hj
      · exact Or.inr ⟨hj.1, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · rintro (hj | hj)
      · exact Or.inl (Or.inl hj)
      · by_cases hlt : j < F.next + n
        · exact Or.inl (Or.inr ⟨hj.1, hlt⟩)
        · exact Or.inr ⟨by omega, by omega⟩
  out := fun j hj => by
    have o2 := h2.out j (by rw [h1.next]; omega)
    have o1 := h1.out j (by omega)
    exact ⟨o2.1.trans o1.1, o2.2.trans o1.2⟩

end Fo
