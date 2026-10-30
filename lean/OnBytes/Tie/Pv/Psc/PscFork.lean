-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Psc/PscFork.lean: what putting values under slots (`Fork.hide`, `Fork.hideRun`,
OnBytes/Model/Hide.lean) does to the state of a sub-proof: which slots it fills, with what, and what
it leaves as it was.

Definitions, and theorems with their proofs.

Main names:
  `Sized F`: the three arrays that hold a slot's shown value, factor and mark have one entry for
    each slot. `Fork.hide` tests this of the marks alone, and writing beyond an array's end does
    nothing, so the laws on what a slot holds require it; `hide_sized`, `hideRun_sized`,
    `took_sized`, `owe_sized`, `paid_sized`: the steps keep it; `slots_sized`: setting up the slots
    gives it.
  `Filled F j`: slot j is marked as filled.
  `hide_ok`: one value: the slot was free and below the number of slots; afterwards it is filled and
    holds the value and the factor; every other slot is as before; nothing else of the state
    changes.
  `hideRun_ok`: the same for a run of values under the slots first, first + 1, ..
  `Same F G`: G differs from F at most in the three arrays.

Limits: nothing is said where a step refuses. Nothing on soundness, on an honest prover or on
hiding.


-/
import OnBytes.Tie.Pv.Psc.PscRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.PscRun
open OnBytes OnBytes.Model

/-- The three arrays have one entry for each slot. -/
def Sized (F : Fork) : Prop := F.vp.size = F.ns ∧ F.mf.size = F.ns ∧ F.gotF.size = F.ns

/-- Slot j is marked as filled. -/
def Filled (F : Fork) (j : Nat) : Prop := F.gotF.getD j false = true

/-- G differs from F at most in what lies under the slots. -/
def Same (F G : Fork) : Prop := G = { F with vp := G.vp, mf := G.mf, gotF := G.gotF }

/-- Every state is the same as itself. -/
theorem Same.refl (F : Fork) : Same F F := rfl

/-- `Same` goes through a state between. -/
theorem Same.trans {F G H : Fork} (h : Same F G) (h' : Same G H) : Same F H := by
  unfold Same at *
  rw [h', h]

/-- The number of slots is the same. -/
theorem Same.ns {F G : Fork} (h : Same F G) : G.ns = F.ns := by
  rw [h]

/-- The next slot is the same. -/
theorem Same.next {F G : Fork} (h : Same F G) : G.next = F.next := by
  rw [h]

/-- Taking slots keeps the sizes. -/
theorem took_sized {F : Fork} (n : Nat) (h : Sized F) : Sized (took F n) := h

/-- The entry that was written. -/
theorem getD_set_self {α : Type} (a : Array α) (j : Nat) (x d : α) (h : j < a.size) :
    (a.set! j x).getD j d = x := by
  simp [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, h]

/-- An entry that was not written. -/
theorem getD_set_other {α : Type} (a : Array α) (j i : Nat) (x d : α) (h : i ≠ j) :
    (a.set! j x).getD i d = a.getD i d := by
  simp [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Ne.symm h]

/-- One value is put under a slot. -/
theorem hide_ok (F G : Fork) (j : Nat) (y factor : E) (hF : Sized F)
    (h : F.hide j y factor = some G) :
    j < F.ns ∧ ¬ Filled F j ∧ Same F G ∧ Sized G ∧ Filled G j ∧ G.vp.getD j zeroE = y ∧
      G.mf.getD j zeroE = factor ∧
      ∀ i, i ≠ j → G.vp.getD i zeroE = F.vp.getD i zeroE ∧ G.mf.getD i zeroE = F.mf.getD i zeroE ∧
        (Filled G i ↔ Filled F i) := by
  unfold Fork.hide at h
  split at h
  · rename_i hq
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at hq
    obtain rfl := Option.some.inj h
    obtain ⟨h1, h2, h3⟩ := hF
    refine ⟨hq.1.1, ?_, rfl, ⟨by simp [h1], by simp [h2], by simp [h3]⟩, ?_, ?_, ?_, ?_⟩
    · unfold Filled
      have hj : j < F.gotF.size := by rw [h3]; exact hq.1.1
      have e : F.gotF.getD j false = F.gotF.getD j true := by
        simp [Array.getD_eq_getD_getElem?, hj]
      rw [e, hq.2]
      simp
    · exact getD_set_self _ _ _ _ (by rw [h3]; exact hq.1.1)
    · exact getD_set_self _ _ _ _ (by rw [h1]; exact hq.1.1)
    · exact getD_set_self _ _ _ _ (by rw [h2]; exact hq.1.1)
    · intro i hi
      refine ⟨getD_set_other _ _ _ _ _ hi, getD_set_other _ _ _ _ _ hi, ?_⟩
      show (F.gotF.set! j true).getD i false = true ↔ F.gotF.getD i false = true
      rw [getD_set_other _ _ _ _ _ hi]
  · simp at h

/-- The steps of a run of values. -/
theorem hideSteps_ok (factor : E) : ∀ (l : List E) (first : Nat) (F : Fork) (x : Nat × Fork),
    Sized F → l.foldlM (Fork.hideStep factor) (first, F) = some x →
    x.1 = first + l.length ∧ (l ≠ [] → first + l.length ≤ F.ns) ∧
      Same F x.2 ∧ Sized x.2 ∧
      (∀ i, i < l.length → ¬ Filled F (first + i) ∧ Filled x.2 (first + i) ∧
        x.2.vp.getD (first + i) zeroE = l.getD i zeroE ∧ x.2.mf.getD (first + i) zeroE = factor) ∧
      ∀ j, (j < first ∨ first + l.length ≤ j) →
        x.2.vp.getD j zeroE = F.vp.getD j zeroE ∧ x.2.mf.getD j zeroE = F.mf.getD j zeroE ∧
          (Filled x.2 j ↔ Filled F j)
  | [], first, F, x, hF, h => by
    have hx : (first, F) = x := by simpa using h
    subst hx
    refine ⟨rfl, fun h => absurd rfl h, Same.refl F, hF, fun i hi => absurd hi (by simp),
      fun j _ => ⟨rfl, rfl, Iff.rfl⟩⟩
  | y :: l, first, F, x, hF, h => by
    rw [List.foldlM_cons] at h
    cases hq : Fork.hideStep factor (first, F) y with
    | none => simp [hq] at h
    | some s =>
      rw [hq] at h
      have h2 : l.foldlM (Fork.hideStep factor) s = some x := by simpa using h
      simp only [Fork.hideStep] at hq
      cases hh : F.hide first y factor with
      | none => simp [hh] at hq
      | some H =>
        rw [hh] at hq
        obtain rfl : (first + 1, H) = s := by simpa using hq
        obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hide_ok F H first y factor hF hh
        obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hideSteps_ok factor l (first + 1) H x a4 h2
        refine ⟨by rw [b1, List.length_cons]; omega, ?_, a3.trans b3, b4, ?_, ?_⟩
        · intro _
          simp only [List.length_cons]
          by_cases hl : l = []
          · subst hl
            simp only [List.length_nil]
            omega
          · have b2' := b2 hl
            rw [a3.ns] at b2'
            omega
        · intro i hi
          cases i with
          | zero =>
            obtain ⟨c1, c2, c3⟩ := b6 first (Or.inl (by omega))
            exact ⟨a2, c3.2 a5, by rw [Nat.add_zero, c1, a6]; rfl, by rw [Nat.add_zero, c2, a7]⟩
          | succ i =>
            have hi' : i < l.length := by simpa using hi
            obtain ⟨c1, c2, c3, c4⟩ := b5 i hi'
            have e : first + (i + 1) = first + 1 + i := by omega
            rw [e]
            refine ⟨fun hf => c1 ((a8 _ (by omega)).2.2.2 hf), c2, ?_, c4⟩
            rw [c3]
            rfl
        · intro j hj
          have hj1 : j ≠ first := by
            rcases hj with hj | hj
            · omega
            · simp only [List.length_cons] at hj
              omega
          obtain ⟨c1, c2, c3⟩ := b6 j (by
            rcases hj with hj | hj
            · exact Or.inl (by omega)
            · simp only [List.length_cons] at hj
              exact Or.inr (by omega))
          obtain ⟨d1, d2, d3⟩ := a8 j hj1
          exact ⟨c1.trans d1, c2.trans d2, c3.trans d3⟩

/-- A run of values is put under the slots first, first + 1, .. -/
theorem hideRun_ok (F G : Fork) (first : Nat) (v : Array E) (factor : E) (hF : Sized F)
    (h : F.hideRun first v factor = some G) :
    Same F G ∧ Sized G ∧
      (∀ i, i < v.size → first + i < F.ns ∧ ¬ Filled F (first + i) ∧ Filled G (first + i) ∧
        G.vp.getD (first + i) zeroE = v.getD i zeroE ∧ G.mf.getD (first + i) zeroE = factor) ∧
      ∀ j, (j < first ∨ first + v.size ≤ j) →
        G.vp.getD j zeroE = F.vp.getD j zeroE ∧ G.mf.getD j zeroE = F.mf.getD j zeroE ∧
          (Filled G j ↔ Filled F j) := by
  unfold Fork.hideRun at h
  split at h
  · rename_i x hx
    obtain rfl := Option.some.inj h
    rw [← Array.foldlM_toList] at hx
    obtain ⟨-, b2, b3, b4, b5, b6⟩ := hideSteps_ok factor v.toList first F x hF hx
    refine ⟨b3, b4, ?_, ?_⟩
    · intro i hi
      have hi' : i < v.toList.length := by simpa using hi
      obtain ⟨c1, c2, c3, c4⟩ := b5 i hi'
      have hne : v.toList ≠ [] := by
        intro e
        rw [e] at hi'
        simp at hi'
      have b2' := b2 hne
      refine ⟨by omega, c1, c2, ?_, c4⟩
      rw [c3]
      simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
    · intro j hj
      exact b6 j (by simpa using hj)
  · simp at h

/-- Putting a value under a slot keeps the sizes. -/
theorem hide_sized {F G : Fork} {j : Nat} {y factor : E} (hF : Sized F)
    (h : F.hide j y factor = some G) : Sized G := (hide_ok F G j y factor hF h).2.2.2.1

/-- Putting a run of values under slots keeps the sizes. -/
theorem hideRun_sized {F G : Fork} {first : Nat} {v : Array E} {factor : E} (hF : Sized F)
    (h : F.hideRun first v factor = some G) : Sized G := (hideRun_ok F G first v factor hF h).2.1

/-- Setting up the slots makes the three arrays of that size. -/
theorem slots_sized (F : Fork) (n : Nat) : Sized (F.slots n) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Fork.slots]

/-- Entering an owed claim keeps the sizes. -/
theorem owe_sized {F : Fork} (what : String) (h : Sized F) : Sized (F.owe what).2 := h

/-- Marking an owed claim as added keeps the sizes. -/
theorem paid_sized {F : Fork} (i : Nat) (h : Sized F) : Sized (F.paid i) := h

end OnBytes.PscRun

#print axioms OnBytes.PscRun.hide_ok
#print axioms OnBytes.PscRun.hideRun_ok
