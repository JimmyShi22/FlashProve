-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/DoorOfPromise.lean: the code switch: AT THE BORDER IN FRONT OF A
SWITCH THE TABLE OF JOINTS' OWN PROMISE GIVES WHAT CarryClosed.lean's doorZ_at_switch ASKS OF THE
STATE: so there the cured way in of «carry» is the elder one.
  stand_of_promise   at a state without a mark inside the promise at border k, with the place p
                     behind it: the state stands where the table says the chain is to stand there
                     (the first clause of First/Borders.lean's shapeAt: standOf s = standAt links p)
  out_of_between, out_of_headFront  a state that stands between the links, or in the head's front,
                     is outside a link; in the head's front its part «here» is the head's
  doorZ_of_promise   THE STATEMENT: doorZ Z m s = ProofFile.doorAtK2 Z m s at such a state, where the
                     table says «between», or «the head's front» at a place of the sort .head
WHAT IT IS FOR. The fourth tie (K2Caller/TieFourR.lean) asks «the sentence's way in
is the seated sub-protocol's door». As an unfenced sentence over all states that is FALSE at the
cured way in; under the promise it follows from this and the elder door's own fact.
LIMITS. hst is a closed fact on the written list of places: by First/Borders.lean's standAt a place
of a segment with piece ≤ 1 and the back's K2 stand «between», the head's segment's piece 2 «the
head's front» [by reading]: not evaluated here. No soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.CarryClosed
import Johnson.Top.H0.K2Caller.TiesFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Meaning Numbers standOf standAt)

variable {A P W : Type} {F : Frame} (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
  (ps : List VerifiableInference.Desc.Place) (get : A → P × First.S) (k : ℕ)

theorem stand_of_promise (a : A × F.E.Str) (ha : onQ N Mg links ps get k a)
    (hm : ¬ (get a.1).2.failed ≠ none) (p : VerifiableInference.Desc.Place)
    (hp : ps[k]? = some p) :
    standOf (get a.1).2 = standAt links p := by
  obtain ⟨-, h⟩ := ha
  rcases h with h | ⟨hb, -⟩
  · exact absurd h hm
  · simp only [Bool.and_eq_true] at hb
    have hh := hb.1.1.1.1.1
    rw [hp] at hh
    unfold VerifiableInference.Desc.First.shapeAt at hh
    simp only [Bool.and_eq_true, beq_iff_eq] at hh
    exact hh.1.1

theorem out_of_between (s : First.S) (h : standOf s = .between) :
    s.inLink = false ∧ ∀ a, s.here ≠ .head a := by
  unfold standOf at h
  cases hq : s.here with
  | between =>
    exact ⟨by simp [First.S.inLink, First.S.fork?, hq], fun a e => by cases e⟩
  | lay a => rw [hq] at h; cases h
  | att a => rw [hq] at h; cases h
  | head a =>
    rw [hq] at h
    simp only at h
    split at h <;> cases h
  | fin a => rw [hq] at h; cases h
  | mem a => rw [hq] at h; cases h

theorem out_of_headFront (s : First.S) (h : standOf s = .headFront) :
    s.inLink = false ∧ ∃ a, s.here = .head a := by
  unfold standOf at h
  cases hq : s.here with
  | between => rw [hq] at h; cases h
  | lay a => rw [hq] at h; cases h
  | att a => rw [hq] at h; cases h
  | head a =>
    rw [hq] at h
    simp only at h
    cases hi : s.inLink with
    | false => exact ⟨rfl, a, rfl⟩
    | true =>
      rw [hi] at h
      cases h
  | fin a => rw [hq] at h; cases h
  | mem a => rw [hq] at h; cases h

/-- **Under the promise, at the switch's own border, the cured way in is the elder one.** -/
theorem doorZ_of_promise (Z : ProofFile.Pub) (m : ℕ) (a : A × F.E.Str)
    (ha : onQ N Mg links ps get k a) (hm : ¬ (get a.1).2.failed ≠ none)
    (p : VerifiableInference.Desc.Place) (hp : ps[k]? = some p)
    (hst : (standAt links p = .between ∧ (ProofFile.pAtK2 Z m).stands ≠ .head) ∨
      standAt links p = .headFront) :
    doorZ Z m (get a.1).2 = ProofFile.doorAtK2 Z m (get a.1).2 := by
  have hs := stand_of_promise N Mg links ps get k a ha hm p hp
  rcases hst with ⟨h1, h2⟩ | h1
  · exact doorZ_at_switch Z m _ (out_of_between _ (hs.trans h1)).1 fun e => absurd e h2
  · obtain ⟨o1, o2⟩ := out_of_headFront _ (hs.trans h1)
    exact doorZ_at_switch Z m _ o1 fun _ => o2

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.doorZ_of_promise
