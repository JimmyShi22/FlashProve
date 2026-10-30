-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/ForkPromise.lean: THE SMALLNESS TEST: IN FRONT OF A DRAW THE OPEN SEGMENT'S
LEDGER OF CLAIMS (`S.fork?`) IS THERE: OUT OF THE FIRST TABLE'S PROMISE. Statements with their
proofs; one test with code.


Main names (namespace `VerifiableInference.Desc.First.K8`).
  **`fork_of_stand`**: where the verifier's state stands in an open segment (`standOf s = .link
    sub`, Johnson/Desc/First/Borders.lean): ∃ F, `s.fork? = some F`. At the output head's segment
    `standOf` itself asks `S.inLink`, which is `s.fork?.isSome`.
  `inLinkAtB links ps k`: the test: the list has a place at number k, and `standAt` says there that
    a segment is open. `inLinkAtB_full`: it accepts at all twenty-five draws of the full size: BY
    LEAN'S KERNEL. `stand_full`: the fact, for l ≤ 24.
  `shapeAt_of_onQ`: the promise at a state without a mark holds the test `shapeAt`.
    **`fork_of_onQ`**: the three joined, at `Sound.linksFull`, its written list of places and
    `drawAt l` (Johnson/Desc/First/K8/TiePromise.lean).

Every "there is", walked. F: tied by `fork? = some F`. p, sub in `stand_full`: tied by the list's
entry and by `standAt`.
Limits. IT STANDS ON THE PROMISE AND ON "NO MARK", not on the fold from the first state. Nothing is
said of what the ledger holds. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.K8.TiePromise

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers start openSets flatPlacesOf
  shapeAt standOf standAt Stand)

/-- **Where a segment is open the ledger of claims is there.** -/
theorem fork_of_stand (s : S) (sub : ModelPart) (h : standOf s = .link sub) :
    ∃ F, s.fork? = some F := by
  unfold standOf at h
  cases hh : s.here with
  | between => rw [hh] at h; cases h
  | lay a => exact ⟨a.F, by simp [S.fork?, hh]⟩
  | att a => exact ⟨a.F, by simp [S.fork?, hh]⟩
  | head a =>
    rw [hh] at h
    dsimp only at h
    split at h
    · rename_i hi
      exact Option.isSome_iff_exists.1 hi
    · cases h
  | fin a => rw [hh] at h; cases h
  | mem a => rw [hh] at h; cases h

/-- The test: the list has a place at number k, at which a segment is to stand open. -/
def inLinkAtB (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  match ps[k]? with
  | some p =>
    match standAt links p with
    | .link _ => true
    | _ => false
  | none => false

theorem inLinkAtB_full :
    ((List.range 25).all fun l =>
      inLinkAtB linksFull (flatPlacesOf linksFull true) (drawAt l)) = true := by
  decide +kernel

/-- **THE CLOSED FACT**, at the full size, at kind K8's draw of every segment. -/
theorem stand_full (l : ℕ) (hl : l ≤ 24) :
    ∃ p sub, (flatPlacesOf linksFull true)[drawAt l]? = some p ∧
      standAt linksFull p = .link sub := by
  have h := List.all_eq_true.1 inLinkAtB_full l (List.mem_range.2 (Nat.lt_succ_of_le hl))
  unfold inLinkAtB at h
  split at h
  · rename_i p hp
    split at h
    · rename_i sub hs
      exact ⟨p, sub, hp, hs⟩
    · cases h
  · cases h

/-- The promise at a state without a mark holds the test on where the chain stands. -/
theorem shapeAt_of_onQ {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (ps : List Place) (get : A → P × First.S) (k : ℕ) (a : A × Fr.E.Str)
    (h : onQ N Mg links ps get k a) (hm : (get a.1).2.failed = none) :
    shapeAt links ps[k]? (get a.1).2 = true := by
  rcases h.2 with h' | h'
  · exact absurd hm h'
  · have e := h'.1
    simp only [Bool.and_eq_true] at e
    exact e.1.1.1.1.1

/-- **OUT OF THE PROMISE, AT THE FULL SIZE, IN FRONT OF THE DRAW OF SEGMENT l.** -/
theorem fork_of_onQ {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (get : A → P × First.S) (l : ℕ) (hl : l ≤ 24) (a : A × Fr.E.Str)
    (h : onQ N Mg linksFull (flatPlacesOf linksFull true) get (drawAt l) a)
    (hm : (get a.1).2.failed = none) : ∃ F, (get a.1).2.fork? = some F := by
  obtain ⟨p, sub, hp, hs⟩ := stand_full l hl
  have e := shapeAt_of_onQ N Mg _ _ get _ a h hm
  rw [hp] at e
  unfold shapeAt at e
  simp only [Bool.and_eq_true, beq_iff_eq] at e
  exact fork_of_stand _ sub (e.1.1.trans hs)

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.fork_of_stand
#print axioms VerifiableInference.Desc.First.K8.inLinkAtB_full
#print axioms VerifiableInference.Desc.First.K8.stand_full
#print axioms VerifiableInference.Desc.First.K8.shapeAt_of_onQ
#print axioms VerifiableInference.Desc.First.K8.fork_of_onQ
