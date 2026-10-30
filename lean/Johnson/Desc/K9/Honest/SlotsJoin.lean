-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K9/Honest/SlotsJoin.lean (kind K9): THE BOOL `slotsLive` (Johnson/Desc/K9/Honest/SlotsLive.lean),
CUT LIST BY LIST: what each of several lists of claims must bring, so that the Bool holds of the lists in a row.
(That a segment's gatherer yields the runs' lists in a row is `gather_ran`, in a file beside the seal:
Johnson/Desc/ProofFile/Honest/K9/GatherFold.lean.) Statements and proofs on the verifier's own data; no prover
is in this file, and no goal is stated.

  `liveAt_append`, `plainAt_append`, `unnamedAt_append`   over two lists in a row: a slot is live if it is live
                    in one of them; "plain" and "unnamed" must hold in both
  `liveAt_flatten`, `plainAt_flatten`, `unnamedAt_flatten`   the like over a list of lists
  `slotsLive_iff`   the Bool, slot by slot
  `slotsLive_of_runs`   **SO: the Bool holds of the runs' lists in a row if: each slot below n but the merge's
                    is live in SOME run's list · every run's list is plain at each such slot · no run's list
                    names the merge's slot**
WHAT IS NOT CLAIMED. That any run's list brings its share. Nothing on any property.

-/
import Johnson.Desc.K9.Honest.SlotsLive

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9H

theorem liveAt_append (l l' : List Claim) (j : Nat) :
    liveAt (l ++ l') j = (liveAt l j || liveAt l' j) := by
  unfold liveAt
  rw [List.any_append]

theorem plainAt_append (l l' : List Claim) (j : Nat) :
    plainAt (l ++ l') j = (plainAt l j && plainAt l' j) := by
  unfold plainAt
  rw [List.all_append]

theorem unnamedAt_append (l l' : List Claim) (j : Nat) :
    unnamedAt (l ++ l') j = (unnamedAt l j && unnamedAt l' j) := by
  unfold unnamedAt
  rw [List.all_append]

theorem liveAt_flatten (j : Nat) : ∀ (ls : List (List Claim)),
    liveAt ls.flatten j = ls.any fun l => liveAt l j
  | [] => rfl
  | l :: ls => by rw [List.flatten_cons, liveAt_append, liveAt_flatten j ls, List.any_cons]

theorem plainAt_flatten (j : Nat) : ∀ (ls : List (List Claim)),
    plainAt ls.flatten j = ls.all fun l => plainAt l j
  | [] => rfl
  | l :: ls => by rw [List.flatten_cons, plainAt_append, plainAt_flatten j ls, List.all_cons]

theorem unnamedAt_flatten (j : Nat) : ∀ (ls : List (List Claim)),
    unnamedAt ls.flatten j = ls.all fun l => unnamedAt l j
  | [] => rfl
  | l :: ls => by rw [List.flatten_cons, unnamedAt_append, unnamedAt_flatten j ls, List.all_cons]

/-- The Bool, slot by slot. -/
theorem slotsLive_iff (n : Nat) (merge : Option Nat) (cls : List Claim) :
    slotsLive n merge cls = true ↔
      ∀ j < n, (merge = some j → unnamedAt cls j = true) ∧
        (merge ≠ some j → liveAt cls j = true ∧ plainAt cls j = true) := by
  unfold slotsLive
  rw [List.all_eq_true]
  constructor
  · intro h j hj
    have h1 := h j (List.mem_range.2 hj)
    constructor
    · intro hm
      have he : (merge == some j) = true := by simpa using hm
      rw [he] at h1
      simpa using h1
    · intro hm
      have he : (merge == some j) = false := by simpa using hm
      rw [he] at h1
      simpa using h1
  · intro h j hj
    obtain ⟨h1, h2⟩ := h j (List.mem_range.1 hj)
    by_cases hm : merge = some j
    · have he : (merge == some j) = true := by simpa using hm
      rw [he]
      simpa using h1 hm
    · have he : (merge == some j) = false := by simpa using hm
      rw [he]
      simpa using h2 hm

/-- **The Bool out of the runs' shares.** -/
theorem slotsLive_of_runs (n : Nat) (merge : Option Nat) (ls : List (List Claim))
    (live : ∀ j < n, merge ≠ some j → ∃ l ∈ ls, liveAt l j = true)
    (plain : ∀ j < n, merge ≠ some j → ∀ l ∈ ls, plainAt l j = true)
    (unnamed : ∀ j < n, merge = some j → ∀ l ∈ ls, unnamedAt l j = true) :
    slotsLive n merge ls.flatten = true := by
  rw [slotsLive_iff]
  intro j hj
  refine ⟨fun hm => ?_, fun hm => ⟨?_, ?_⟩⟩
  · rw [unnamedAt_flatten, List.all_eq_true]
    exact unnamed j hj hm
  · rw [liveAt_flatten, List.any_eq_true]
    exact live j hj hm
  · rw [plainAt_flatten, List.all_eq_true]
    exact plain j hj hm

end VerifiableInference.Desc.K9H

#print axioms VerifiableInference.Desc.K9H.liveAt_flatten
#print axioms VerifiableInference.Desc.K9H.plainAt_flatten
#print axioms VerifiableInference.Desc.K9H.unnamedAt_flatten
#print axioms VerifiableInference.Desc.K9H.slotsLive_iff
#print axioms VerifiableInference.Desc.K9H.slotsLive_of_runs
