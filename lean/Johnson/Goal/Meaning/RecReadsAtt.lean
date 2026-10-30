-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/RecReadsAtt.lean: the quiet step behind the reads' sending at an attention link
(Johnson/Desc/First/Att/ReadsO.lean) hands RecAll on (Johnson/Goal/Meaning/RecAll.lean; RecRel,
Johnson/Goal/Meaning/RecRel.lean), and leaves the statement as it is.

By the step's text: it writes, of the link's own part, the tables, the record of the smallness test
and a slot's number: never the link's state of the calls, the walk's state or the statement.
  readsAtSO_eq: what a yes returns.
  readsAtSO_rec: Keeps.Fn (RecRel cs sh) (readsAtSO A).
  readsAtO_rec: Whole (RecRel cs sh) of whatever readsAtO returns.
Not claimed: anything on another step.
OBJECT: the makers' blocks and steps that are named above. USER: the walk
(Johnson/Goal/Meaning/RecWalk.lean: recAll_border), at the letters cs and sh: it asks
Decides (RecRel cs sh) of every block of a list; that list is not laid yet. Which maker stands
at which place of a seated text is not said here.
-/
import Johnson.Goal.Meaning.RecRel
import Johnson.Desc.First.Att.ReadsO

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Fn)
open VerifiableInference.Desc.First.Att (readsAtSO readsAtO)

variable {cs : Codes} {sh : ReqShape} {Cl : Type}

theorem readsAtSO_eq {A : Attention.Plan} {s s' : S} (h : readsAtSO A s = .ok s') :
    ∃ a t tl, s.here = .att a ∧
      s' = { s with here := .att { a with t := some t, tl := tl } } := by
  unfold readsAtSO at h
  dsimp only at h
  split at h
  · rename_i a ha
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨r, _, h⟩ := bindE h
    cases h
    exact ⟨a, r.1, r.2.1, ha, rfl⟩
  · cases h

theorem readsAtSO_rec (A : Attention.Plan) : Fn (RecRel cs sh) (readsAtSO A) := fun s s' h R => by
  obtain ⟨a, t, tl, ha, rfl⟩ := readsAtSO_eq h
  refine same_frames R rfl fun f hm => ?_
  unfold framesIn at hm ⊢
  rw [ha]
  exact hm

theorem readsAtO_rec {W : Verify.Public} {l g : Nat} {b : Block S Cl}
    (h : readsAtO W l g = some b) : Whole (RecRel cs sh) b := by
  unfold readsAtO at h
  obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨fun s _ _ s' e => readsAtSO_rec A s s' e, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩

theorem readsAtSO_st {A : Attention.Plan} {s s' : S} (h : readsAtSO A s = .ok s') :
    s'.st = s.st := by
  obtain ⟨a, t, tl, -, rfl⟩ := readsAtSO_eq h
  rfl

#print axioms readsAtSO_rec
#print axioms readsAtO_rec

end Meaning.K2
