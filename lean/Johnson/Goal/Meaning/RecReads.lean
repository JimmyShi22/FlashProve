-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/RecReads.lean: the quiet steps behind the reads' sending, at a layers' link and
at the head's link (Johnson/Desc/K8/ReadsQuiet.lean), hand RecAll on
(Johnson/Goal/Meaning/RecAll.lean; RecRel, Johnson/Goal/Meaning/RecRel.lean), and leave the
statement as it is.

By the library's own inversions (Johnson/Desc/K8/ReadsQuietLaws.lean: layers_ok, head_ok): each step
writes, of the link's own part, the record of the smallness test, a slot's number and (at the head)
the tables: never the link's state of the calls, the frame fr, the walk's state or the statement.
  layers_rec, head_rec: Whole (RecRel cs sh).
  blockAt_rec: so of whatever ReadsQuiet.blockAt returns (Johnson/Desc/K8/ReadsQuietAt.lean).
  layers_st, head_st: the statement is the same: so every reflexive relation on statements is kept.
Not claimed: anything on the attention link's like step (Johnson/Desc/First/Att/ReadsO.lean).
OBJECT: the makers' blocks and steps that are named above. USER: the walk
(Johnson/Goal/Meaning/RecWalk.lean: recAll_border), at the letters cs and sh: it asks
Decides (RecRel cs sh) of every block of a list; that list is not laid yet. Which maker stands
at which place of a seated text is not said here.
-/
import Johnson.Goal.Meaning.RecRel
import Johnson.Desc.K8.ReadsQuietLaws
import Johnson.Desc.K8.ReadsQuietAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole)
open VerifiableInference.Desc.K8.ReadsQuiet

variable {cs : Codes} {sh : ReqShape}

theorem layers_rec (P : PG) : Whole (RecRel cs sh) (layers P) := by
  refine ⟨fun s rs gs s' h R => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  obtain ⟨a, own, tl', ha, -, -, rfl⟩ := layers_ok h
  refine same_frames R rfl fun f hm => ?_
  unfold framesIn at hm ⊢
  rw [ha]
  exact hm

theorem head_rec (P : PH) : Whole (RecRel cs sh) (head P) := by
  refine ⟨fun s rs gs s' h R => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  obtain ⟨a, cov, x, t, tl', ha, -, -, -, -, -, rfl⟩ := head_ok h
  refine same_frames R rfl fun f hm => ?_
  unfold framesIn at hm ⊢
  rw [ha]
  exact hm

theorem blockAt_rec {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL}
    {H : Head.HPlanH2} {kinds : List (Nat × Nat)} {l : Nat} {b : Block S Unit}
    (h : blockAt G hS HLy H kinds l = some b) : Whole (RecRel cs sh) b := by
  unfold blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact layers_rec _
  · split at h
    · cases h
      exact head_rec _
    · cases h

theorem layers_st {P : PG} {s s' : S} {rs gs} (h : (layers P).decide s rs gs = .ok s') :
    s'.st = s.st := (layers_frame h).2.2.1

theorem head_st {P : PH} {s s' : S} {rs gs} (h : (head P).decide s rs gs = .ok s') :
    s'.st = s.st := (head_frame h).2.2.1

#print axioms layers_rec
#print axioms head_rec
#print axioms blockAt_rec

end Meaning.K2
