-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Driver/BatchAt.lean: where the driver takes a segment's batching from: one field
of the record Blocks, asked once a segment, at the segment's place of the kind K9; the driver writes
that place into the block and turns nothing else.

Why. The guard on the reply (Johnson/Desc/SeatGuard.lean), which `firstChain` lays as scaffolding,
"can only refuse more" at the whole chain under one premise a segment, on the segment's batching
(Link.BatchMono, Johnson/Desc/Sound/SeatGuardChain.lean). This file says whose that
premise is: the batching's rounds and decision are those of the maker that the supplier returns at
that place. Definitions, statements and proofs.
Main names:
  `batchPlaceOf`, `batchPlacesOf`: the place at which the batching of the segment number l is asked
    for; these places for a list of parts, in order.
  `linkAt_batch`: where linkAt makes a segment L: the field batch returns a maker mk at batchPlaceOf
    l sub, and L.batch is "mk's block with that place written in".
  `linkAt_batch_reads`: so decision, rounds, oracles, what stands before, test on the plan, lists,
    later steps and name of L.batch c are those of mk c.
  `bare_batch`: every segment of the chain that firstChainWithoutReplyGuard makes has its batching so, at a member of
    batchPlacesOf.
Limits. Which maker a seat's record returns at these places is not said here: Blocks is a letter.
Link.BatchMono itself is not named here (its file does not lie beneath this one): that it carries
over from the maker is two rewritings by linkAt_batch, not typed. Nothing is said of the later
chains: the driver makes the first alone. No soundness is claimed, and nothing is said on hiding.
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.First.Driver.PlacesLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc

variable {S Cl : Type}

/-- The place at which the driver asks for a segment's batching. -/
def batchPlaceOf (l : Nat) (sub : ModelPart) : Place :=
  { chain := 1, link := some l, piece := (kindsBeforeBatching sub (l == 0)).length + 1, kind := .K9 }

/-- These places for a list of parts, in order. -/
def batchPlacesOf (links : List ModelPart) : List Place :=
  links.zipIdx.map fun x => batchPlaceOf x.2 x.1

/-- **A segment's batching is what the field `batch` returns at the segment's place of K9, with that
place written in, and nothing else.** -/
theorem linkAt_batch (H : Blocks S Cl) (l : Nat) (sub : ModelPart) (L : Link S Cl)
    (h : linkAt H l sub = some L) :
    ∃ mk, H.batch (batchPlaceOf l sub) = some mk ∧
      L.batch = fun c => { mk c with place := batchPlaceOf l sub } := by
  unfold linkAt at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨hear, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨batch, hb, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨close, _, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  exact ⟨batch, hb, rfl⟩

/-- So all that a run or a test on the plan reads of it, but the place, is the supplier's. -/
theorem linkAt_batch_reads (H : Blocks S Cl) (l : Nat) (sub : ModelPart) (L : Link S Cl)
    (h : linkAt H l sub = some L) :
    ∃ mk, H.batch (batchPlaceOf l sub) = some mk ∧ ∀ c, (L.batch c).decide = (mk c).decide ∧
      (L.batch c).rounds = (mk c).rounds ∧ (L.batch c).oracles = (mk c).oracles ∧
      (L.batch c).before = (mk c).before ∧ (L.batch c).planOk = (mk c).planOk ∧
      (L.batch c).claims = (mk c).claims ∧ (L.batch c).after = (mk c).after ∧
      (L.batch c).name = (mk c).name ∧ (L.batch c).place = batchPlaceOf l sub := by
  obtain ⟨mk, h1, h2⟩ := linkAt_batch H l sub L h
  refine ⟨mk, h1, fun c => ?_⟩
  rw [h2]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every segment of the chain without the scaffolding has its batching from that one field, at a
place of `batchPlacesOf`. That it is the place of the segment's own number is not said here. -/
theorem bare_batch (H : Blocks S Cl) (links : List ModelPart) (several : Bool) (c : Chain S Cl)
    (h : firstChainWithoutReplyGuard H links several = some c) :
    ∀ L ∈ c.links, ∃ a ∈ batchPlacesOf links, ∃ mk, H.batch a = some mk ∧
      L.batch = fun f => { mk f with place := a } := by
  intro L hL
  unfold firstChainWithoutReplyGuard at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  split at h
  · cases h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨ls, hl, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨back, _, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  obtain ⟨x, hx, e⟩ := mem_of_mapM (fun x : ModelPart × Nat => linkAt H x.2 x.1) _ _ hl L hL
  obtain ⟨mk, h1, h2⟩ := linkAt_batch H x.2 x.1 L e
  exact ⟨batchPlaceOf x.2 x.1, List.mem_map.2 ⟨x, hx, rfl⟩, mk, h1, h2⟩

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.linkAt_batch
#print axioms VerifiableInference.Desc.First.linkAt_batch_reads
#print axioms VerifiableInference.Desc.First.bare_batch
