-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K3CallsTable.lean: THE LOOKUP ON A LINK's CALLS: A TEST ON THE TABLE OF
JOINTS ALONE, BY THE KERNEL: WHICH PUBLIC ITEMS ARE OPEN OR TIED BEHIND THE LOOKUP ON THE CALLS OF
EACH OF THE 25 SEGMENTS, at the full size's written list of segments (linksFull) and the composed
meaning's closed list of extra public tests (mgMore, Johnson/Desc/Sound/MgAllAt.lean): each is one
of the five that calls_behindR pays (paidCallsR), or one of a short list that is open or tied in
front too (keptCalls), or one of a short list that is new there (newCalls). It reads no state of the
verifier. NO SOUNDNESS IS CLAIMED.

OBJECT: the table of joints (pubSets, openSets, pubStep, stepOpen, pubOfItems): no sub-protocol's
  text.
USER: Johnson/Desc/Sound/MgAt/K3CallsOthers.lean.
LETTERS: l: a segment below 25; sub: its sort; a: the place at the border kOfCalls l.

Main names: `kOfCalls` · `keptCalls`, `newCalls` · `callsRowB`, `callsTableB` ·
  `callsTableB_mgMore` (by the kernel) · `callsTableB_empty` (A NEGATIVE TEST: with the two lists
  empty the test says false) · `calls_sorted`.

Limits. The full size's list and mgMore alone: another list of extra public tests wants its own
evaluation.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAllAt
import Johnson.Desc.Sound.AtDriver
import Johnson.Desc.First.Look.K3CallsBehindR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart More Pub flatPlacesOf pubSets openSets start pubStep
  pubRowM pubOfItems stepOpen)

/-- The number of the border in front of the lookup on the calls of segment l. -/
def kOfCalls (l : ℕ) : ℕ := 14 * l + (if l = 24 then 2 else 1) + 2

/-- What is open or tied on both sides, beside the five. -/
def keptCalls (l : ℕ) : ModelPart → List Pub
  | .layers => [.unheard, .more (some l) "frame.sentIs", .more (some l) "ledger.treesAre", .indexIs,
      .indexThere]
  | .attention => [.unheard, .more (some l) "frame.sentIs", .more (some l) "ledger.treesAre",
      .more (some l) "K5.readsThere", .more (some l) "K5.liveReq", .indexIs, .indexThere]
  | .head => [.tokenSmall, .more (some l) "frame.sentIs", .more (some l) "ledger.treesAre",
      .indexIs, .indexThere]

/-- What is new behind, beside the five. -/
def newCalls (l : ℕ) : ModelPart → List Pub
  | .layers => [.look l, .callerIn l, .more (some l) "K4.rowsBare", .more (some l) "K4.lookLeft",
      .formsInT l 2 "objects"]
  | .attention => [.look l, .callerIn l, .formsInT l 2 "objects"]
  | .head => [.look l, .formsInT l 3 "objects"]

/-- What is open or tied in front of block number k. -/
def frontAtK (M : More) (k : ℕ) : List Pub :=
  (pubSets M linksFull (flatPlacesOf linksFull true))[k]?.getD [] ++
    pubOfItems ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[k]?.getD [])

/-- What is open or tied behind it. -/
def behindAtK (M : More) (k : ℕ) (a : Desc.Place) : List Pub :=
  pubStep ((pubSets M linksFull (flatPlacesOf linksFull true))[k]?.getD [])
      (pubRowM M linksFull a) ++
    pubOfItems (stepOpen
      ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[k]?.getD [])
      (Desc.First.rowOf linksFull a))

/-- The test at one segment, at two lists as letters. -/
def callsRowB (M : More) (kept new : ℕ → ModelPart → List Pub) (l : ℕ) : Bool :=
  (linksFull[l]?).any fun sub => ((flatPlacesOf linksFull true)[kOfCalls l]?).any fun a =>
    ((behindAtK M (kOfCalls l) a).all fun q =>
      (paidCallsR l a.piece).contains q || (kept l sub).contains q || (new l sub).contains q) &&
    (kept l sub).all (frontAtK M (kOfCalls l)).contains

/-- The test at all 25. -/
def callsTableB (M : More) (kept new : ℕ → ModelPart → List Pub) : Bool :=
  (List.range 25).all (callsRowB M kept new)

set_option maxRecDepth 1000000 in
theorem callsTableB_mgMore : callsTableB mgMore keptCalls newCalls = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the test can fail. -/
theorem callsTableB_empty :
    callsTableB mgMore (fun _ _ => []) (fun _ _ => []) = false := by decide +kernel

/-- **What the test gives at a segment.** -/
theorem calls_sorted {l : ℕ} (hl : l < 25) {sub : ModelPart} (hs : linksFull[l]? = some sub)
    {a : Desc.Place} (here : (flatPlacesOf linksFull true)[kOfCalls l]? = some a) :
    (∀ q ∈ behindAtK mgMore (kOfCalls l) a,
      q ∈ paidCallsR l a.piece ∨ q ∈ keptCalls l sub ∨ q ∈ newCalls l sub) ∧
      ∀ q ∈ keptCalls l sub, q ∈ frontAtK mgMore (kOfCalls l) := by
  have h := List.all_eq_true.1 callsTableB_mgMore l (List.mem_range.2 hl)
  unfold callsRowB at h
  rw [hs, here, Option.any_some, Option.any_some, Bool.and_eq_true] at h
  refine ⟨fun q hq => ?_, fun q hq => ?_⟩
  · have h1 := List.all_eq_true.1 h.1 q hq
    rw [Bool.or_eq_true, Bool.or_eq_true] at h1
    rcases h1 with (h1 | h1) | h1
    · exact Or.inl (List.contains_iff_mem.1 h1)
    · exact Or.inr (Or.inl (List.contains_iff_mem.1 h1))
    · exact Or.inr (Or.inr (List.contains_iff_mem.1 h1))
  · exact List.contains_iff_mem.1 (List.all_eq_true.1 h.2 q hq)

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.callsTableB_mgMore
#print axioms VerifiableInference.OnPublicFiles.callsTableB_empty
#print axioms VerifiableInference.OnPublicFiles.calls_sorted
