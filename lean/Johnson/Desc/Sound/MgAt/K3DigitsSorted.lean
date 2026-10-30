-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/MgAt/K3DigitsSorted.lean: the lookup on the digits of a segment's approximate
range proof: WHICH PUBLIC ITEMS OF OTHER KINDS ARE OPEN OR TIED BEHIND THE DIGITS' SUB-PROTOCOL, AT
THE COMPOSED MEANING's CLOSED LIST OF EXTRA PUBLIC TESTS mgMore (Johnson/Desc/Sound/MgAllAt.lean)
AND THE FULL SIZE's WRITTEN LISTS: two written lists a sort of segment, held against the table by
the kernel at all twenty-five segments. After the like file at the calls (MgAt/K3CallsTable.lean).
NO SOUNDNESS IS CLAIMED.

Main names.
  keptDigits l sub: what stands on both sides. newDigits l sub: what is new behind: formsIn l (7 +
    shift sub) "objects" alone.
  digSort_mgMore: at all 25: every item behind is one of K3's own (k3Like), or kept, or new; and
    every kept item stands in front. digSort_empty: A NEGATIVE TEST: at empty lists the test says
    false.
  digits_sorted: what the test gives at a segment.
WHENCE THE LISTS. An evaluation at the segments 0, 1 and 24 (by a small program that is not in this
library); at the other 22 they are FORETOLD from the counts: the kernel's test is what holds them.
OBJECT. Functions with code of the table of joints at closed lists.
USER. othersPub_dig_mgAll (MgAt/K3DigitsOthers.lean).
LETTERS. l, sub.
IS IT EMPTY? No premise.


Compiled with the whole library.

Limits. The full size's lists and the closed list of the build apart from the library's, and these
alone: over another version of the composed meaning the lists may part.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MoreAll
import Johnson.Desc.First.Look.K3DigitsBehind
import Johnson.Desc.First.Look.K3Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Pub More shift pubSets pubStep pubRowM pubOfItems stepOpen
  openSets start)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- What is open or tied on both sides of the digits' place, and none of K3's own. -/
def keptDigits (l : ℕ) : ModelPart → List Pub
  | .layers => [.unheard, .ledger l, .freeAbove l, .indexIs, .indexThere, .hasRow l,
      .formsIn l 2 "objects", .formsIn l 2 "planes", .formsIn l 2 "join", .formsIn l 3 "own",
      .formsIn l 5 "small"]
  | .attention => [.unheard, .ledger l, .freeAbove l, .more (some l) "K5.okAt",
      .more (some l) "K5.plain", .indexIs, .indexThere, .formsIn l 2 "objects",
      .formsIn l 2 "planes", .formsIn l 2 "join", .formsIn l 3 "own", .formsIn l 5 "small"]
  | .head => [.ledger l, .freeAbove l, .indexIs, .indexThere, .formsIn l 3 "objects",
      .formsIn l 3 "planes", .formsIn l 4 "join", .formsIn l 4 "own", .formsIn l 4 "weights",
      .formsIn l 6 "small"]

/-- What is new behind it, and none of K3's own. -/
def newDigits (l : ℕ) (sub : ModelPart) : List Pub := [.formsIn l (7 + shift sub) "objects"]

/-- What is open or tied in front of the digits' place of segment l. -/
def frontDig (M : More) (l : ℕ) : List Pub :=
  (pubSets M linksFull PS)[k3K l true]?.getD [] ++
    pubOfItems ((openSets linksFull PS (start linksFull))[k3K l true]?.getD [])

/-- What is open or tied behind it. -/
def behindDig (M : More) (l : ℕ) : List Pub :=
  pubStep ((pubSets M linksFull PS)[k3K l true]?.getD [])
      (pubRowM M linksFull (IM.k3Place l true)) ++
    pubOfItems (stepOpen ((openSets linksFull PS (start linksFull))[k3K l true]?.getD [])
      (Desc.First.rowOf linksFull (IM.k3Place l true)))

/-- The test at one segment, at two lists as letters. -/
def digRowB (M : More) (kept new : ℕ → ModelPart → List Pub) (l : ℕ) : Bool :=
  (linksFull[l]?).any fun sub =>
    ((behindDig M l).all fun q =>
      k3Like q || (kept l sub).contains q || (new l sub).contains q) &&
    (kept l sub).all (frontDig M l).contains

/-- The test at all 25. -/
def digSortB (M : More) (kept new : ℕ → ModelPart → List Pub) : Bool :=
  (List.range 25).all (digRowB M kept new)

set_option maxRecDepth 1000000 in
theorem digSort_mgMore : digSortB mgMore keptDigits newDigits = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test.** -/
theorem digSort_empty : digSortB mgMore (fun _ _ => []) (fun _ _ => []) = false := by
  decide +kernel

/-- **What the test gives at a segment.** -/
theorem digits_sorted {l : ℕ} (hl : l < 25) {sub : ModelPart} (hs : linksFull[l]? = some sub) :
    (∀ q ∈ behindDig mgMore l, k3Like q = true ∨ q ∈ keptDigits l sub ∨ q ∈ newDigits l sub) ∧
      ∀ q ∈ keptDigits l sub, q ∈ frontDig mgMore l := by
  have h := List.all_eq_true.1 digSort_mgMore l (List.mem_range.2 hl)
  unfold digRowB at h
  rw [hs, Option.any_some, Bool.and_eq_true] at h
  refine ⟨fun q hq => ?_, fun q hq => ?_⟩
  · have h1 := List.all_eq_true.1 h.1 q hq
    rw [Bool.or_eq_true, Bool.or_eq_true] at h1
    rcases h1 with (h1 | h1) | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl (List.contains_iff_mem.1 h1))
    · exact Or.inr (Or.inr (List.contains_iff_mem.1 h1))
  · exact List.contains_iff_mem.1 (List.all_eq_true.1 h.2 q hq)

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.digSort_mgMore
#print axioms VerifiableInference.OnPublicFiles.digSort_empty
#print axioms VerifiableInference.OnPublicFiles.digits_sorted
