-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/RowTakers/AllDefs.lean: ALL ENTRIES OF THE WRITTEN BOOK WHOSE OWNER IS THE CODE SWITCH
AT THE LINK 2 g, g = 1 … 11: THE WALK WITHOUT A TEST ON THE NUMBERS, AND ITS WRITTEN LIST. Six
definitions; two small statements. A sister of Defs.lean, whose ownerAt, rowSpentAt and carriersW it
takes. The closed facts: AllWants.lean and AllSeg.lean in this folder; what follows from them:
AtFullSide/K1/OwnerEntriesAtSwitches.lean, whose head tells the whole and its limits. A TRIAL THAT
COUNTS IN NO COLUMN.
NO PROPERTY IS CLAIMED.

  ownedIn l g the walk: the entries of l whose owner is ownerAt g, IN l's OWN ORDER, each as
(spender, start, count, once)
  carriedPairsW       WRITTEN OUT: six pairs (start, count): under these the entries marked as
                carried stand
  foldSpentAt g the one entry marked as spent that lies behind the row
  allCarriedAt g the entries marked as carried: bearer by bearer, in carriersW's order from its
number 4 * (g - 1) on; at each bearer the six pairs in carriedPairsW's order; the first bearer has
the first five alone
  ownedListW g **the written list**: rowSpentAt g, then foldSpentAt g, then allCarriedAt g

  meetsRowT x Defs.lean's test meetsRow, on a member of the written list

WHERE THE LIST COMES FROM: as Defs.lean's: printed off the written book's entries by Lean's
evaluator: A LISTING, NOT A SECOND SOURCE.
Terms: lean/GLOSSARY.md.
-/
import AtFullSide.K1.RowTakers.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K1
open ProofFile.Honest ProofFile.Honest.K14
open AtFullSide.K14
open VerifiableInference.Desc (Place KindName)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- **The walk without a test on the numbers**: in the list's own order. -/
def ownedIn (l : List Ahead) (g : Nat) : List (Addr × Due × Due × Bool) :=
  (l.filter fun e => e.owner == ownerAt g).map fun e => (e.spender, e.start, e.count, e.once)

/-- WRITTEN OUT: start and count of the entries that are marked as carried. -/
def carriedPairsW : List (Due × Due) :=
  [(⟨0, 0⟩, ⟨0, 439⟩), (⟨0, 439⟩, ⟨660, 0⟩), (⟨660, 439⟩, ⟨22776, 8411⟩),
    (⟨23436, 8850⟩, ⟨1974, 0⟩), (⟨25410, 8850⟩, ⟨660, 0⟩), (⟨26070, 8850⟩, ⟨0, 236⟩)]

/-- The one entry marked as spent behind the row. -/
def foldSpentAt (g : Nat) : Addr × Due × Due × Bool :=
  (⟨⟨1, some (2 * g), 11, .K10⟩, 0⟩, ⟨26070, 8850⟩, ⟨0, 17⟩, true)

/-- The entries marked as carried, at the group g: by the bearer, then by the pair. -/
def allCarriedAt (g : Nat) : List (Addr × Due × Due × Bool) :=
  (carriersW.drop (4 * (g - 1))).zipIdx.flatMap fun x =>
    (if x.2 == 0 then carriedPairsW.take 5 else carriedPairsW).map fun s => (x.1, s.1, s.2, false)

/-- **The written list of all entries of the owner, at the group g.** -/
def ownedListW (g : Nat) : List (Addr × Due × Due × Bool) :=
  rowSpentAt g ++ [foldSpentAt g] ++ allCarriedAt g

/-- Defs.lean's test meetsRow, on a member of the written list: it reads the same two numbers. -/
def meetsRowT (x : Addr × Due × Due × Bool) : Bool :=
  decide (0 < x.2.2.1.e) && decide (x.2.1.e < 8631) && decide (439 < x.2.1.e + x.2.2.1.e)

/-- The walk goes through an append. -/
theorem ownedIn_append (a b : List Ahead) (g : Nat) :
    ownedIn (a ++ b) g = ownedIn a g ++ ownedIn b g := by
  unfold ownedIn
  rw [List.filter_append, List.map_append]

theorem ownedIn_nil (g : Nat) : ownedIn [] g = [] := rfl

end AtFullSide.K1

#print axioms AtFullSide.K1.ownedIn_append
#print axioms AtFullSide.K1.ownedIn_nil
