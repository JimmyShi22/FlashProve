-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/OwnerRest.lean: the kind "the code switch" (K2): one public test at a written place of
the kind, at a list of the owner's entries: each spender stands where the written
positions name it, and the test ownerOk (Honest/K2/Law/BookByRuns.lean) says yes at the owner's
entries. It is evaluated in the files OwnerRest/R*.lean, one place a file.

  ownerEntriesIn, ownerEntries   the owner's entries as tuples, in a list's order; in the book's
  restTest                       the test at a list of tuples

Limits. Definitions: the test is shown of no place here. Public: starts and counts are numbers.
-/
import AtFullSide.K2.OwnerTest
import AtFullSide.K14.RawAheadWritten
import AtFullSide.K14.RawLengthsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open ProofFile.Honest ProofFile.Honest.K2
open ProofFile.Honest.K2.Law (placesW ownerOk entryTuple)
open ProofFile.Honest.K14
open AtFullSide.K14
open P2Law.ProofPlan (WP)

/-- The owner's entries in a list, as tuples, in the list's order. -/
def ownerEntriesIn (l : List Ahead) (p : SwitchPlace) : List (Addr × Due × Due × Bool) :=
  (l.filter fun e => e.owner == (⟨p.place, 0⟩ : Addr)).map entryTuple

/-- The owner's entries in the book, as tuples. -/
abbrev ownerEntries : SwitchPlace → List (Addr × Due × Due × Bool) := ownerEntriesIn rawAheadW

/-- The book's small pieces, in the book's order. -/
def smallPieces : List (List Ahead) :=
  [foldsFirstW, foldsSharedW, [splitEntryWritten], rawCarriesFoldedW, rawCarriesOmegaW,
    rawCarriesWW, rawOwnCarryW]

/-- The whole from the stretches, the chain of segments and the seven small pieces. -/
def joinPieces (a s : List (Addr × Due × Due × Bool)) :
    List (List (Addr × Due × Due × Bool)) → List (Addr × Due × Due × Bool)
  | [b₁, b₂, b₃, b₄, b₅, b₆, b₇] => a ++ b₁ ++ b₂ ++ b₃ ++ s ++ b₄ ++ b₅ ++ b₆ ++ b₇
  | _ => []

theorem ownerEntriesIn_append (l l' : List Ahead) (p : SwitchPlace) :
    ownerEntriesIn (l ++ l') p = ownerEntriesIn l p ++ ownerEntriesIn l' p := by
  unfold ownerEntriesIn
  rw [List.filter_append, List.map_append]

/-- **The owner's entries in the book, piece by piece.** -/
theorem ownerEntries_join {p : SwitchPlace} {a s : List (Addr × Due × Due × Bool)}
    {o : List (List (Addr × Due × Due × Bool))}
    (ha : ownerEntriesIn (rawWantsW.map (·.entry)) p = a) (hs : ownerEntriesIn rawSegW p = s)
    (ho : smallPieces.map (fun l => ownerEntriesIn l p) = o) :
    ownerEntries p = joinPieces a s o := by
  subst ha hs ho
  show ownerEntriesIn rawAheadW p = _
  unfold rawAheadW
  simp only [ownerEntriesIn_append]
  have e : ownerEntriesIn [] p = [] := rfl
  rw [e, List.append_nil]
  rfl

/-- **The test** at a list of tuples. -/
def restTest (p : SwitchPlace) (L : List (Addr × Due × Due × Bool)) : Bool :=
  (L.all fun t => placedAt posW (orderOf WP) t.1.place) &&
    ownerOk p.sizes.codes (switchSent p.sizes p.others)
      (switchFresh p.sizes p.others p.foldVars) (beforeG posW) L

end AtFullSide.K2

#print axioms AtFullSide.K2.ownerEntriesIn
#print axioms AtFullSide.K2.restTest
