-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE KEY FILE's TWO LOOKUPS: THE OFFLINE PROVER.
The three further tests that `chainSteps` (Honest/Frame.lean) asks of the book at a place, the number of
  rounds, and the lending at the first chain's coins, AT THE LOOKUP's ROW WITH A LETTER FOR THE OWNERS
  (`proverSideOfLookupInChain`, Honest/K3/RowOwned.lean): the sisters of `place_tests`, `rowLendsFirst` (Honest/K3/Law/RowLends.lean)
  and `lookSeat_rounds` (Honest/K3/Law/MemberSite.lean), which stand at the row of one owner.

Johnson/Desc/ProofFile/Honest/K3/Key/OwnedSeatMeetsThePlaceTests.lean. General in the letter for the owners, the book, the
summands, the reader and the lookup's public data: no key file is named here. Four theorems with their proofs.

  `ownedSeatHasTheStagesMoves`        the owned seat's parts have the stages' numbers of rounds as numbers of moves
  `ownedSeatMeetsThePlaceTests`       `placeFits` ⊢ the three tests do not reject the owned seat
  `ownedSeatHasTheVerifiersRounds`    at a face with two planes or more: as many rounds as `entriesV` has entries
  `bookLendsTheOwnedSeatInTheFirstChain`   `bookFitsOwned` at the first chain's table and the book's own counts ⊢ at
                                       every run's coins `lendRow` returns, and what is lent is the entries' own coins

How it goes. `lookRowOwned_moves` (RowOwned.lean) carries the numbers of moves to
`lookRow`; `proverSideOfLookupInChainAtOneOwner_moves`, `rounds_stages` do the rest. The lending is `rowLendsOwned` (Parts/OwnedLends.lean) with
`look_due_first` (Law/RowLends.lean), as `rowLendsFirst` is `rowLends` with it.

Limits. Implications on a book that is a letter. Nothing on whether a part plays or a verifier accepts.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Parts.OwnedLends
import Johnson.Desc.ProofFile.Honest.K3.Law.MemberSite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Key
open ProofFile.Honest.K3.Law ProofFile.Honest.K3.Parts
open VerifiableInference.Desc.K3 (entriesV)

variable {V₁ W₁ X₁ W : Type}

/-- The owned seat's parts have, in order, the stages' numbers of rounds as their numbers of moves, at every letter. -/
theorem ownedSeatHasTheStagesMoves (owners : Owners) (reads : Reads) (jobs : LookJobs W) (wit : W₁ → W)
    (lookup : At) :
    (proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) owners reads jobs wit lookup).parts.map (·.moves.length) =
      (stages lookup.face).map (Stage.rounds lookup.face) := by
  have e : (proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) owners reads jobs wit lookup).parts.map (·.moves.length) =
      (lookRowOwned (V := Unit) owners reads jobs lookup).map (·.moves.length) := by
    simp [proverSideOfLookupInChain, Part.lift, Function.comp_def]
  rw [e, lookRowOwned_moves, lookRow_moves]

/-- **Conditional on `placeFits`: the three further tests of `chainSteps` do not reject the owned seat.** -/
theorem ownedSeatMeetsThePlaceTests (owners : Owners) (reads : Reads) (jobs : LookJobs W) (wit : W₁ → W)
    (lookup : At) (book : ProverCoinCounts) (rows : List (Addr × Due)) (fits : placeFits book rows lookup = true) :
    book.cuts.lookup lookup.place =
        some ((proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) owners reads jobs wit lookup).parts.map (·.moves.length)) ∧
    (rows.any fun r => r.1.place == lookup.place &&
      decide ((proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) owners reads jobs wit lookup).parts.length ≤ r.1.part)) = false ∧
    (book.ahead.any fun e => e.spender.place == lookup.place &&
      decide ((proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) owners reads jobs wit lookup).parts.length ≤ e.spender.part)) =
      false := by
  have hm := ownedSeatHasTheStagesMoves (V₁ := V₁) (X₁ := X₁) owners reads jobs wit lookup
  have hl : (proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) owners reads jobs wit lookup).parts.length =
      (stages lookup.face).length := by
    simpa using congrArg List.length hm
  simp only [placeFits, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at fits
  rw [hm, hl]
  exact ⟨fits.1.1, fits.1.2, fits.2⟩

/-- At a face with two planes or more the owned seat has as many rounds as the verifier's text has entries. -/
theorem ownedSeatHasTheVerifiersRounds (owners : Owners) (reads : Reads) (jobs : LookJobs W) (wit : W₁ → W)
    (lookup : At) (planes : 2 ≤ lookup.face.planes) :
    (proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) owners reads jobs wit lookup).rounds = (entriesV lookup.face).length := by
  unfold Placed.rounds
  rw [foldl_add_eq_sum (fun p : Part V₁ W₁ X₁ => p.moves.length), ownedSeatHasTheStagesMoves,
    rounds_stages lookup.face planes, Nat.zero_add]

/-- **The book lends the owned seat its coins in the first chain, at every run's coins**; what each part is lent to spend
is, stretch by stretch, its entries' own coins. Conditional on the test `bookFitsOwned` at the first chain's table and at
the book's own counts there. -/
theorem bookLendsTheOwnedSeatInTheFirstChain (owners : Owners) (reads : Reads) (jobs : LookJobs W) (wit : W₁ → W)
    (lookup : At) (book : ProverCoinCounts)
    (fits : bookFitsOwned owners book (book.rowsOf 0) (dueAt book.first) lookup = true) (coins : Coins book) :
    ∃ lent, lendRow book (book.rowsOf 0) (coins.look 0) lookup.place
        (proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) owners reads jobs wit lookup).parts 0 = .ok lent ∧
      rowSpent _ lent = (List.range (stages lookup.face).length).map fun i =>
        (entriesAt book lookup.place i).map (lentE (coins.look 0)) := by
  have e : (fun o => (coins.look 0 o).1) = dueAt book.first := funext (look_due_first book coins)
  exact rowLendsOwned owners reads jobs wit lookup book (book.rowsOf 0) (coins.look 0)
    (by rw [e]; exact fits)

end ProofFile.Honest.K3.Key

#print axioms ProofFile.Honest.K3.Key.ownedSeatHasTheStagesMoves
#print axioms ProofFile.Honest.K3.Key.ownedSeatMeetsThePlaceTests
#print axioms ProofFile.Honest.K3.Key.ownedSeatHasTheVerifiersRounds
#print axioms ProofFile.Honest.K3.Key.bookLendsTheOwnedSeatInTheFirstChain
