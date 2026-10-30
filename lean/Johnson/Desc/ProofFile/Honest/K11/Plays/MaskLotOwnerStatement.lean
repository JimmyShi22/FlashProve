-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/MaskLotOwnerStatement.lean: WHOSE ELEMENTS THE MERGE's FIRST
RUN IS MADE OF; AND THAT THE KIND's FIRST LOT `k11MaskLot` (MsgLotsStatement.lean of this folder)
AND A SENDER's TEXT ANSWER ALIKE WHEREVER BOTH ANSWER, UNDER ONE PUBLIC TEST ON THE BOOK. STATEMENTS
ALONE: two definitions of propositions; no definition of another kind. NOTHING IS PROVED IN THIS
FILE, and neither is one of the library's goals: they are lemmas' statements.

  `MaskRunIsOwners`   where `k11Lent` returns c and e is the book's first spending entry for the
                      row's part number 1: member i of the first run, i below 2 lk + 2, is element
                      number e.start.e + i, of the extension field, of what k (the letter of the
                      type `Coins`) holds at the address e.owner. GENERAL IN THE BOOK: no test on it
  `MaskLotMeets`      the sender's text is a letter tx. Its one premise: where it answers at (mask,
                      row 0, place ν), ν below a letter L, its answer is element number base + ν of
                      what k holds at the sender's address o. The test on the book (`entryRunIs`,
                      Honest/Small/EntryRunIs.lean): that first entry has the owner o and the start
                      base + ν₀. One public premise more: ν₀ + (2 lk + 2) ≤ L. Then: wherever the
                      lot and tx both answer, they answer alike

Why the premise on tx names no part of the end. It speaks of the sender's text and the sender's own
elements alone: not of the lot, of what the row is lent, or of the book. The test on the book ties
the two; without it nothing follows.

WHAT IT IS NOT. An implication at letters: no text of a sender is laid at tx here, and that any book
passes the test is not said. Beyond L nothing is asked of tx: a sender's text may answer there with
a constant. The count in the test is idle here: where `k11Lent` returns, `lend` (Honest/Frame.lean)
has held the entry's count against the part's own. ONE LETTER ch STANDS FOR THE SPENDER's CHAIN AND
THE SENDER's: whoever lays tx lays both at one chain. Other spenders' lots of the same message are
not treated: that no entry is spent twice is the book's own test. No lot is laid.

NEAR. `lend_head` (Honest/Law/LendHead.lean): what `lend` hands over for its first entry is a cut of
the owner's: called. The law of Honest/K2/Law/CarriedOfLend.lean: the like for a carried entry, at
any number.

Limits. Unfoldings over the frame's laws on lending. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.MsgLotsStatement
import Johnson.Desc.ProofFile.Honest.Small.EntryRunIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (zeroE)
open OnBytes.Model (Reading WsClaim)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Place)
open Johnson.Desc.First.ForkMerge (HeadMergeP)
open ProofFile.Honest.SumLaw (firstRun)

/-- The statement on whose elements the first run is made of. Not proved here; a lemma's statement,
none of the library's goals. -/
def MaskRunIsOwners : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X : Type) (ch : Nat) (pl : Place) (P : HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) (k : Coins Bk) c
    (e : Ahead),
    k11Lent Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights k = .ok c →
    (spentE Bk ⟨pl, 1⟩)[0]? = some e →
    ∀ i, i < 2 * P.lay.lk + 2 →
      (k.look ch e.owner).2.eAt (e.start.e + i) =
        .ok (Reading.gl.val ((firstRun c.2.1).getD i zeroE))

/-- **The statement on the lot and a sender's text.** Not proved here; a lemma's statement, none of
the library's goals. -/
def MaskLotMeets : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X : Type) (ch : Nat) (pl : Place) (P : HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) (n ν₀ : Nat)
    (o : Addr) (sf base L : Nat)
    (tx : Coins Bk → Local W₀ Rc Xi Tr → List Fmt.Drawn → Bool → Nat → Nat → Option GE),
    entryRunIs (spentE Bk ⟨pl, 1⟩) 0 o ⟨sf, base + ν₀⟩ ⟨0, 2 * P.lay.lk + 2⟩ = true →
    ν₀ + (2 * P.lay.lk + 2) ≤ L →
    (∀ k w hd ν y', ν < L → tx k w hd true 0 ν = some y' →
      (k.look ch o).2.eAt (base + ν) = .ok y') →
    ∀ k w hd hd' mask row place y y',
      (k11MaskLot Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights n ν₀).txt k w hd mask row
        place = some y →
      tx k w hd' mask row place = some y' → y' = y

end ProofFile.Honest.K11
