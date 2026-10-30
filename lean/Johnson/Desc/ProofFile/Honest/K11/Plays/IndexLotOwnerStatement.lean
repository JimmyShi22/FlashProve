-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/IndexLotOwnerStatement.lean: WHOSE ELEMENT THE MERGE's END
RUN IS; AND THAT THE KIND's SECOND LOT `k11IndexLot` (MsgLotsStatement.lean of this folder) AND A
SENDER's TEXT ANSWER ALIKE WHEREVER BOTH ANSWER, UNDER ONE PUBLIC TEST ON THE BOOK. The like, at the
book's second spending entry and the end run, of MaskLotOwnerStatement.lean of this folder.
STATEMENTS ALONE: two definitions of propositions; no definition of another kind. NOTHING IS PROVED
IN THIS FILE, and neither is one of the library's goals: they are lemmas' statements.

  `EndRunIsOwners`    where `k11Lent` returns c and e is the book's SECOND spending entry for the
                      row's part number 1: the end run's one member is element number e.start.e, of
                      the extension field, of what k (the letter of the type `Coins`) holds at the
                      address e.owner. GENERAL IN THE BOOK: no test on it
  `IndexLotMeets`     the sender's text is a letter tx. Its one premise, at the one entry (mask, row
                      r, place p) at which the lot answers: where tx answers there, its answer is
                      element number el of what k holds at the sender's address o. The test on the
                      book (`entryRunIs`, Honest/Small/EntryRunIs.lean): that second entry has the
                      owner o and the start el. Then: wherever the lot and tx both answer, they
                      answer alike

WHAT IT IS NOT. An implication at letters: no text of a sender is laid at tx here, and that any book
passes the test is not said. IT IS ONE OF THREE THINGS THAT THE PREMISE OF `IndexTieOfOwn`
(IndexTieOfOwnStatement.lean of this folder) WANTS OF ITS PAYER; the other two, on the index masks'
sender's whole-message text, are not here. The count in the test is idle here: where `k11Lent`
returns, `lend` (Honest/Frame.lean) has held the entry's count against the part's own. ONE LETTER ch
STANDS FOR THE SPENDER's CHAIN AND THE SENDER's. Other kinds spend of the index masks' message too:
that the merge's one entry is no other part's is the book's own test. No lot is laid.

NEAR. `lend_head` (Honest/Law/LendHead.lean): called twice. `endRun_coin`
(Honest/SumLaw/Counts.lean): how a member of the end run reads, with a cast; here `endCoins_coin`
(Honest/SumLaw/More.lean) is called.

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
open ProofFile.Honest.SumLaw (endRun)

/-- The statement on whose element the end run is. Not proved here; a lemma's statement, none of the
library's goals. -/
def EndRunIsOwners : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X : Type) (ch : Nat) (pl : Place) (P : HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) (k : Coins Bk) c
    (e : Ahead),
    k11Lent Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights k = .ok c →
    (spentE Bk ⟨pl, 1⟩)[1]? = some e →
    (k.look ch e.owner).2.eAt e.start.e = .ok (Reading.gl.val ((endRun c.2.1).headD zeroE))

/-- **The statement on the lot and a sender's text.** Not proved here; a lemma's statement, none of
the library's goals. -/
def IndexLotMeets : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X : Type) (ch : Nat) (pl : Place) (P : HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) (n r p : Nat)
    (o : Addr) (sf el : Nat)
    (tx : Coins Bk → Local W₀ Rc Xi Tr → List Fmt.Drawn → Bool → Nat → Nat → Option GE),
    entryRunIs (spentE Bk ⟨pl, 1⟩) 1 o ⟨sf, el⟩ ⟨0, 1⟩ = true →
    (∀ k w hd y', tx k w hd true r p = some y' → (k.look ch o).2.eAt el = .ok y') →
    ∀ k w hd hd' mask row place y y',
      (k11IndexLot Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights n r p).txt k w hd mask row
        place = some y →
      tx k w hd' mask row place = some y' → y' = y

end ProofFile.Honest.K11
