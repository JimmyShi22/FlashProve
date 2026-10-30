-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/IndexLotKeyStatement.lean: THE KIND's SECOND LOT
`k11IndexLot` (MsgLotsStatement.lean of this folder) AND THE WHOLE-MESSAGE TEXT OF A SENDING OF THE
KIND K1 (`K1.msgTxt`, Honest/K1/ScriptLots.lean, a file that is not in
this library) ANSWER ALIKE WHEREVER BOTH ANSWER, UNDER ONE PUBLIC TEST ON THE BOOK: `IndexLotMeets`
(IndexLotOwnerStatement.lean of this folder) WITH ITS LETTER tx LAID AT THAT TEXT. STATEMENTS ALONE:
two definitions of propositions; no definition of another kind. NOTHING IS PROVED IN THIS FILE, and
neither is one of the library's goals: they are lemmas' statements.

  `SenderAtSlot`    general in the sending's job J, the message's number n and the entry's number ν
                    of its mask rows: n is one of the job's messages, its table does not ride, ν
                    lies below rows * length: wherever the text answers at (mask, row ν % rows,
                    place ν / rows), its answer is element number `maskStart` + ν, of the extension
                    field, of what k (the letter of the type `Coins`) holds at the sending's own
                    address
  `IndexLotAgrees`  these three premises, and the test on the book (`entryRunIs`,
                    Honest/Small/EntryRunIs.lean): the book's second spending entry for the row's
                    part number 1 has that address as its owner and the start `maskStart` + ν. Then:
                    wherever the lot at that row and place and the text both answer, they answer
                    alike

WHAT IT IS NOT. AT LETTERS STILL: J IS ANY JOB. That the job of the index masks' sender at the
library's head has given numbers n and ν, a given `maskStart` and a given place, and that (ν % rows,
ν / rows) is the entry at which the lot is meant to be laid, is not said. The lot's number n' is a
free letter: it is not held against the sender's. That any book passes the test is not said. Other
kinds spend of the same message: that the merge's one entry is no other part's is the book's own
test. ONE LETTER ch STANDS FOR THE SPENDER's CHAIN AND THE SENDER's. The count in the test is idle
here. No lot is laid.

NEAR. `K1.msgTxt_mask_slot` (Honest/K1/ScriptMaskSlot.lean, the same authors', not in this library):
the text at such an entry is a value of the part's own cut: called; by its own head that value is 0
beyond the part's count, and whoever spends the equation calls `K1.mask_in`
(Honest/K1/MaskLaw.lean): it is called here, and the first statement's end is a return, not a
default. The public test `K1.sendFits` (Honest/K1/Coins.lean), which that head names beside it, is
not taken: `K1.mask_in` needs it not. `senderAt24`, `maskLot_agrees`
(Honest/K2/Law/MaskLotAgrees.lean): the like for the kind's first lot, at a switch's text.

Limits. Unfoldings and calls. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.IndexLotOwnerStatement
import Johnson.Desc.ProofFile.Honest.K1.ScriptLots
import Johnson.Desc.ProofFile.Honest.K1.MaskLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model (WsClaim)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Place)
open Johnson.Desc.First.ForkMerge (HeadMergeP)
open Johnson.Prover.Send (shapeAt)
open ProofFile.Honest.K1 (SendJob msgTxt)

/-- The statement on the sender's text. Not proved here; a lemma's statement, none of the library's
goals. -/
def SenderAtSlot : Prop :=
  ∀ (Bk : ProverCoinCounts) (W Wl X : Type) (ch : Nat) (wit : Wl → W) (J : SendJob W X) (own₀ : X) (n ν : Nat),
    n < J.P.sent.size → J.ride n = none →
    ν < (shapeAt J.P n).maskRows * (J.P.codes.mask.getD (shapeAt J.P n).maskCode default).ell →
    ∀ (k : Coins Bk) (w : Wl) (hd : List Fmt.Drawn) (y' : GE),
      msgTxt ch wit J own₀ n k w hd true (ν % (shapeAt J.P n).maskRows)
        (ν / (shapeAt J.P n).maskRows) = some y' →
      (k.look ch ⟨J.P.place, 0⟩).2.eAt (K1.maskStart J.P J.ride n + ν) = .ok y'

/-- **The statement on the lot and the sender's text.** n': the lot's number. Not proved here; a
lemma's statement, none of the library's goals. -/
def IndexLotAgrees : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X : Type) (ch : Nat) (pl : Place) (P : HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) (n' : Nat)
    (W Y : Type) (wit : Local W₀ Rc Xi Tr → W) (J : SendJob W Y) (own₀ : Y) (n ν sf : Nat),
    n < J.P.sent.size → J.ride n = none →
    ν < (shapeAt J.P n).maskRows * (J.P.codes.mask.getD (shapeAt J.P n).maskCode default).ell →
    entryRunIs (spentE Bk ⟨pl, 1⟩) 1 ⟨J.P.place, 0⟩ ⟨sf, K1.maskStart J.P J.ride n + ν⟩ ⟨0, 1⟩ =
      true →
    ∀ k w hd hd' mask row place y y',
      (k11IndexLot Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights n'
        (ν % (shapeAt J.P n).maskRows) (ν / (shapeAt J.P n).maskRows)).txt k w hd mask row place =
          some y →
      msgTxt ch wit J own₀ n k w hd' mask row place = some y' → y' = y

end ProofFile.Honest.K11
