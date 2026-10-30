-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Exchange/AtSeatStatement.lean: WHAT A LINK STATES UNDER "the merge", WHERE ITS
HEARING BLOCK NUMBER 8 IS THE KIND's BLOCK AS IT STANDS ALONE AT A SEAT (`IM.seatedAs`,
Johnson/IMR/SeatForm.lean): STATEMENTS ALONE: three, each a definition of a proposition. NOTHING IS
PROVED IN THIS FILE, and none of the three is one of the library's goals: they are lemmas'
statements. The texts are the description's and the table's; no prover is named.

  `LotBlockIs`          the block that the kind's lot lays (`K11.blkAt`,
                        Johnson/Desc/ProofFile/Lot/K11.lean) IS the kind's block at the lot's
                        numbers, where `verify-on-bytes`'s step under the name that the lot looks
                        up is found: the two differ in the test on the plan alone, by that one
                        clause
  `MergeStatedAtSeat`   such a link states, under that name, the merge's own run of claims
                        (`headMergeClaim`, Johnson/Desc/First/Fork/MergeKind.lean), to the letter
  `MergedAtMgSeated`    so `MergedAtMg` (Johnson/Desc/K11/Exchange/AtMgStatement.lean) holds with
                        its two premises on what the link states replaced by that one on the
                        block's form

Limits. That the step under the name that the lot looks up is found is a premise. That a link of the
description has such a block at number 8 is a premise. Nothing on a seat at which a block is joined
behind. Nothing on any property.
-/
import Johnson.Desc.K11.Exchange.AtMgStatement
import Johnson.Desc.K11.Returns.SeatStatement
import Johnson.Desc.ProofFile.Lot.K11

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Exchange
open VerifiableInference.Desc (Link Claim Strs Wit Place)
open VerifiableInference.Desc.First (S ModelPart Meaning)
open VerifiableInference.Desc.First.MergeLaw (mergeStates)
open VerifiableInference.Desc.K9 (Readers statesOfLink)
open VerifiableInference.Desc.Sound (formsQ MgData mgAll seatTab CellsQ MsgT)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind headMergeClaim)

/-- The statement that the lot's block is the kind's. Z, G: what is read off the public files. look:
the name of `verify-on-bytes`'s step in front of which the oracle messages are counted. Not proved
here; a lemma's statement, none of the library's goals. -/
def LotBlockIs : Prop :=
  ∀ (Z : ProofFile.Pub) (look : String) (G : ProofFile.Ground), (K11.sentAt? Z look).isSome = true →
    K11.blkAt Z look G = headClaimMergeKind (K11.parAt Z look G)

/-- The statement on what the link states. l: the link. P: the kind's public data. name, a: the
seat's name and place. Not proved here; a lemma's statement, none of the library's goals. -/
def MergeStatedAtSeat : Prop :=
  ∀ (l : Link S Claim) (P : HeadMergeP) (name : String) (a : Place),
    l.hear[8]? = some (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name a) →
    ((statesOfLink l 8).find? fun x => x.1 == "the merge") = some ("the merge", headMergeClaim)

/-- The statement at the composed meaning's field forms. The letters: as in `MergedAtMg`. Not proved
here; a lemma's statement, none of the library's goals. -/
def MergedAtMgSeated : Prop :=
  ∀ (Xi P Tok : Type) (rows cols nR : ℕ) (X : OnBytes.Model.Verify.Public)
    (D : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
    (m : ℕ) (l : Link S Claim) (Pm : HeadMergeP) (name : String) (a : Place)
    (z : P) (b : S) (y : Strs) (w : Wit (CellsQ rows cols) Tok MsgT),
    D.links[m]? = some .head → D.lk m = some l →
    l.hear[8]? = some (IM.seatedAs ProofFile.sameReply (headClaimMergeKind Pm) name a) →
    formsQ (Readers.ofStates (mergeStates "the merge")) (D.N.group m) 8 "the merge" b
      (seatTab D.cs D.arr D.ms w) →
    (mgAll D Mg).forms m 9 "merged" (z, b) y w

end Johnson.Desc.First.ForkMerge.Exchange
