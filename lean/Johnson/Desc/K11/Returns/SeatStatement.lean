-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Returns/SeatStatement.lean: TWO THINGS MORE ON WHAT THE MERGE OF THE CLAIMS ON THE
WEIGHTS WRITES (`headMergeDecide`, `headMergeClaim`, Johnson/Desc/First/Fork/MergeKind.lean):
STATEMENTS ALONE: three, each a definition of a proposition. NOTHING IS PROVED IN THIS FILE, and
none of the three is one of the library's goals: they are lemmas' statements. The text is the
verifier's; no prover is named.

  `HeadMergeRecs`          wherever the decision returns: the parts for the row on the weights that
                           it leaves are made of the claim that lay in front, at the batching
                           factor 1, IN THE FORM IN WHICH THE HEARING LAYS THEM: the scalar is
                           written out.
                           (`MergeBehind`, Statement.lean of this folder, says "at some scalar".)
  `HeadMergeLeavesReply`   wherever the decision or the run of claims returns, the state behind
                           holds the reply that the state in front held: the test of the guard under
                           which a sub-protocol stands at a seat of the proof file's description
                           (`ProofFile.sameReply`, Johnson/Desc/ProofFile/Frames1.lean)
  `HeadMergeSeated`        so the kind's block AS IT STANDS ALONE AT A SEAT of the first chain
                           (`IM.seatedAs`, Johnson/IMR/SeatForm.lean: the guard on the reply round
                           the block with the test on a mark of failure, under the seat's name, at
                           the seat's place) IS that block without the guard. That a block which
                           never writes the seat is its guarded form is the library's
                           (`Block.Still.guarded_eq`, Johnson/Desc/Sound/SeatGuardChain.lean)

Limits. Each "there is" in the first is the one value of a reader at a state that is named. The test
on a mark of failure stays round the block. Nothing on a seat at which a block is joined behind.
Nothing on any property.
-/
import Johnson.Desc.K11.Returns.Statement
import Johnson.IMR.SeatForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Returns
open OnBytes (E oneE mulE)
open OnBytes.Model (WsClaim WsForkOut wsRowPart wsEpsT)
open VerifiableInference.Desc (Place Claim Block)
open VerifiableInference.Desc.First (S HeadOwn)

/-- The statement on the parts for the row. Not proved here; a lemma's statement, none of the
library's goals. -/
def HeadMergeRecs : Prop :=
  ∀ (P : HeadMergeP) (s s' : S) (rs : List Fmt.RoundView), headMergeDecide P s rs = .ok s' →
    ∃ (a a' : HeadOwn) (claim : WsClaim) (wo : WsForkOut),
      s.here = .head a ∧ s'.here = .head a' ∧ a.claim = some claim ∧ a'.wo = some wo ∧
      wo.recs = [(claim, oneE)].map fun y =>
        wsRowPart P.lay y.1 (mulE y.2 (wsEpsT P.lay y.1 wo.rm))

/-- The statement that the reply stands. Not proved here; a lemma's statement, none of the library's
goals. -/
def HeadMergeLeavesReply : Prop :=
  (∀ (P : HeadMergeP) (s s' : S) (rs : List Fmt.RoundView), headMergeDecide P s rs = .ok s' →
      ProofFile.sameReply s s' = true) ∧
    ∀ (n : Nat) (s : S) (y : List Claim × S), headMergeClaim n s = .ok y →
      ProofFile.sameReply s y.2 = true

/-- The statement at the seat's own term. name, a: the seat's name and place. Not proved here; a
lemma's statement, none of the library's goals. -/
def HeadMergeSeated : Prop :=
  ∀ (P : HeadMergeP) (name : String) (a : Place),
    IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name a =
      { IM.marked (headClaimMergeKind P) name with place := a }

end Johnson.Desc.First.ForkMerge.Returns
