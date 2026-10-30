-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerTiesJoinOwed.lean: ONE STATEMENT THAT IS OWED FOR K14's LAW, AS A
PROPOSITION BY def: NO PROOF HERE. The law of the shared chain's twelve pieces at the cap
(ledger_at_cap) asks five ties of its pieces' written rounds to the written list: hdW, t2, t4, t5,
t7, in the words atW and Ties (Johnson/Goal/Numbers/K14RoundsAt.lean,
K14OwnAt.lean). Already proved: the
five equations in scope in the word writtenAt (tiesAtScope, Johnson/Desc/K14/Law/LedgerTies.lean),
and that a row's data begin with the seven rounds (takeOfRow). OWED: the join: the five binders, to
the letter, at the written list of the full proof file.

  TiesJoinOwed   in scope, where the value is laid, at a row of pieces whose data are the second
                 chain's: ledger_at_cap's hdW, t2, t4, t5, t7 at Wr := dryProofFull.2.1
What is not claimed. That it holds.
(It is proved in Johnson/Desc/K14/Law/LedgerTiesJoin.lean: tiesJoin.)
Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerTies
import Johnson.HB.LLHARD.K14Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Maker
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)

/-- OWED: the five ties that the law at the cap asks, at the written list of the full proof file. -/
def TiesJoinOwed : Prop :=
  ∀ (o : ProofFile.SecondHashFunctionArgument) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF),
    VerifierAndGoals.InScope Z = true → LPFD.Full.proofDataAndDecisionOfPublicFiles o Z.pol Z.lay Z.KL = .ok (D, r) →
    ∀ (C : CK) (Fr : Frame) (S Cl W : Type) (f pt x2 x3 x4 x5 x6 x7 : Piece C Fr S Cl W)
      (rest : List (Piece C Fr S Cl W)) (d d21 d22 d4 d51 d52 d7 : RDT),
      rowData f (pt :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest) = D.ds₂ → f.ds = [] →
      pt.ds = [d] → x2.ds = [d21, d22] → x3.ds = [] → x4.ds = [d4] → x5.ds = [d51, d52] →
      x6.ds = [] → x7.ds = [d7] →
      atW Johnson.G.dryProofFull.2.1 0 = some (d.entry, d.kind) ∧
        Ties Johnson.G.dryProofFull.2.1 2 [d21, d22] ∧ Ties Johnson.G.dryProofFull.2.1 4 [d4] ∧
        Ties Johnson.G.dryProofFull.2.1 5 [d51, d52] ∧ Ties Johnson.G.dryProofFull.2.1 7 [d7]

end Desc.K14.Law
