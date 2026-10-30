-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerTiesOwed.lean: THREE STATEMENTS THAT ARE OWED FOR K14's LAW, AS
PROPOSITIONS BY def: NO PROOF HERE. The law of the shared chain's twelve pieces prices the rounds of
five of them at the numbers of the WRITTEN list of rounds (Johnson.G.dryProofFull's second list).
The pieces bear the FILE's data (RDT). OWED: that the entry and the kind of these pieces' rounds are
those of the written list's rounds number 0 ("LIN point"), 1 (the seeds of "send o_u"), 3 ("LOC"),
4 (the seeds of "send o_omega") and 6 ("LIN zeta").

  writtenAt          the entry and the kind of a written list's round number i (a definition)
  DataOfWrittenOwed  the data made of three written lists have, round by round of the second chain,
                     the written round's entry and kind
  TakeOfRowOwed      a row of pieces whose first eight have 0 · 1 · 2 · 0 · 1 · 2 · 0 · 1 rounds:
                     the row's data begin with these seven rounds, in order
  TiesAtScopeOwed    so in scope, where the value is laid: the five equations
What is not claimed. That they hold.
(They are proved in Johnson/Desc/K14/Law/LedgerTies.lean: dataOfWritten, takeOfRow, tiesAtScope.)
That a row of pieces with these numbers of rounds is the
maker's. Nothing on soundness.

-/
import Johnson.Desc.Laid.ProofFullScope
import Johnson.Desc.Sound.ChainRule

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Maker
open OnBytes.Params (Rounds)
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)

/-- The entry and the kind of a written list's round number i. -/
def writtenAt (Wr : Rounds) (i : ℕ) : Option (Fmt.Entry × Fmt.Kind) :=
  (Wr[i]?).map fun r => (r.1.entry, r.1.kind)

/-- OWED: the data of the second chain bear the written rounds' entries and kinds. -/
def DataOfWrittenOwed : Prop :=
  ∀ (a : ℕ) (R : Rounds × Rounds × Rounds) (i : ℕ),
    ((WholeD.of a (wholeAt (some R))).ds₂[i]?).map (fun d : RDT => (d.entry, d.kind)) =
      writtenAt R.2.1 i

/-- OWED: the first seven rounds of a row's data, from the first eight pieces' own. -/
def TakeOfRowOwed : Prop :=
  ∀ (C : CK) (Fr : Frame) (S Cl W : Type) (f pt x2 x3 x4 x5 x6 x7 : Piece C Fr S Cl W)
    (rest : List (Piece C Fr S Cl W)) (d d21 d22 d4 d51 d52 d7 : RDT), f.ds = [] → pt.ds = [d] →
    x2.ds = [d21, d22] → x3.ds = [] → x4.ds = [d4] → x5.ds = [d51, d52] → x6.ds = [] →
    x7.ds = [d7] →
    (rowData f (pt :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest)).take 7 =
      [d, d21, d22, d4, d51, d52, d7]

/-- OWED: in scope, where the value is laid, the five rounds that the law prices have the written
rounds' entries and kinds. -/
def TiesAtScopeOwed : Prop :=
  ∀ (o : ProofFile.SecondHashFunctionArgument) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF),
    VerifierAndGoals.InScope Z = true → LPFD.Full.proofDataAndDecisionOfPublicFiles o Z.pol Z.lay Z.KL = .ok (D, r) →
    ∀ d d21 d22 d4 d51 d52 d7 : RDT, D.ds₂.take 7 = [d, d21, d22, d4, d51, d52, d7] →
      writtenAt Johnson.G.dryProofFull.2.1 0 = some (d.entry, d.kind) ∧
        writtenAt Johnson.G.dryProofFull.2.1 1 = some (d21.entry, d21.kind) ∧
        writtenAt Johnson.G.dryProofFull.2.1 3 = some (d4.entry, d4.kind) ∧
        writtenAt Johnson.G.dryProofFull.2.1 4 = some (d51.entry, d51.kind) ∧
        writtenAt Johnson.G.dryProofFull.2.1 6 = some (d7.entry, d7.kind)

end Desc.K14.Law
