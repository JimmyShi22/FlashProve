-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/MaskAtHeadStatement.lean: THE PREMISE `MaskAt`
(Johnson/Top/H0/MergeLaw/MaskRow.lean) OF THE MERGE's PUBLIC TEST ON FORMS, AT THE FIRST CHAIN's
THREAD AT THE LIBRARY's ONE HYPOTHESIS, IN FRONT OF THE MERGE's MEMBER (BORDER 346): STATEMENTS
ALONE: two, each a definition of a proposition. NOTHING IS PROVED IN THIS FILE, and neither is one
of the library's goals: they are lemmas' statements.

`MaskAt own xM R s`: in the state s an open segment's part is there; its request's frame names a
message as the one that holds the segment's mask rows; the book of trees gives that message the
member xM's place, among the segment's own; R bits number the rows of its mask table.

The library has the test with code at border 346 under the hypothesis, an opening and nine premises
(`K11.mask_paid`, Johnson/K11R/MaskPaid.lean), at every statement that is reached by the
description's own "reached" (`RchAt`, Johnson/Top/H0/Walk/ReachAt.lean). IT ALSO PAYS ALL NINE UNDER
THE HYPOTHESIS, at the written layout, at message number 181, mask number 0 and R := 0, at the
member that the list of messages has at the seat (73, 2): the six facts on numbers as
`K11.k11Pub_of_eight` lays them (Johnson/K11R/CondOfEight.lean); the three facts along "reached" as
fields of `P5J.foldFacts_at_head'` (Johnson/P5J/FoldJ3Whole.lean), which holds at every family
within that "reached". The thread with "every word that the rounds seen show is below the prime"
gives that "reached" (`thrS_rchAt`, Honest/Thread/ReachAtHead.lean). The law beneath
(`maskAtB_seated`, Johnson/K11R/MaskSeat.lean) is general in the table's meaning: at the meaning of
which the thread's own clause on the table's condition speaks (`Letters.thread`, field formP,
Honest/Thread/First.lean) that clause is the law's premise.

  `MaskMemberAtHead`   under the hypothesis: the list of messages has a member at the seat
                   (73, 2): so the first premise below only names xM
  `MaskAtAtHead`   under the hypothesis; xM: the member that the list of messages has at the seat
                   (73, 2); where the thread with that word on words stands at border 346 at the
                   state s: `MaskAt (h.𝔇.N.group 24) xM 0 s`. NO OTHER PREMISE: that s bears no
                   mark, and the table's condition at the border, are clauses of the thread itself

Limits. The library's own file names idle cases: in two of the three cases of what can stand at
number 339, and where the reads at number 342 have no arrays, nothing is reached at 346, and the law
speaks of no state; which case holds is said by no file (Johnson/K11R/MaskSeat.lean, Limits). The
hypothesis is a premise; it stands at the earlier hash, and over the form of the proof file's entry
tests with thirteen rows (Johnson/K11R/CondOfEight.lean, Limits). No thread is shown to stand
anywhere. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead
import Johnson.K11R.CondOfPend

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.MergeLaw (MaskAt)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- The statement that the member is there. Not proved here; a lemma's statement, none of the
library's goals. -/
def MaskMemberAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place),
    AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x → ∃ xM : Mem, xAt (P5J.At.ms Zp Z.lay) (73, 2) = some xM

/-- The statement. The letters of the thread: those of `thrS_rchAt`. Fr and a member of its strings:
the library's law speaks of a statement with such a member beside it, and does not read it. Not
proved here; a lemma's statement, none of the library's goals. -/
def MaskAtAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (k : Coins Bk) (s : TS)
    (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env) (Fr : Frame) (_ : Fr.E.Str) (xM : Mem),
    xAt (P5J.At.ms Zp Z.lay) (73, 2) = some xM →
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346 k s m
      E →
    MaskAt (h.𝔇.N.group 24) xM 0 s

end ProofFile.Honest.K11
