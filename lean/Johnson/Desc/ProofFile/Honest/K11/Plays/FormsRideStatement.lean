-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/FormsRideStatement.lean: THE ITEMS "forms 24 k r" OF THE
FIRST CHAIN's THREAD AT THE LIBRARY's HEAD RIDE PAST THE MERGE's MEMBER, NUMBER 346, AT EVERY NAME
BUT "weights", WHERE THE THREAD's "keeps" AT 346 GIVES THE KIND's STRONGER CLAUSE; AND THE FRAME's
`BehindS` AT THAT CLAUSE: STATEMENTS ALONE: three definitions of propositions. NOTHING IS PROVED IN
THIS FILE, and none is one of the library's goals: they are lemmas' statements.

  `KeepsYesOfStepped`    general in the thread: behind a step of the kind's block as it stands at a
                         seat: `K11KeepsYes` (Johnson/Desc/K11/Returns/KeepsYesStatement.lean)
  `HeadMergeBehindYesS`  general in the thread: `HeadMergeBehindS` (BehindSStatement.lean of this
                         folder) with `K11KeepsYes` where that has `K11Keeps`: the frame's `BehindS`
                         at a thread whose "keeps" is laid at the stronger clause
  `FormsRideAtHead`      at the head's thread: the base Bs · r ≠ "weights" · "keeps" at 346 gives
                         `K11KeepsYes` · run by run under the name: `Fwd` and `NotLate`: the frame's
                         `RidesPastAtS` (Honest/Thread/SharesS.lean) at SaidOk, at 346, at the item
                         .forms 24 k r

Limits. THE PREMISE ON "keeps" STAYS: that letter is not laid at 346. THE TWO PREMISES ON EACH
RUN STAY HERE (what the run's reader answers in front it answers behind; the slot of the merge's end
value is none of the run's late ones): the library has payers for them at the merge from other named
premises (Johnson/Top/H0/MergeLaw/RunsPassAtMerge.lean): not called here. FROM THE PAIR `ThrS` AT
SaidOk, not from the thread's sentence alone: the ledger's sizes in front are taken from
`frontS_at_head`. WHICH ITEMS ARE OPEN ACROSS 346 IS NOT SAID HERE. NOTHING HERE SHOWS THAT A FORM's
SENTENCE HOLDS AT ANY STATE. The two sentences "worth" are not treated. The head is a premise here,
at the earlier hash, at the full size. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.BehindSStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.SeatFieldsStatement
import Johnson.Desc.ProofFile.Honest.Thread.SaidOk
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.Desc.K11.Returns.KeepsYesStatement
import Johnson.Top.H0.MergeLaw.KeepAtMerge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place Claim)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.First.MergeLaw (NotLate)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Reads.Pass (Fwd)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind)
open Johnson.Desc.First.ForkMerge.Returns (K11KeepsYes)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- The statement on the step. Not proved here; a lemma's statement, none of the library's goals.
-/
def KeepsYesOfStepped : Prop :=
  ∀ (Bk : ProverCoinCounts) (V W X Pb : Type) (T : Thread Bk S Claim V W X Pb) (b : Nat) (P : HeadMergeP)
    (name : String) (pl : Place),
    T.bs[b]? = some (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl) →
    ∀ blk k s m E ds y cols s', T.bs[b]? = some blk → T.Stepped blk k s m E ds y cols s' →
      K11KeepsYes P s s'

/-- The statement on the frame's debt behind the member. Not proved here; a lemma's statement, none
of the library's goals. -/
def HeadMergeBehindYesS : Prop :=
  ∀ (Bk : ProverCoinCounts) (V W X Pb : Type) (T : Thread Bk S Claim V W X Pb)
    (Said : Nat → Coins Bk → Mid W X → Prop) (b : Nat) (P : HeadMergeP)
    (name : String) (pl : Place),
    T.bs[b]? = some (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl) →
    (∀ s s', K11KeepsYes P s s' → T.keeps b s s') →
    (∀ blk k s m E ds y cols s', ThrS T Said b k s m E → T.Stepped blk k s m E ds y cols s' →
      T.bs[b]? = some blk → K11KeepsYes P s s' → T.form (b + 1) (T.seat k y.2 s') = true) →
    (∀ blk k s m E ds y cols s', ThrS T Said b k s m E → T.Stepped blk k s m E ds y cols s' →
      T.bs[b]? = some blk → K11KeepsYes P s s' → T.formP (b + 1) (T.seat k y.2 s')) →
    (∀ blk k s m E ds y cols s', ThrS T Said b k s m E → T.Stepped blk k s m E ds y cols s' →
      T.bs[b]? = some blk → K11KeepsYes P s s' → T.rides (b + 1) y.2.st.input s') →
    BehindS T Said b

/-- The statement on the items. Not proved here; a lemma's statement, none of the library's goals.
-/
def FormsRideAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (Bs : ProofFile.PureBase)
    (kk : ℕ) (rr : String), rr ≠ "weights" →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    (∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps 346 s s' →
      K11KeepsYes (_root_.K11.parOf Zp Bs.G₀) s s') →
    (∀ k s m E s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346 k s m
        E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps 346 s s' →
      ∀ p ∈ h.𝔇.runs 24 kk rr, Fwd (h.𝔇.Rd 24) p.1 p.2 s s' ∧
        NotLate (h.𝔇.Rd 24) (_root_.K11.parOf Zp Bs.G₀) p.1 p.2 s) →
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
      (Item.forms 24 kk rr)

end ProofFile.Honest.K11
