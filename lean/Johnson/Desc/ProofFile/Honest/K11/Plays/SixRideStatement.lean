-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/SixRideStatement.lean: ALL SIX ITEMS "forms" THAT THE
LIBRARY NAMES AS OPEN ON BOTH SIDES OF THE MERGE (`sixNames`,
Johnson/Top/H0/MergeLaw/FormsBackAtMerge.lean: 3 "objects" · 3 "planes" · 4 "join" · 4 "own" · 6
"small" · 8 "objects", at segment 24) RIDE PAST THE MERGE's MEMBER, NUMBER 346, AT THE FIRST CHAIN's
THREAD AT THE LIBRARY's HEAD, WITH NO PREMISE ON A RUN: A STATEMENT ALONE: one definition of a
proposition. NOTHING IS PROVED IN THIS FILE, and it is none of the library's goals: it is a lemma's
statement.

  `SixFormsRideAtHead`  the base Bs · "keeps" at 346 gives `K11KeepsYes`
                        (Johnson/Desc/K11/Returns/KeepsYesStatement.lean): at every pair y of
                        `sixNames`: the frame's `RidesPastAtS` at SaidOk, at 346, at the item .forms
                        24 y.1 y.2

Why. `FormsRideAtHead` (FormsRideStatement.lean of this folder) leaves two premises on each run
under the item's name. The thread's own form at 346 holds the public tests from which the library's
lemmas have both.

Limits. THE PREMISE ON "keeps" STAYS: that letter is not laid at 346. From the pair `ThrS` at
SaidOk. THAT THE SIX ARE OPEN ACROSS 346 AT THE THREAD IS NOT SAID HERE. NOTHING HERE SHOWS THAT A
FORM's SENTENCE HOLDS AT ANY STATE. The two sentences "worth" and the pile are not treated. The
frame's debt on what rides past 346 is not paid by this: six shares. The head is a premise here, at
the earlier hash, at the full size. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.FormsRideStatement
import Johnson.Top.H0.MergeLaw.FormsBackAtMerge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.First.MergeLaw (sixNames)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.ForkMerge.Returns (K11KeepsYes)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- The statement. Not proved here; a lemma's statement, none of the library's goals. -/
def SixFormsRideAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (Bs : ProofFile.PureBase),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    (∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps 346 s s' →
      K11KeepsYes (_root_.K11.parOf Zp Bs.G₀) s s') →
    ∀ y ∈ sixNames,
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
        (Item.forms 24 y.1 y.2)

end ProofFile.Honest.K11
