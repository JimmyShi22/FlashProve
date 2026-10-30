-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FHeadJ.lean: the clause keeps with one relation more: at the
kind K12 the state after the step is one that the proximity test's decision at the finish returns.
fHeadI (Honest/Thread/FHeadI.lean) holds K12KeepsFirst there, which what rides past the member needs
more of. A definition, and what it gives at the lower clause.

  relsFinish   the relation: at K12 the accepted step itself; everywhere else True
  fHeadJ       fHeadI with it beside
  kpBy_fHeadJ  fHeadJ implies fHeadI
  cellJ_of_I   a cell of the column hR at fHeadI is one at fHeadJ
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHeadI
import Johnson.Desc.K12.AtFinish

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-- What the riders past the proximity test need of keeps: at K12 the state after the step is one
that the decision at the finish returns. Everywhere else it is True. -/
def relsFinish (p12 : VerifiableInference.Desc.K12.P12) : KindName → TS → TS → Prop
  | .K12 => fun s s' => ∃ rs gs, (VerifiableInference.Desc.K12.atFinish p12).decide s rs gs = .ok s'
  | _ => fun _ _ => True

/-- fHeadI with this relation beside it. -/
def fHeadJ (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl) (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) (D : VerifiableInference.Desc.First.PubData) :
    KindName → Place → TS → TS → Prop :=
  fun κ p s s' => fHeadI Zp cF G take P11 p12 P13 D κ p s s' ∧ relsFinish p12 κ s s'

/-- fHeadJ implies fHeadI. -/
theorem kpBy_fHeadJ {Zp : ProofFile.Pub} {cF : Chain TS ProofFile.Cl} (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) (Dp : VerifiableInference.Desc.First.PubData) :
    ∀ p s s', kpBy (fHeadJ Zp cF G take P11 p12 P13 Dp) p s s' →
      kpBy (fHeadI Zp cF G take P11 p12 P13 Dp) p s s' :=
  fun _ _ _ hk => hk.1

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- A cell of the column hR at fHeadI is one at fHeadJ. -/
theorem cellJ_of_I {b : Nat} {i : Item}
    (hc : RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadI Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said b i) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said b i :=
  head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (kpBy (fHeadI Zp cF G take P11 p12 P13 h.𝔇.pubD)) w
    (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD))
    (kpBy_fHeadJ G take P11 p12 P13 h.𝔇.pubD) Said hc

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.kpBy_fHeadJ
#print axioms ProofFile.Honest.FirstThread.cellJ_of_I
