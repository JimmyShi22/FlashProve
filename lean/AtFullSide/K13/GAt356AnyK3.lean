-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K13/GAt356AnyK3.lean: kind K13, the members' batching: UNDER THE LIBRARY's ONE HYPOTHESIS
AT THE FULL SIZE, h (`P5J.AtMgA`; the format's second hash function) AND A BASE (hB: under h there is one:
`base_at_head`, Johnson/Desc/ProofFile/Honest/K13/AcceptedByTies.lean): AT THE CLOSED TERM
`pileAnyK3` (Honest/K13/PileOfAnySize.lean) FOR THE PILE's FILLER, AT THE BASE's GROUND: THE
LIBRARY's SENTENCE `PileIs` HOLDS AT THE BORDER 355; AND SO THE ROW WEIGHTS THAT THE FILLING OF W's
MAIN ROW MAKES ARE THE CLAIM's. Two statements with their proofs: calls; no definition; no closed
fact of its own. THE EQUATIONS READ PUBLIC DATA ALONE: the verifier's state, the instance, the
challenges heard. THE THREAD IN FRONT OF THE SECOND, AS IT IS TYPED, NAMES A RUN's COINS AND A
SCRIPT.

Main names: `k13_pileIs_pileAnyK3`; `k13_g_at_356_pileAnyK3`: **the premise hPile of `k13_g_at_356`
(GAt356.lean of this folder) is gone at that filler.**

How. `pileAnyK3` is `pileOfAnySize` at two written parameters, by its text; under h, at a base's
ground, that is the filler over the text of the claims with all its arms laid (`pileOfAnySize_at`,
Honest/K13/PileOfAnySizeAt.lean); `k13_pileIs_at_head` (Honest/K13/PileIsAtHead.lean), whose
parameter Q₀ is free; `k13_g_at_356`.

Limits. CONDITIONAL ON h AND hB: that h can be met is not shown here (Honest/Thread/FirstHead.lean's
head says what is had of it). THE SECOND STATEMENT KEEPS THREE PREMISES BEHIND ITS COLON: the thread
in front of number 356, the reply as asked, the one row on the state's table: what is gone is the
premise on the filler alone. `PileIs` IS AN IMPLICATION FROM THE RETURN OF THE VERIFIER's FOLD: that
a fold returns anywhere is not said. THAT THE FILLER YIELDS A ROW AT ANY DATA IS NOT SAID BESIDE
THAT: at the full size it has been evaluated at none. AT THE BASE's GROUND ALONE: that the ground at
which a prover is laid is that one is another law's. Of a row's mask form and target nothing is
said. The row weights hold one value that was sent, the reply as heard: that is what ANY prover
sent: only the premise on the reply makes it the instance's. THE LINK SERVES `WitnessHasW`, AND W IS
LINEAR IN THE WEIGHTS: the second statement never stands in front of a law over coins. Where the
thread stands nowhere it holds for nothing. No filling of a prover is named. The counts beneath rest
on evaluations in Lean's kernel, which no independent checker has replayed. `k13_pileIs_pileAnyK3`
is called by EndsAtBookAnyK3.lean of this folder: no part of the library;
`k13_g_at_356_pileAnyK3` by no file.

What is not claimed. It is none of the library's goals. Nothing on soundness, completeness or
hiding.
-/
import AtFullSide.K13.GAt356
import Johnson.Desc.ProofFile.Honest.K13.PileIsAtHead
import Johnson.Desc.ProofFile.Honest.K13.PileOfAnySizeAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K13
open OnBytes OnBytes.Model
open ProofFile.Honest ProofFile.Honest.K13
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs)
open VerifiableInference.Desc.K13.Honest (PileIs roundsAhead)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **`PileIs` AT THE BORDER 355, OF THE CLOSED TERM `pileAnyK3` AT A BASE's GROUND**: under h and a
base. An implication from the fold's return. -/
theorem k13_pileIs_pileAnyK3 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) (Bs : ProofFile.PureBase)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    PileIs cF.blocksInOrder (fun ξ : ProofFile.Inst => ProofFile.startS Zp ξ.pub) 355 (roundsAhead cF.blocksInOrder 355)
      (pileAnyK3 Zp Bs.G₀) ProofFile.Inst.asked := by
  show PileIs _ _ 355 _ (pileOfAnySize headArmOfSeg q0Idle Zp Bs.G₀) _
  rw [pileOfAnySize_at h q0Idle Bs]
  exact k13_pileIs_at_head h Bs hB _

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE ROW WEIGHTS THAT THE FILLING OF W's MAIN ROW MAKES AT `pileAnyK3` ARE THE CLAIM's**: under
h and a base, from the thread in front of number 356, the reply as asked, and the one row on the
state's table: no premise on the filler is left. -/
theorem k13_g_at_356_pileAnyK3 (Bs : ProofFile.PureBase)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    ∀ k s m En,
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread 356 k s m En →
      ReplyIs ProofFile.Inst.asked m.st.input.x s → ∀ row : TensorRow, s.rows = [row] →
      wG Zp.first.lin (wHeard Zp) (pileAnyK3 Zp Bs.G₀) m.st.input.x
        (m.st.heard.take (wHeard Zp)) = row.g :=
  k13_g_at_356 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ (k13_pileIs_pileAnyK3 h Bs hB)

end AtFullSide.K13

#print axioms AtFullSide.K13.k13_pileIs_pileAnyK3
#print axioms AtFullSide.K13.k13_g_at_356_pileAnyK3
