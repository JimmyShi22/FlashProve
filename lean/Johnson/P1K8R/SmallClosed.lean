-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/SmallClosed.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: A
PAYMENT BENEATH THE KIND'S FROZEN CONDITION: THE FIELD `small` OF `K8LeftT`, TO THE LETTER, FROM THE
HEAD AND CLOSED TESTS ON PUBLIC DATA ALONE. NO SOUNDNESS.

`small_of_plan` (SmallAtHead.lean) has the field from the head, the facts along "reached"
(`FoldFacts`) and the closed sentences `SmallPlan`. Another file has `FoldFacts` at the head's
closed term under three closed premises (`P5J.foldFacts_at_head'`, Johnson/P5J/FoldJ3Whole.lean).
`SmallPlan` follows from one test with code a link (`smallPlan_of_test`, SmallPlanTest.lean).
Here the three are joined:
  `small_closed`: **under the head, at every link l ≤ 24 and every condition that gives `RchAt`:
    "the plan's list of seats can be laid", that file's two closed premises `startB` and `SendsB`,
    and `smallPlanB Zp cF L₀ l Xl = true` give `K8LeftT`'s field `small`, to the letter.** NO
    PREMISE READS A STATE OR A WITNESS.
Limits. That the head can be met, and that the four closed premises hold at any files, is shown
nowhere here. AT `OnBytes.secondHashFunction` ALONE. Nothing on soundness.

-/
import Johnson.P1K8R.SmallPlanTest
import Johnson.P5J.FoldJ3Whole

set_option autoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open Iop
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain Place Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.First.K8
open Johnson.Desc.First.Walk.Tied (RchAt)
open Desc.K14.Law (secondAt seatZ)
open ProofFile (Cl)
open P5J (AtMgA mgAtAll)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **THE FIELD `small` OF `K8LeftT`, TO THE LETTER, FROM THE HEAD AND CLOSED TESTS ALONE.** -/
theorem small_closed (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {Fr : Frame} {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24) {Xl : LinkH}
    (e3 : G.built[l]? = some Xl) {Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop}
    (hRch : ∀ k a, Rch k a → RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a)
    {L₀ : VerifiableInference.Desc.K12.Door.Laid} (hL₀ : P5J.At.laid? Zp = some L₀)
    (hs : VerifiableInference.Desc.First.FillP1.startB Zp
      (VerifiableInference.Desc.K12.Door.msgsOfChain Zp.made.proof.1)
      (P5J.At.N Zp cF).indexNo = true)
    (hB : P5J.SendsB Zp) (hT : smallPlanB Zp cF L₀ l Xl = true) :
    ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str) w,
      onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
        (fun s => (z, s)) (drawAt l) a →
      Rch (drawAt l) ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none →
      TieAt (cellsAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l
        (z, a.1)) a.1 w →
      (mgAtAll h).constr l .small (z, a.1) (strsOf Fr a.2) w :=
  small_of_plan h hG hl e3 hRch (P5J.foldFacts_at_head' h.toAtMg Rch hRch hL₀ hs hB)
    (smallPlan_of_test hT)

end P1K8T

#print axioms P1K8T.small_closed
