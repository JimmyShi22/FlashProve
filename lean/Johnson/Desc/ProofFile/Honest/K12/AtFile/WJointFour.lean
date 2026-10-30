-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WJointFour.lean: under the head, what taken_at_lastAt
(WJointLast.lean) asks of the shared chain's tables at tableShared: four lines on Omega's table.

  omega_pub_head       the sending's public part under the head: the shared chain's own plan, at number 0
  omega_arm_head       hO: own 1 of tableShared is the sending's table
  omega_fixed_head     hf: the count at own 1 is behind the number of "LIN point"
  four_on_omega        tableOmega, fixedOmega, rowsOmega at tableShared, fixedShared, witOf

By what. inFront_at_head (K12/AtProof/HalfAtPure.lean), treesU_head (TreesAtShared.lean).

Limits. rounds, the fourth, is r₁'s own definition. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.TreesAtShared
import Johnson.Desc.ProofFile.Honest.Small.FixedSent
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfAtPure
import Johnson.Desc.ProofFile.Honest.K12.AtProof.Members

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Chain K1.qAt)
open Desc.K14 (St blocks P14)
open ProofFile.Honest.K14 (SendPub jobOmega sendPlace sendTable witOf)
open ProofFile.Honest.K12.AtProof (sendPub)
open P2Law.ProofPlan (declProofFull)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {W₀ Rc X₀ : Type} {Bk : ProverCoinCounts}

/-- **The sending's public part under the head.** -/
theorem omega_pub_head (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {An : SendPub}
    (hAn : sendPub Zp = some An) : An = ⟨K1.qAt Zp Np, 0⟩ := by
  have hA := hAn
  unfold sendPub at hA
  rw [(ProofFile.Honest.K14.readers_at Zp Np h.laid.places).1] at hA
  change Option.map _ _ = some An at hA
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hA
  have e := ProofFile.Honest.K12.AtProof.inFront_at_head h b1 b2 b3 b4 b5 b6 b7 b8 hb
  rw [e] at ha
  obtain rfl := Option.some.inj ha
  rfl

/-- **hO.** -/
theorem omega_arm_head (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) (wts : W₀ → Weights)
    (rnd : Rc → TableRand) (JU JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀) :
    (tableShared (Bk := Bk) (K1.qAt Zp Np) wts rnd JU JO own₀) (.own 1) =
      sendTable (jobOmega ⟨K1.qAt Zp Np, 0⟩) (witOf (K1.qAt Zp Np) wts rnd) (sendPlace 5) 1 0 := by
  have hu := treesU_head h
  show (if 1 < ProofFile.Honest.K14.treesU (K1.qAt Zp Np) then _ else if 1 < 3 then _ else _) = _
  rw [if_neg (by omega), if_pos (by omega), hu]

/-- Own 1 goes out in round 4. -/
theorem sent_own_one : ProofFile.Honest.Small.sentIn declProofFull.2.1 1 = 4 := by decide +kernel

/-- **hf.** -/
theorem omega_fixed_head : (0 : ℕ) + 1 ≤ fixedShared declProofFull.2.1 (.own 1) := by
  show 0 + 1 ≤ ProofFile.Honest.Small.sentIn declProofFull.2.1 1
  rw [sent_own_one]
  omega

/-- **The premises tableOmega, fixedOmega, rowsOmega of taken_at_lastAt and of
takenAtTheBaseProver, at tableShared, fixedShared and witOf.** rd: the readers of the last chain's input
read the witness's. -/
theorem four_on_omega {L₂ : Type} (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) (wts : W₀ → Weights)
    (rnd : P14 → Rc → TableRand) (JU JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (toCommon : L₂ → Common W₀ Rc TableKey) (gw : L₂ → W₀) (gr : L₂ → Rc)
    (hw : ∀ v, (toCommon v).w₀ = gw v) (hr : ∀ v, (toCommon v).rc = gr v) :
    (∀ An, sendPub Zp = some An →
      (tableShared (Bk := Bk) (K1.qAt Zp Np) wts (rnd (K1.qAt Zp Np)) JU JO own₀) (.own 1) =
        sendTable (jobOmega An) (witOf (K1.qAt Zp Np) wts (rnd (K1.qAt Zp Np)))
          ProofFile.Honest.K12.AtProof.senderO.place 1 0) ∧
    (∀ An, sendPub Zp = some An → An.atPoint + 1 ≤ fixedShared declProofFull.2.1 (.own 1)) ∧
    (∀ An, sendPub Zp = some An → ∀ v,
      (ProofFile.Honest.K12.Light.askOf An (fun v => wts (gw v)) (fun v => rnd An.P (gr v)) v).rows =
        (witOf (K1.qAt Zp Np) wts (rnd (K1.qAt Zp Np)) (toCommon v)).rows) := by
  refine ⟨fun An hAn => ?_, fun An hAn => ?_, fun An hAn v => ?_⟩
  · obtain rfl := omega_pub_head h b1 b2 b3 b4 b5 b6 b7 b8 hb hAn
    exact omega_arm_head h wts (rnd (K1.qAt Zp Np)) JU JO own₀
  · obtain rfl := omega_pub_head h b1 b2 b3 b4 b5 b6 b7 b8 hb hAn
    exact omega_fixed_head
  · obtain rfl := omega_pub_head h b1 b2 b3 b4 b5 b6 b7 b8 hb hAn
    show ProofFile.Honest.K14.rowsOf _ (wts (gw v)) (rnd _ (gr v)) =
      ProofFile.Honest.K14.rowsOf _ (wts (toCommon v).w₀) (rnd _ (toCommon v).rc)
    rw [hw, hr]

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.four_on_omega
#print axioms ProofFile.Honest.K12.AtFile.sent_own_one
#print axioms ProofFile.Honest.K12.AtFile.omega_pub_head
#print axioms ProofFile.Honest.K12.AtFile.omega_arm_head
#print axioms ProofFile.Honest.K12.AtFile.omega_fixed_head
