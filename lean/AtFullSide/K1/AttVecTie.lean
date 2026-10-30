-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/AttVecTie.lean: vec_att_head (Johnson/Desc/ProofFile/Honest/K1/Law/AttVecAtHead.lean) WITH ITS PREMISE
AttTlS PAID BY attTlS_head (AtFullSide/K1/TieStateAtHead.lean), AND THE NUMBER OF READS AS nReads: the form VecTie
(AtFullSide/K1/ReadsCore.lean) at the twelve attention reads, under the head, hSaid and the plan at g. wit is free: valsAt
at an odd segment does not read the cover.

  nReads_att       nReads at an odd segment is the plan's nW
  vecTie_att_head  THE CLAIM

NO PROPERTY IS CLAIMED.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.AttVecAtHead
import AtFullSide.K1.TieStateAtHead
import AtFullSide.K1.VecTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Model (HTailF2)
open OnBytes.HonestTrace (pairOf heardOf parOfMats)
open OnBytes.HonestTrace.U3 (u3Seats SegVals valsAt covOf)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K3 (matsOwn)
open ProofFile.Honest.K8 (cellsAtOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)

/-- nReads at an odd segment below 24 is the plan's number of reads. -/
theorem nReads_att {X : OnBytes.Model.Verify.Public} {g : ℕ} (hg : g < 12) {A : OnBytes.Attention.Plan}
    (hA : X.A[g]? = some A) : nReads X (2 * g + 1) = A.nW := by
  unfold nReads
  rw [if_neg (by omega), if_neg (by omega), show (2 * g + 1) / 2 = g by omega, hA]
  rfl

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)

set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)

include hSaid in
/-- **VecTie at an attention's reads, under the head**, at nReads. wit is free: valsAt at an odd segment does not read the
cover. -/
theorem vecTie_att_head {g : ℕ} (hg : g < 12) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {Ad : MsgAddr} {am : ℕ}
    (hPair : pairOf (u3Seats Zp G) Ad = some (2 * g + 1, am))
    (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst) :
    VecTie (𝕋) Said (K1.noL (2 * g + 1) false) wit Zp G (2 * g + 1) (nReads (P5J.At.X Zp) (2 * g + 1)) Ad := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  obtain ⟨-, -, -, A, -, -, -, -, hA, -⟩ := IM.k5_of h.scope h.reads O g hg
  have hW : Bs.G₀.W = P5J.At.X Zp := O.W
  have hAX : (P5J.At.X Zp).A[g]? = some A := hW ▸ hA
  rw [nReads_att hg hAX]
  exact vec_att_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hg hG hA hPair
    (attTlS_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hSaid O hg hA) wit

end

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.nReads_att
#print axioms ProofFile.Honest.K1.vecTie_att_head
