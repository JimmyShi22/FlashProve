-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/TieAtAll.lean: THE ITEM "tie l" AT THE READS OF EACH OF THE 25 SEGMENTS, AT THE BASE PROVER: exchangeAtS_tie_base (TieAtBase.lean) with hSt paid by tieStateP_all_head (TieStateAtHead.lean).

  exchangeAtS_tie_all   hF1 and hF2 stand as premises; the binder hI (paid at matrixInput by trace_at_matrix) and hV as in TieAtBase

OF COMPLETENESS's KIND: hI, hV name the input: NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean).
NO PROPERTY IS CLAIMED.
-/
import AtFullSide.K1.TieAtBase
import AtFullSide.K1.TieStateAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.HonestTrace (Sz ServesAt theTrace)
open ProofFile.Honest.FirstThread
open P5J (AtMgA TS)

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **K1's share at the item tie l, at each segment's reads, at the base prover.** -/
theorem exchangeAtS_tie_all
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref openHonest) = .ok A)
    (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (Q : Script A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop) (Rd : Nat → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (hI : ∀ u ξ C, I.trace A.Z u ξ = some C → ∃ i x,
      C.cell = OnBytes.HonestTrace.cellOf (P5J.At.X A.Z) (theTrace (P5J.At.X A.Z) i x) ∧
        ServesAt (P5J.At.X A.Z) i x)
    (hV : Vd w → ReadyInput A.F A.H w) {l : ℕ} (hl : l < 25)
    (hF1 : TieMatS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said (P5J.At.cs A.Z)
      (P5J.At.arr A.Z) (P5J.At.ms A.Z Z.lay) Sz.ref (witBT I A.Z) (K1.noL l false) l)
    (hF2 : TieReadsS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said (P5J.At.cs A.Z)
      (P5J.At.arr A.Z) (P5J.At.ms A.Z Z.lay) (witBT I A.Z) (K3.matsOwn (P5J.At.X A.Z) l)
      (K1.noL l false) l (nReads (P5J.At.X A.Z) l)) :
    ExchangeAtS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said (K1.noL l false)
      (.tie l) :=
  exchangeAtS_tie_base hA h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hI hV hl
    (tieStateP_all_head h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hSaid hl) hF1 hF2

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.exchangeAtS_tie_all
