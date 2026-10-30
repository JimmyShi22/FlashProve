-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.LLT25R.LastSeat
import Johnson.Desc.K12.Coin.LawAtTileThird
/-
TYPED WITHOUT A COMPILER. FOR A BUILD THAT HOLDS BOTH SIDES.

(Where this and lean/THEOREM.md differ, the page holds.)
Johnson/Loose/H2K12/LastRestAtW.lean:
FOUR FIELDS OF THE LAST CHAIN's LEDGER (Johnson/LLT25R/LastLedger.lean: LastRest.joh · batOne ·
count · errs) AT THE PROOF FILE's OWN DESCRIPTION FL, FROM K12's FILES' RECORD AT THE PLACE W
(ClosedL) AND TWO NUMBERS OF THE PLACE. One theorem; its proof is a row of calls.
WHOSE: the statement's right side is the ledger's own text, field for field; FL, c0 to c3,
last_flat_pure (Johnson/LLT25R/LastSeat.lean), ds₂, capB, capT (Johnson/Flat/Last/): other files';
ClosedL (Coin/LawAtLight.lean), count_errs_tile₃ (Coin/LawAtTileThird.lean), batOneOk_of_planOk: K12's files'.
WHAT IT IS NOT: ClosedL, "no own mask" and "no root in front" are PREMISES here. In the goals' scope
they are paid at K12's FILES' name of the description (descN …: closedL_in_scope_W ·
ownMask_in_scope_W, H2K12/ClosedAtSeats.lean), not at FL: that tie is typed nowhere.

(Where this and lean/THEOREM.md differ, the page holds.)
Nothing on soundness.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K.AtW
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Coin
open H2K.Pub (johOk batV0)
open H2K.First (batOneOk)
open LLT25 (FL c0 c1 c2 c3 last_flat_pure)

/-- **The ledger's four fields at W.** -/
theorem four_at_W (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub) (A : ProofFile.SharedSeat)
    (N : H2U.Places4) (c : Chain First.S ProofFile.Cl) (file : String) (D : WholeD)
    (r : Fmt.M1.Stage → ℕ) (ch b₁ b₂ : ℕ) (T : List (Fmt.TreeSource × ℕ)) (dB : RDT) (dt : List RDT)
    (hcl : ClosedL (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) r ch b₁ b₂ T)
    (ho : (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.ownMask = false)
    (hfree : (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.free = 0)
    (h : (FL o mk Z A N c).data file = .ok D)
    (hds : ds₂ D.ds₃
      (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) (c0 Z))
      (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) (c1 N))
      (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) (c2 N)) =
        dB :: dt) :
    johOk (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) r = true ∧
      batOneOk (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) = true ∧
      batV0 (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) r * (bsRound .two dB.entry dB.kind).w ≤
        capB dB dt ∧
      Err.le (errJ (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) r dt) (capT dB dt) :=
  ⟨hcl.joh, H2K.Made.batOneOk_of_planOk guardedProximityTestParts _ hcl.plan,
    count_errs_tile₃ (FL o mk Z A N c) file D h (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) r
      [c0 Z, c1 N] (c2 N) [c3 Z N] (last_flat_pure o mk Z A N c) rfl hfree hcl.plan hcl.chain
      hcl.joh hcl.bat ho dB dt hds⟩

end H2K.AtW

#print axioms H2K.AtW.four_at_W
