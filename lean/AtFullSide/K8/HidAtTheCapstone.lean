-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/HidAtTheCapstone.lean: the two binders on the private stops of the last statement on
completeness, at rows whose parts are the prover's own.

  hid_at_the_capstone   HidSmall at the served requests, at 2 ^ (-174)
  hid_in_room           that number lies within its room

Limits. Those of Johnson/P1K8R/WindowAtTerm.lean.
-/
import Johnson.P1K8R.WindowAtTerm
import E2E.TheRooms
import E2E.CompleteAsIOPServedLaws

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.AtFiles.HonestTerm
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed AtPublicFiles.Cut
open ProofFile.Honest.Term (OnlineReturn onlineMaker)
open LPFD.Full (instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed committerCoinCountLessOne)
open P5J

local instance (priority := high) nonemptyPadZ_hidAtTheCapstone : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

local instance (priority := high) nonemptyRunValue_hidAtTheCapstone : Nonempty RunValue :=
  ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_hidAtTheCapstone : Inhabited RunValue :=
  ⟨fun _ => 0⟩

/-- **The number lies within its room.** -/
theorem hid_in_room : ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ)) ≤ AtPublicFiles.TheRooms.onlineHidRoom := by
  have e : (2 : ℝ) ^ (-100 : ℝ) = ((2 : ℝ)⁻¹) ^ (100 : ℕ) := by
    rw [Real.rpow_neg (by norm_num), inv_pow]
    norm_num
  have h₁ : ENNReal.ofReal ((2 : ℝ) ^ (-100 : ℝ)) = AtPublicFiles.TheRooms.onlineHidRoom := by
    rw [e, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
    show _ = ((2 : ℝ≥0∞)⁻¹) ^ 100
    norm_num
  rw [← h₁]
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))

variable {Z : PublicFiles} {A : OnlineReturn Z}

/-- **The binder hid**, at rows whose parts are the prover's own. -/
theorem hid_at_the_capstone {pp : Inst.Model.ScalesAndPolicy} (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hA : onlineMaker Z = .ok A) {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} (hNp : H2U.placesOfMade A.Z.made = .ok Np)
    (hcF : ProofFile.onlineFirstChainAt A.Z = .ok cF)
    (G : ProofFile.Honest.Sides (descZ A.Z Np cF) A.B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness OnBytes.TableKey
      ProofFile.Honest.Cells Unit Unit)
    (hG : G.prover A.H = A.H) :
    HidSmall (famG Z A.Z Np cF runValueBytes runValueBytes A.B G A.H)
      (fun n w a => TiedYes Z A.Z Np cF runValueBytes runValueBytes A.B G A.H
        (ServedRequest committerCoinCountLessOne Z hr) n w (instanceAsPlainRecord a))
      (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) :=
  hid_small_at_rows scope hr live hA hNp hcF G hG
    (fun _ _ h => servedRequest_below committerCoinCountLessOne Z scope hr h)

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.hid_in_room
#print axioms AtPublicFiles.AtFiles.HonestTerm.hid_at_the_capstone
