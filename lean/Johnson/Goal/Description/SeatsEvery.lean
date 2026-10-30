-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Description/SeatsEvery.lean: the two files' seats' equations in the shape «for every
description that the maker returns», and what the seats do where the maker refuses.
`pseat_every`: where `protocolDataWellFormed` says yes: EVERY F that `ProofFile.onlineDescription` returns at the three public
files and the format's second hash function passes its tests on the plan and every test of
`LPFD.lawsAsk`; its own data are `theProofData`; its own run at `LPFD.Full.instanceAsPlainRecord` is `theProofRun`.
`kseat_every`: the like for the key file: every F that `Key.descAt` returns at what `publicOfO`
reads. Both off `pseat_name` | `kseat_name`: a maker returns one value.
`theProofLaid_no_of_desc`, `theKeyLaid_no_of_public`: where the maker refuses, or the public files
are not read, the seat refuses. `theLive_no_of_pdesc`, `theLive_no_of_public`,
`theLive_no_of_kdesc`: so `protocolDataWellFormed` says no there, and the slots behind the gates say no to all
(Gates.lean; Dead.lean).
Limits. Equations between names: nothing on soundness. The first two stand under `protocolDataWellFormed`'s yes;
`protocolDataWellFormed` says yes at the written copies by theorem (AtFullSide/Top/), as bytes by evaluation alone.

-/
import Johnson.Goal.Description.KeySeat
import Johnson.Goal.Description.ProofSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open VerifierAndGoals
open VerifiableInference.Desc.Key
open VerifiableInference.PlanWritten (publicOfO)

/-- **Every description that the proof file's maker returns is the one behind the gate.** -/
theorem pseat_every (Z : PublicFiles) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (F : VerifiableInference.Desc.FileDescription ProofFile.Inst)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok F) :
    F.planOk = true ∧ F.data "proof file" = .ok (theProofData (asDescriptionFiles Z)) ∧
      (∀ t ∈ LPFD.lawsAsk OnBytes.secondHashFunction Z.pol Z.lay Z.KL F (theProofData (asDescriptionFiles Z)),
        t.2 = true) ∧
      theProofRun (asDescriptionFiles Z) = (F.pull LPFD.Full.instanceAsPlainRecord).run := by
  obtain ⟨F', h, rest⟩ := pseat_name Z live
  obtain rfl : F' = F := Except.ok.inj (h.symm.trans hF)
  exact rest

/-- **Every description that the key file's maker returns is the one behind the gate.** -/
theorem kseat_every (Z : PublicFiles) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (X₀ : OnBytes.Model.Verify.Public) (F : VerifiableInference.Desc.FileDescription Xi)
    (hX : publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hF : descAt X₀ Z.lay fixedDigest = .ok F) :
    F.planOk = true ∧ F.wantedOk = true ∧ F.owedOk = true ∧
      F.data "key file" = .ok (theKeyData (asDescriptionFiles Z)) ∧
      theKeyRun (asDescriptionFiles Z) = (F.pull keyInstanceOfOutOfDomainSample).run := by
  obtain ⟨X₁, m, X, N, P, h1, _, h3, h4, h5, h6, _, h8, h9⟩ := kseat_name Z live
  obtain rfl : X₁ = X₀ := Except.ok.inj (h1.symm.trans hX)
  obtain rfl : descriptionFromSource X N P = F := Except.ok.inj (h3.symm.trans hF)
  exact ⟨h4, h5, h6, h8, h9⟩

/-- Where the proof file's maker refuses, its seat refuses. -/
theorem theProofLaid_no_of_desc (Zk : OnBytes.K.Pub) (e : String)
    (h : ProofFile.onlineDescription OnBytes.secondHashFunction Zk.pol Zk.lay Zk.KL = .error e) :
    theProofLaid Zk = .error ("the proof file's description is not made: " ++ e) := by
  show LPFD.Full.proofDataAndDecisionOfPublicFiles OnBytes.secondHashFunction Zk.pol Zk.lay Zk.KL = _
  unfold LPFD.Full.proofDataAndDecisionOfPublicFiles
  rw [h]

/-- So `protocolDataWellFormed` says no there. -/
theorem theLive_no_of_pdesc (Zk : OnBytes.K.Pub) (e : String)
    (h : ProofFile.onlineDescription OnBytes.secondHashFunction Zk.pol Zk.lay Zk.KL = .error e) : protocolDataWellFormed Zk = false :=
  theLive_no_of_proof Zk _ (theProofLaid_no_of_desc Zk e h)

/-- Where the public files are not read, the key file's seat refuses. -/
theorem theKeyLaid_no_of_public (Zk : OnBytes.K.Pub) (e : String)
    (h : publicOfO OnBytes.secondHashFunction Zk.pol Zk.KL (some Zk.lay) = .error e) :
    theKeyLaid Zk = .error e := by
  show (publicOfO OnBytes.secondHashFunction Zk.pol Zk.KL (some Zk.lay)).bind (fun X => keyDataAndDecisionAtFixedDigest X Zk.lay) = _
  rw [h]
  rfl

/-- So `protocolDataWellFormed` says no there. -/
theorem theLive_no_of_public (Zk : OnBytes.K.Pub) (e : String)
    (h : publicOfO OnBytes.secondHashFunction Zk.pol Zk.KL (some Zk.lay) = .error e) : protocolDataWellFormed Zk = false :=
  theLive_no_of_key Zk _ (theKeyLaid_no_of_public Zk e h)

/-- Where the key file's maker refuses, `protocolDataWellFormed` says no. -/
theorem theLive_no_of_kdesc (Z : PublicFiles) (X₀ : OnBytes.Model.Verify.Public) (e : String)
    (hX : publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀)
    (h : descAt X₀ Z.lay fixedDigest = .error e) : protocolDataWellFormed (asDescriptionFiles Z) = false := by
  cases hl : protocolDataWellFormed (asDescriptionFiles Z) with
  | false => rfl
  | true =>
    obtain ⟨X₁, m, X, N, P, h1, _, h3, _⟩ := kseat_name Z hl
    obtain rfl : X₁ = X₀ := Except.ok.inj (h1.symm.trans hX)
    rw [h] at h3
    cases h3

end FlashProve

#print axioms FlashProve.pseat_every
#print axioms FlashProve.kseat_every
#print axioms FlashProve.theProofLaid_no_of_desc
#print axioms FlashProve.theLive_no_of_pdesc
#print axioms FlashProve.theKeyLaid_no_of_public
#print axioms FlashProve.theLive_no_of_public
#print axioms FlashProve.theLive_no_of_kdesc
