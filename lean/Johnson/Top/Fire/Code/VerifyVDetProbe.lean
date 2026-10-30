-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Top.Fire.Code.VerifyVDet
import Run.DetOverOne

/-! The statement `VerifyVDetIs` (VerifyVDet.lean), proved: so it is not false.-/

set_option autoImplicit false

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms

theorem evaluate_ofRom' {α : Type} (hash : Hash) : ∀ c : Rom.OComp (rom 256) α,
    (deterministicOf (ofRom c)).evaluate hash = c.det fun _ => hash
  | .pure _ => rfl
  | .query _ q k => evaluate_ofRom' hash (k (hash q))
  | .sample _ k => evaluate_ofRom' hash (k 0)

theorem det_overOneV {S : OSpec} {lam : ℕ} {α : Type} (m : ImplV S lam) (g : Fam (rom lam))
    (c : OComp S α) : (c.overOneV m).det g = c.det (readBlocksV m g) := by
  induction c with
  | pure a => rfl
  | sample n k ih => exact ih 0
  | query o q k ih =>
      show ((askAll lam (m.blocks o) (m.code o q)).bind fun bs =>
          (k ((m.rng o).symm bs)).overOneV m).det g = _
      rw [OComp.det_bind, det_askAll, ih]
      rfl

theorem verifyVDet_is : VerifyVDetIs := by
  intro v hash commitment prompt output proof
  obtain ⟨aux, key, π⟩ := proof
  unfold verifyVDet verifyV ZKCP.verifyBuilt ZKCP.verifyDigestKey
  dsimp only
  cases v.build (prompt, output) aux with
  | none => rfl
  | some x =>
    dsimp only
    cases v.enc key with
    | none => rfl
    | some code =>
      dsimp only
      show (deterministicOf (if hash code = commitment then
          ofRom ((VRAV v.W v.Sd v.cA v.r₀ v.p key x π).overOneV v.m)
        else .pure false)).evaluate hash = _
      by_cases hd : hash code = commitment
      · rw [if_pos hd, if_pos hd, evaluate_ofRom', det_overOneV]
      · rw [if_neg hd, if_neg hd]
        rfl

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.verifyVDet_is
