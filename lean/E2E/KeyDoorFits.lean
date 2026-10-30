-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyDoorFits.lean: door_whole's premise hfit, out of a tie: a key tied to the committer's sample
fits the sizes, and at the shared chain's thread at the key the only valid input is the letter w.

  keyFits_of_tied   the body of hFits in E2E/OfflineSharedAtTied.lean, as a lemma at TiedOffline
  door_fits         hfit at the thread

Nothing on any property.
-/
import E2E.KeyOodTie
import E2E.KeySharedThread
import E2E.KeyThePartsFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm
open OnBytes (TableKey)
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open VerifierAndGoals (PublicFiles InScope)
open AtPublicFiles.KeyFiveFields (pubKey)
open AtPublicFiles.KeyOodTie (validAt_of_tied)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open Bind.ForProver (oodSh shapeOf keyFits_oodSh_of)
open AtPublicFiles.KeyStoredTie (readF readG)

/-- **A key tied to the committer's sample fits the sizes.** -/
theorem keyFits_of_tied {Z : PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
    {Q₂ Q₃ X₀ Xh Wk : Type} [Nonempty Q₂] [Inhabited Q₃] {val₂ : Q₂ → ByteArray}
    {val₃ : Q₃ → ByteArray} {K : KeyParts FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) X₀ Xh Wk} {ok : FullSizeMatrix → Prop}
    {w : FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed} {x : KeyInst}
    (sourced : KeySourced Z X N P) (scope : InScope Z = true)
    (hKey : (keyProver K).key = fun y => y.key)
    (ht : TiedOffline Z X N P val₂ val₃ K ok w x) (Z₀ : ProofFile.Pub) :
    keyFits x.key AtPublicFiles.AtFiles.Full.QK.par.S.fold.index = true := by
  have hk := AtPublicFiles.AtFiles.sized_sourced sourced scope
  obtain ⟨sd, hsd⟩ := validAt_of_tied Z hKey ht Z₀ X.chains hk
  have hsd' : x.key = oodSh (shapeOf (pubKey Z₀ X.chains)) (pubKey Z₀ X.chains)
      ⟨readF w.1, readG w.2.1, sd⟩ := hsd
  rw [← AtPublicFiles.AtFiles.Full.par_sourced sourced scope, hsd']
  exact keyFits_oodSh_of _ _ _ rfl

/-- **hfit**: at the shared thread the only valid input is the letter w. -/
theorem door_fits {W₀ Rc X₀ X Wk : Type} {Bk : ProofFile.Honest.ProverCoinCounts} {Xs : Source} {Nr : H2U.PlaceNums}
    {Pl : LaterPlaces} {K : KeyParts W₀ Rc X₀ X Wk} {P₁ Wt : Type} {ℓ Nm Mg₀ tb rest Kp Vd}
    {w : ProofFile.Honest.Common W₀ Rc TableKey}
    (hf : keyFits w.key AtPublicFiles.AtFiles.Full.QK.par.S.fold.index = true) :
    ∀ v, (AtPublicFiles.KeySharedThread.threadKey (Bk := Bk) (P₁ := P₁) (Wt := Wt) Xs Nr Pl K ℓ Nm Mg₀ tb rest
      Kp Vd w).valid v → keyFits v.key AtPublicFiles.AtFiles.Full.QK.par.S.fold.index = true := by
  intro v hv
  have e : v = w := hv.1
  rw [e]
  exact hf

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.keyFits_of_tied
#print axioms AtPublicFiles.AtFiles.HonestTerm.door_fits
