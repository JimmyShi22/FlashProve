-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastVisStand.lean: the half on W of (Dot) at a stand of the first thread at 19, at the thread's witness: `w_is_at_stand` through `vis_rows`.

  `hv_stand`.

What stays open. The premises of `w_is_at_stand`. Of the witness u: that its first half is the thread's. What remains to the door: the same shape, codes, number and weights on
the last chain's side: four equations on the value.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyLastVis
import E2E.KeyLastDotOwn
import E2E.KeyLastEvOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyLastChain
open OnBytes OnBytes.Params OnBytes.Slice
open OnBytes.Means (Words)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces rowOfLinClaim)
open VerifiableInference.Desc.K13.Law (WIs ρg)
open _root_.Desc.K14.Law (VIs)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.KeyValues (oneOf matrixEntryOf firstW)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.FirstH (Th FirstPublic WPublic HeardOfFold LaterFill HCells HTab fillH w_is_at_stand)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest

variable {W₀ Rc X₀ X' Wk : Type} {K₀ : KeyPub} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {Z : PublicFiles}
  {K : KeyParts W₀ Rc X₀ X' Wk} {f : W₀ → ProofFile.Honest.Weights} {Q : LaterFill (keyBook K₀) W₀ Rc}
  {w₀ : W₀} {rc : Rc} {x : Xi}

/-- **The half on W at a stand at 19.** -/
theorem hv_stand (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) (hK : fullPub = some K₀)
    (hp : FirstPublic (Pl := Pl) Xs N K f) (hw : WPublic Xs N Pl) (hF : HeardOfFold Xs N Pl)
    {k : Coins (keyBook K₀)} {e₁ : FirstState} {m : Mid (In1 W₀ Rc) X'} {E : Env}
    (hT : Thr (Th Xs N Pl K f Q w₀ rc x) 19 k e₁ m E) (rd : ProofFile.Honest.TableRand) (u : Wit HCells Unit HTab × Words GE)
    (hu : u.1 = (Th Xs N Pl K f Q w₀ rc x).wit k m.st.input (m.st.heard ++ [])) :
    VIs (oneOf Xs).lin (gKey (x, e₁))
      (fun r j => ρg.val (ProofFile.Honest.K14.rowsOf (oneOf Xs).lin (f m.st.input.w₀) rd r j))
      (wvK (val₁Key Xs (fillH Xs N Pl K f Q x)) (oneOf Xs).lin (oneOf Xs).codes (firstW Xs) u) := by
  obtain ⟨l, hl, hW⟩ := w_is_at_stand hs scope hK hp hw hF hT []
    (matBits (oneOf Xs).lin (matrixEntryOf f m.st.input)) (fun i e he => matBits_low _ _ i e he)
  have hv := vis_rows (oneOf Xs).lin (matrixEntryOf f m.st.input) rd.pad rd.tail _ _ _ _ hW
  have eg : gKey (x, e₁) = fun y => (l.claim.g.map fun g => ρg.val (g.entry y)).sum := by
    funext y
    unfold gKey
    simp only [hl, Option.map_some, Option.getD_some]
    rfl
  rw [eg]
  unfold wvK val₁Key
  rw [hu]
  exact hv

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.hv_stand
