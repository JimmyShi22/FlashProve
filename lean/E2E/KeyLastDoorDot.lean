-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastDoorDot.lean: the premise `hV` of `door_dot` (F8's E2E/KeyDoorDot.lean), so the item (Dot) at the key's door, from `hv_stand`: the first half of the last witness is the first thread's witness,
and the rows of the shared chain are those of the weights that W's sending reads.

  `hv_door`, `hdot_door`.

Left as premises: the four equations on the value: hS, hS', hc (the shapes and codes), hn (W's number); hf: the key's weights are f. The premises of `hv_stand`.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyLastVisStand
import E2E.KeyDoorDot

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyLastChain
open OnBytes OnBytes.Params OnBytes.Slice
open OnBytes.Means (Words)
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces thirdPar descriptionFromSource)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law (VIs)
open AtPublicFiles.KeyFile (KeyParts In1 keyProver)
open AtPublicFiles.KeyValues (oneOf firstW)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.AtFiles (KeySourced CF)
open AtPublicFiles.AtFiles.Full (A0)
open AtPublicFiles.FirstH (Th FirstPublic WPublic HeardOfFold LaterFill HCells HTab fillH tbH)
open AtPublicFiles.KeySharedThread (parKey randKey threadKey)
open AtPublicFiles.KeyThread (decl₁ laid₁)
open AtPublicFiles.KeyDoorItems (wit₃ commonOf)
open ProofFile.Honest
open ProofFile.Honest.K14 (WitLens holds2)
open VerifierAndGoals (PublicFiles InScope)

variable {W₀ Rc X₀ X' Wk P₂ Wt₂ : Type} {K₀ : KeyPub} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {Z : PublicFiles}
  {K : KeyParts W₀ Rc X₀ X' Wk} {f : W₀ → ProofFile.Honest.Weights} {Q : LaterFill (keyBook K₀) W₀ Rc}
  {w₀ : W₀} {rc : Rc} {x : Xi}
  (ℓ₂ : WitLens Wt₂) (Nm : NumbersS)
  (Mg₂ : Common W₀ Rc TableKey → MeaningS St P₂ Wt₂)
  (tb₂ : Fmt.TreeSource → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest₂ : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt₂)
  (Kp₂ : Nat → St → St → Prop) (Vd₂ : Common W₀ Rc TableKey → Prop)
  (w₂ : Common W₀ Rc TableKey)

set_option maxHeartbeats 2000000 in
/-- **The half on W at the door.** -/
theorem hv_door (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) (hK : fullPub = some K₀)
    (hp : FirstPublic (Pl := Pl) Xs N K f) (hw : WPublic Xs N Pl) (hF : HeardOfFold Xs N Pl)
    (hS : (parKey Xs Pl).par.S = (oneOf Xs).lin) (hS' : (thirdPar Xs.chains).S = (oneOf Xs).lin)
    (hc : CF = (oneOf Xs).codes) (hn : A0.2.w = firstW Xs) (hf : K.weights = f)
    (hw₂ : w₂ = commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit))
    {k : Coins (keyBook K₀)} {e₁ : FirstState} {m₁ : Mid (In1 W₀ Rc) X'} {E₁ : Env}
    (hT : Thr (Th Xs N Pl K f Q w₀ rc x) 19 k e₁ m₁ E₁) (hl : m₁.st.heard.length = (decl₁ (descriptionFromSource Xs N Pl)).length)
    (rest : List Fmt.Drawn) :
    VIs (parKey Xs Pl).par.S (gKey (x, e₁)) (holds2 (parKey Xs Pl) K.weights (randKey K) k w₂).Rw
      (wvK (val₁Key Xs (fillH Xs N Pl K f Q x)) (thirdPar Xs.chains).S CF A0.2.w
        (wit₃ Xs N Pl K (fillH Xs N Pl K f Q x) ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ k ⟨w₀, rc, x, ()⟩ (m₁.st.heard ++ rest))) := by
  have hin : m₁.st.input = ⟨w₀, rc, x, ()⟩ := (hT.2.2.2.2.2.2.1 : _)
  have hfst : (wit₃ Xs N Pl K (fillH Xs N Pl K f Q x) ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ k ⟨w₀, rc, x, ()⟩ (m₁.st.heard ++ rest)).1 =
      (fillH Xs N Pl K f Q x).wit k w₀ rc ((m₁.st.heard ++ rest).take (decl₁ (descriptionFromSource Xs N Pl)).length) [] := rfl
  have hTh : (Th Xs N Pl K f Q w₀ rc x).wit k m₁.st.input (m₁.st.heard ++ []) =
      (fillH Xs N Pl K f Q x).wit k m₁.st.input.w₀ m₁.st.input.rc (m₁.st.heard ++ []) [] := rfl
  have hRw : (holds2 (parKey Xs Pl) K.weights (randKey K) k w₂).Rw =
      fun r j => rdE.val (ProofFile.Honest.K14.rowsOf (parKey Xs Pl).par.S (K.weights w₂.w₀) (randKey K w₂.rc) r j) := rfl
  generalize wit₃ Xs N Pl K (fillH Xs N Pl K f Q x) ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ k ⟨w₀, rc, x, ()⟩ (m₁.st.heard ++ rest) = u at hfst ⊢
  have hu : u.1 = (Th Xs N Pl K f Q w₀ rc x).wit k m₁.st.input (m₁.st.heard ++ []) := by
    rw [hTh, hfst, hin, List.append_nil, ← hl, List.take_left]
  have hv := hv_stand hs scope hK hp hw hF hT (randKey K w₂.rc) u hu
  have hwe : w₂.w₀ = m₁.st.input.w₀ := by
    rw [hw₂, hin]
    rfl
  rw [hRw, hS]
  try rw [hS']
  rw [hc, hn, hf, hwe]
  exact hv

/-- **The item (Dot) at the key's door**: the premise `hdot` of `door_behind_key`, at the one (Dot), from `hv_door` and `hdot_key`. -/
theorem hdot_door (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) (hK : fullPub = some K₀)
    (hp : FirstPublic (Pl := Pl) Xs N K f) (hw : WPublic Xs N Pl) (hF : HeardOfFold Xs N Pl)
    (hS : (parKey Xs Pl).par.S = (oneOf Xs).lin) (hS' : (thirdPar Xs.chains).S = (oneOf Xs).lin)
    (hc : CF = (oneOf Xs).codes) (hn : A0.2.w = firstW Xs) (hf : K.weights = f)
    (hw₂ : w₂ = commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit))
    (D : MeaningS St (Xi × FirstState) (Wit HCells Unit HTab × Words GE))
    (k : Coins (keyBook K₀)) {e₁ : FirstState} {m₁ : Mid (In1 W₀ Rc) X'} {E₁ : Env} {e₂ : St}
    {m₂ : Mid (Common W₀ Rc TableKey) X₀} {E₂ : Env}
    (u₁ : Thr (Th Xs N Pl K f Q w₀ rc x) 19 k e₁ m₁ E₁)
    (u₂ : Thr (threadKey Xs N Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) 12 k e₂ m₂ E₂)
    (y : VerifiableInference.Desc.Strs) (ds : List Fmt.Drawn) :
    (AtPublicFiles.KeyDotItem.dotFill (parKey Xs Pl).par.S gKey
      (fun _ => wvK (val₁Key Xs (fillH Xs N Pl K f Q x)) (thirdPar Xs.chains).S CF A0.2.w) D).dot (x, e₁) e₂ y
      (wit₃ Xs N Pl K (fillH Xs N Pl K f Q x) ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ k ⟨w₀, rc, x, ()⟩
        (m₁.st.heard ++ (m₂.st.heard ++ ds))) := by
  obtain ⟨l₁, -, -⟩ := AtPublicFiles.KeyThread.lengths scope hs.named
  obtain ⟨nO, hO⟩ := AtPublicFiles.KeyDoorDot.omega_place hs scope
  have hl : m₁.st.heard.length = (decl₁ (descriptionFromSource Xs N Pl)).length := by
    have e := (Th Xs N Pl K f Q w₀ rc x).heard_length u₁.2.1
    rw [e]
    show 0 + (declsTo (descriptionFromSource Xs N Pl).first.blocksInOrder 19).length = _
    rw [Nat.zero_add, ← l₁]
    unfold declsTo
    rw [List.take_length]
  exact AtPublicFiles.KeyDotKey.hdot_key Xs N Pl K (fillH Xs N Pl K f Q x) ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x _ _ _ _ D hs scope nO hO l₁ hw₂
    k u₁ u₂ y ds (hv_door ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ hs scope hK hp hw hF hS hS' hc hn hf hw₂ u₁ hl _)

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.hv_door
#print axioms AtPublicFiles.KeyLastChain.hdot_door
