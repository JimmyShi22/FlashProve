-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyDoorWhole.lean: `DoorBehindS` at the last thread `threadOwn` and its letter `saidOwn`, with the three ties paid.

Why. `door_behind_key` (E2E/KeyLastDoor.lean) and `door_own` (E2E/KeyLastDoorOwn.lean) leave `hst`, `htrees`, `hv`, `hr` as premises;
E2E/KeyDoorTies.lean pays the first three from the threads' letters, and `hr` is nothing at `threadOwn`.

Main names. `door_whole`. `door_of_asks`: the same from what each earlier chain brings to the door (`DoorAsks`). `door_at_Th`: at the
first chain's thread `Th`.

What stays open. `a₁`, `a₂`: one stand at each last border. `o₁`, `o₂`: one state there. `hfit`: the key fits. `hdot`: the item (Dot).
`L₁`, `L₂`: the field clauses. `hL`: the filling's stored table is the prover's. `c₁`: the first chain's count of trees. `hVd`.

No law over coins. Nothing on soundness, completeness, hiding or binding: a conditional.

-/
import E2E.KeyDoorTies
import E2E.KeyLastDoorOwn
import E2E.LotFieldFirstLaw
import E2E.FirstHPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyLastChain
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Place Wit OpenedColumn FileDescription)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Last (MeaningL)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces descriptionFromSource)
open VerifiableInference.Desc.Own (keyFits)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeySharedThread (threadKey)
open AtPublicFiles.KeyThread (KeyFill laid₁)
open AtPublicFiles.KeyDoorItems (commonOf wit₃)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (QK)
open AtPublicFiles.KeyThread (lengths)
open AtPublicFiles.LotField (DoorAsks)
open AtPublicFiles.FirstH (Th Fl fillH tbH LaterFill HCells HTab)

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk Cells M Smp Rec P₂ Wt₂ : Type} {Z : VerifierAndGoals.PublicFiles}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (L : KeyFill Bk W₀ Rc Cells M Smp Rec)
  (ℓ₂ : WitLens Wt₂) (Nm : NumbersS)
  (Mg₂ : Common W₀ Rc TableKey → MeaningS St P₂ Wt₂)
  (tb₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest₂ : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt₂)
  (Kp₂ : Nat → St → St → Prop) (Vd₂ : Common W₀ Rc TableKey → Prop)
  (w₂ : Common W₀ Rc TableKey) (w₀ : W₀) (rc : Rc) (x : Xi)
  (hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X))
  (tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
  (Said₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X → Prop)
  (Said₂ : Nat → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
  (d : (Xi × FirstState) × St)
  (Dt : Local W₀ Rc Xi Unit → MeaningS St (Xi × FirstState) (Wit Cells Unit M × Words Cb.Gl.E))
  (ML : MeaningL S₃ (Wit Cells Unit M × Words Cb.Gl.E))
  (n₁ n₂ : Nat) (Vd : Local W₀ Rc Xi Unit → Prop) (w : Local W₀ Rc Xi Unit)
  (dfltT : Place × Table) (dfltM : Mid (Local W₀ Rc Xi Unit) X)

/-- **The door at the last thread, with its three ties paid.** A conditional. -/
theorem door_whole (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (a₁ : OneStand Said₁ (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length)
    (a₂ : OneStand Said₂ (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length)
    (o₁ : OneState (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ 19)
    (o₂ : OneState (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂ 12)
    (hfit : ∀ v, (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).valid v →
      keyFits v.key QK.par.S.fold.index = true)
    (hw₂ : w₂ = commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit)) (k : Coins Bk)
    (R : Ready W₀ Rc Xi TableKey Unit X₀ X) (hown : R.own = ⟨w₀, rc, x, ()⟩) (hw : R.own = w) (hVd : Vd w)
    (hL : L.stored = (keyProver K).storedWords)
    (c₁ : 5 < treesTo (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁).bs (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length)
    (hdot : ∀ (e₁ : FirstState) (m₁ : Mid (Local W₀ Rc Xi Unit) X) (E₁ : Env) (e₂ : St)
        (m₂ : Mid (Common W₀ Rc TableKey) X₀) (E₂ : Env),
        ThrS (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ 19 k e₁ m₁ E₁ →
        ThrS (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂ 12 k e₂ m₂ E₂ →
        ∀ y ds, (Dt ⟨w₀, rc, x, ()⟩).dot (x, e₁) e₂ y
          (wit₃ Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ k ⟨w₀, rc, x, ()⟩
            (m₁.st.heard ++ (m₂.st.heard ++ ds))))
    (L₁ : ∀ e m E, ThrS (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length k e m E →
      (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁).Field [] (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length m E)
    (L₂ : ∀ e m E, ThrS (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂
        (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length k e m E →
      (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).Field [] (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length m E) :
    DoorBehindS (descriptionFromSource Xs Nr Pl) (keyProver K) (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁)
      (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂)
      (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM)
      Said₁ Said₂
      (saidOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM)
      x k R :=
  door_own Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM
    hs scope a₁ a₂ hw₂ k R hown
    (door_behind_key Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML _ n₁ n₂ Vd _ _ w
      hs scope o₁ o₂ hfit hw₂ k R hown hdot
      (hst_key Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML _ n₁ n₂ Vd _ _ w hL R hown)
      (htrees_key Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML _ n₁ n₂ Vd _ _ w hs scope
        _ rfl rfl rfl (taken_key Xs Nr Pl hs scope) c₁
        (shared_trees Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ hs scope) hw₂ k R hown)
      (fun _ _ _ _ _ _ _ _ _ _ => trivial)
      (hv_key Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML _ n₁ n₂ Vd _ _ w R hw hVd)
      L₁ L₂)

/-- **The door, from what the two earlier threads bring to it.** -/
theorem door_of_asks (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (D₁ : DoorAsks (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ 19)
    (D₂ : DoorAsks (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂ 12)
    (hfit : ∀ v, (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).valid v →
      keyFits v.key QK.par.S.fold.index = true)
    (hw₂ : w₂ = commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit)) (k : Coins Bk)
    (R : Ready W₀ Rc Xi TableKey Unit X₀ X) (hown : R.own = ⟨w₀, rc, x, ()⟩) (hw : R.own = w) (hVd : Vd w)
    (hL : L.stored = (keyProver K).storedWords)
    (c₁ : 5 < treesTo (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁).bs (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length)
    (hdot : ∀ (e₁ : FirstState) (m₁ : Mid (Local W₀ Rc Xi Unit) X) (E₁ : Env) (e₂ : St)
        (m₂ : Mid (Common W₀ Rc TableKey) X₀) (E₂ : Env),
        ThrS (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ 19 k e₁ m₁ E₁ →
        ThrS (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂ 12 k e₂ m₂ E₂ →
        ∀ y ds, (Dt ⟨w₀, rc, x, ()⟩).dot (x, e₁) e₂ y
          (wit₃ Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ k ⟨w₀, rc, x, ()⟩
            (m₁.st.heard ++ (m₂.st.heard ++ ds)))) :
    DoorBehindS (descriptionFromSource Xs Nr Pl) (keyProver K) (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁)
      (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂)
      (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM)
      Said₁ Said₂
      (saidOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM)
      x k R := by
  have hl := lengths scope hs.named
  have e₁ : (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length = 19 := hl.1
  have e₂ : (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length = 12 := hl.2.1
  refine door_whole Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT
    dfltM hs scope ?_ ?_ D₁.state D₂.state hfit hw₂ k R hown hw hVd hL c₁ hdot ?_ ?_
  · rw [e₁]
    exact D₁.one
  · rw [e₂]
    exact D₂.one
  · rw [e₁]
    exact D₁.field k
  · rw [e₂]
    exact D₂.field k

end

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk P₂ Wt₂ : Type} {Z : VerifierAndGoals.PublicFiles}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (f : W₀ → Weights) (Q : LaterFill Bk W₀ Rc)
  (ℓ₂ : WitLens Wt₂) (Nm : NumbersS)
  (Mg₂ : Common W₀ Rc TableKey → MeaningS St P₂ Wt₂)
  (tb₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest₂ : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt₂)
  (Kp₂ : Nat → St → St → Prop) (Vd₂ : Common W₀ Rc TableKey → Prop)
  (w₂ : Common W₀ Rc TableKey) (w₀ : W₀) (rc : Rc) (x : Xi)
  (Said₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X → Prop)
  (Said₂ : Nat → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
  (d : (Xi × FirstState) × St)
  (Dt : Local W₀ Rc Xi Unit → MeaningS St (Xi × FirstState) (Wit HCells Unit HTab × Words Cb.Gl.E))
  (ML : MeaningL S₃ (Wit HCells Unit HTab × Words Cb.Gl.E))
  (n₁ n₂ : Nat) (Vd : Local W₀ Rc Xi Unit → Prop) (w : Local W₀ Rc Xi Unit)
  (dfltT : Place × Table) (dfltM : Mid (Local W₀ Rc Xi Unit) X)

/-- **The door at the first chain's thread `Th`.** What is left is what the two chains bring, the key's fit and (Dot). -/
theorem door_at_Th (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (D₁ : DoorAsks (laid₁ Xs Nr Pl (fillH Xs Nr Pl K f Q x) w₀ rc x (keyProver K).first (tbH Xs Nr Pl K f Q)) Said₁ 19)
    (D₂ : DoorAsks (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂ 12)
    (hfit : ∀ v, (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).valid v →
      keyFits v.key QK.par.S.fold.index = true)
    (hw₂ : w₂ = commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit)) (k : Coins Bk)
    (R : Ready W₀ Rc Xi TableKey Unit X₀ X) (hown : R.own = ⟨w₀, rc, x, ()⟩) (hw : R.own = w) (hVd : Vd w)
    (hdot : ∀ (e₁ : FirstState) (m₁ : Mid (Local W₀ Rc Xi Unit) X) (E₁ : Env) (e₂ : St)
        (m₂ : Mid (Common W₀ Rc TableKey) X₀) (E₂ : Env),
        ThrS (laid₁ Xs Nr Pl (fillH Xs Nr Pl K f Q x) w₀ rc x (keyProver K).first (tbH Xs Nr Pl K f Q)) Said₁ 19 k e₁ m₁ E₁ →
        ThrS (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂ 12 k e₂ m₂ E₂ →
        ∀ y ds, (Dt ⟨w₀, rc, x, ()⟩).dot (x, e₁) e₂ y
          (wit₃ Xs Nr Pl K (fillH Xs Nr Pl K f Q x) ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ k ⟨w₀, rc, x, ()⟩
            (m₁.st.heard ++ (m₂.st.heard ++ ds)))) :
    DoorBehindS (descriptionFromSource Xs Nr Pl) (keyProver K)
      (laid₁ Xs Nr Pl (fillH Xs Nr Pl K f Q x) w₀ rc x (keyProver K).first (tbH Xs Nr Pl K f Q))
      (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂)
      (threadOwn Xs Nr Pl K (fillH Xs Nr Pl K f Q x) ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x (keyProver K).first
        (tbH Xs Nr Pl K f Q) Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM)
      Said₁ Said₂
      (saidOwn Xs Nr Pl K (fillH Xs Nr Pl K f Q x) ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x (keyProver K).first
        (tbH Xs Nr Pl K f Q) Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM)
      x k R := by
  have e₁ : (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length = 19 := (lengths scope hs.named).1
  have t : treesTo (descriptionFromSource Xs Nr Pl).first.blocksInOrder 19 = 6 := AtPublicFiles.FirstH.trees_all hs scope
  refine door_of_asks Xs Nr Pl K (fillH Xs Nr Pl K f Q x) ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x (keyProver K).first
    (tbH Xs Nr Pl K f Q) Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM hs scope D₁ D₂ hfit hw₂ k R hown hw hVd rfl ?_ hdot
  show 5 < treesTo (descriptionFromSource Xs Nr Pl).first.blocksInOrder (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length
  rw [e₁, t]
  decide

end

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.door_whole
#print axioms AtPublicFiles.KeyLastChain.door_of_asks
#print axioms AtPublicFiles.KeyLastChain.door_at_Th
