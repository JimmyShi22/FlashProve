-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyDoorTies.lean: three premises of the door at the key (`door_behind_key`, E2E/KeyLastDoor.lean) at the last thread `T₃K`:
`hst`, the stored tables; `hv`, the input; `htrees`, the trees taken over.

Why. The door hands the last thread what the two earlier threads hold. The stored table and the input are one by the threads'
letters; a tree taken over is the sender's, by `taken_trees` (E2E/KeyLastTrees.lean).

Main names.
  `second_rounds`, `taken_key`: the trees taken over are the own test's.
  `shared_trees`: the count that `htrees_key` asks of the shared chain.
  `hst_key`, `hv_key`, `htrees_key`.

What stays open. `hL`: the filling's stored table is the prover's. In `htrees_key`: `hT`, the last thread's tables are `tableLast`;
`ht`, its trees taken over are the written ones; `c₁`, `c₂`: the two earlier chains send enough trees.

No law over coins: each is a sentence at a stand. Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyLastDoor
import E2E.KeyLastTrees
import E2E.KeyLastTaken
import E2E.KeyTreeOwners
import Johnson.Desc.ProofFile.Honest.Thread.ScriptLots

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
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces descriptionFromSource ownTest)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeySharedThread (threadKey)
open AtPublicFiles.KeyThread (KeyFill laid₁ lengths takenIn decl₁ decl₂)
open AtPublicFiles.KeyDoorItems (commonOf)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (PF)

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
  (table : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
  (n₁ n₂ : Nat) (Vd : Local W₀ Rc Xi Unit → Prop) (Rd : Nat → Local W₀ Rc Xi Unit → S₃ → Prop)
  (Kp : Place → S₃ → S₃ → Prop) (w : Local W₀ Rc Xi Unit)

/-- The last chain's rounds are the own test's: the other members have none. -/
theorem second_rounds :
    (descriptionFromSource Xs Nr Pl).second.blocksInOrder.flatMap (·.rounds) = (ownTest Pl).rounds := by
  show (ownTest Pl).rounds ++ ([] ++ []) = _
  simp

/-- **The trees that the last chain takes over, at the description.** -/
theorem taken_key (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) :
    takenIn (AtPublicFiles.KeyThread.decl₃ (descriptionFromSource Xs Nr Pl)) = takenIn (ownTest PF).rounds := by
  obtain rfl := AtPublicFiles.AtFiles.Full.later_sourced hs scope
  exact congrArg takenIn (second_rounds Xs Nr PF)

/-- **The shared chain sends more than one tree.** -/
theorem shared_trees (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) :
    1 < treesTo (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).bs (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length := by
  have hl := (lengths scope hs.named).2.1
  have e := AtPublicFiles.AtFiles.Full.par_sourced hs scope
  obtain rfl := AtPublicFiles.AtFiles.Full.later_sourced hs scope
  obtain ⟨layO, hQ⟩ := AtPublicFiles.KeySharedThread.plan_key hs scope
  obtain ⟨B⟩ := hQ.eight
  have n := (AtPublicFiles.KeyTblTrial.chain_counts Xs Nr K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ e B).2.2
  have m := ProofFile.Honest.FirstThread.treesTo_mono (threadKey Xs Nr PF K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).bs (show 11 ≤ 12 by omega)
  rw [hl]
  rw [n] at m
  exact lt_of_lt_of_le (by decide) m

/-- **The stored tables are one.** -/
theorem hst_key (hL : L.stored = (keyProver K).storedWords) (R : Ready W₀ Rc Xi TableKey Unit X₀ X)
    (hown : R.own = ⟨w₀, rc, x, ()⟩) :
    ∀ v, (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁).valid v → ∀ i p,
      (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁).stored v i p =
        (T₃K Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML table n₁ n₂ Vd Rd
          Kp w).stored R.own i p := by
  rintro v ⟨rfl, -⟩ i p
  show L.stored w₀ rc i p = (keyProver K).storedWords R.own.w₀ R.own.rc i p
  rw [hown, hL]

/-- **The last thread's input is valid.** -/
theorem hv_key (R : Ready W₀ Rc Xi TableKey Unit X₀ X) (hw : R.own = w) (hVd : Vd w) :
    (T₃K Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML table n₁ n₂ Vd Rd
      Kp w).valid R.own :=
  ⟨hw, hw ▸ hVd⟩

/-- **The trees taken over are at hand at the door.** -/
theorem htrees_key (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (own : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
    (hT : table = tableLast (descriptionFromSource Xs Nr Pl) commonOf tb₁ tb₂ own)
    (htb₁ : (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁).table = tb₁)
    (htb₂ : (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).table = tb₂)
    (ht : (T₃K Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML table n₁ n₂ Vd Rd
      Kp w).taken = takenIn (ownTest PF).rounds)
    (c₁ : 5 < treesTo (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁).bs (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length)
    (c₂ : 1 < treesTo (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).bs
      (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length)
    (hw₂ : w₂ = commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit)) (k : Coins Bk)
    (R : Ready W₀ Rc Xi TableKey Unit X₀ X) (hown : R.own = ⟨w₀, rc, x, ()⟩) :
    ∀ e₁ m₁ E₁ e₂ m₂ E₂ o₁ o₂,
      ThrS (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂ (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length k e₂ m₂
        E₂ →
      (T₃K Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML table n₁ n₂ Vd Rd
        Kp w).Trees
        (T₃K Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML table n₁ n₂ Vd Rd
          Kp w).taken k { R.start₃ (keyProver K) m₁ m₂ with opened := some (o₁ ++ o₂) } (envThird E₁ E₂) := by
  intro e₁ m₁ E₁ e₂ m₂ E₂ o₁ o₂ u₁ u₂
  have hl := lengths scope hs.named
  have i₁ : m₁.st.input = ⟨w₀, rc, x, ()⟩ := by
    have v := u₁
    rw [hl.1] at v
    exact v.1.2.2.2.2.2.2.1
  have i₂ : m₂.st.input = commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit) := by
    have v := u₂
    rw [hl.2.1] at v
    exact (v.1.2.2.2.2.2.2.1).trans hw₂
  have l₁ : m₁.st.heard.length = (decl₁ (descriptionFromSource Xs Nr Pl)).length := by
    have f : drawsFit (declsTo (descriptionFromSource Xs Nr Pl).first.blocksInOrder (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length) m₁.st.heard = true :=
      u₁.1.2.1
    have e := drawsFit_length _ _ f
    rw [e]
    unfold declsTo
    rw [List.take_length]
  exact taken_trees (F := descriptionFromSource Xs Nr Pl) commonOf (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁)
    (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂)
    (T₃K Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML table n₁ n₂ Vd Rd Kp w) own
    (by
      show table = _
      rw [htb₁, htb₂]
      exact hT)
    (fun _ => rfl) (fun _ => rfl) rfl
    (hmem_key _ _ _ ht c₁ c₂) _ u₁.1 u₂.1 (by rw [i₁]; exact hown) (by rw [i₂]; exact congrArg commonOf hown.symm) rfl l₁

end

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.taken_key
#print axioms AtPublicFiles.KeyLastChain.shared_trees
#print axioms AtPublicFiles.KeyLastChain.hst_key
#print axioms AtPublicFiles.KeyLastChain.hv_key
#print axioms AtPublicFiles.KeyLastChain.htrees_key
