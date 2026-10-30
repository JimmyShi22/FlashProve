-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OSays.lean: `SaysAt` at the test on G_omega of the filled key thread, at a
stand at 10, at every coin lent; and with it `AcceptedS` at member 10, where the field holds the columns that the
fold read.

  `says_at_ten_key`      the statement
  `accepted_at_ten_key`  `AcceptedS`: of the premises on the letters, the field alone stays

Limits.
- NOT IN FRONT OF A LAW OVER COINS: `says_at_ten_key`, `accepted_at_ten_key` bear this label; the rule is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean.
  Their ground: the thread from Thr as a premise.
- The field is a premise: which letter gives it is not said here.
- That a stand at 10 is reached is not said.
- Nothing on completeness of the whole chain, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open OnBytes (TableKey)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source)
open Desc.K14 (St)
open Desc.K14.Honest (Eight)
open ProofFile.Honest
open ProofFile.Honest.K14
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light (SaysAt colsOpened sentOf)
open ProofFile.Honest.K12.Light.ItemLaws (openKinds_of_thr)
open AtPublicFiles.KeySharedThread (parKey randKey sentKey)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyTreesKey (tbKey)
open AtPublicFiles.AtFiles.Full (QK PF)
open AtPublicFiles.HalvesAreJobs (pU pO JO)
open AtPublicFiles.KeyLay (withTestsOnUAndOmega)
open AtPublicFiles.KeyNineClosed (place_full)
open AtPublicFiles.TableFilled (TR ttF)

section
variable (K₀ : KeyPub) (hK₀ : fullPub = some K₀) {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₁ : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)
  (B : Eight (parKey Xs PF)) (own₀ : X₀)

include hK₀ in
/-- **`SaysAt` at a stand, at every coin lent**, where the field holds the columns that the fold read. -/
theorem says_at_ten_key (e : parKey Xs PF = QK) {layO : OnBytes.TreeLay}
    (hQ : Plan2 (parKey Xs PF) (sentKey Xs PF) layO) {k : Coins (keyBook K₀)} {s : St}
    {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) 10 k s m E)
    (hfield : ∀ cols, (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).colsTo 10 m E = .ok cols →
      m.opened = some cols)
    (c : RowCoins [(firstPart (JO Xs K₁ B) : Part Empty _ _), restPart (JO Xs K₁ B)])
    (hc : lendRow (keyBook K₀) ((keyBook K₀).rowsOf 1) (k.look 1) (JO Xs K₁ B).p.place
      [(firstPart (JO Xs K₁ B) : Part Empty _ _), restPart (JO Xs K₁ B)] 0 = .ok c) :
    SaysAt (manyAtTen Xs K₁ B (X₀ := X₀)) m.st.input (frontOf m) (restCoins (JO Xs K₁ B) c.2.1) := by
  have hen := enters_at_ten_key Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd w B u hfield
  have hrec := Except.ok.inj hen
  have hst : ((manyAtTen Xs K₁ B (X₀ := X₀)).rec₀ m.st.input (frontOf m)).st = s.st :=
    (congrArg (·.st) hrec).symm
  have hg : ((manyAtTen Xs K₁ B (X₀ := X₀)).rec₀ m.st.input (frontOf m)).g = s.loc.gOmega :=
    (congrArg (·.g) hrec).symm
  have hsh : ProofFile.Honest.Sh.testSh ((manyAtTen Xs K₁ B (X₀ := X₀)).rec₀ m.st.input (frontOf m)) =
      ProofFile.Honest.K12.Light.KeyDoorUClosed.shapeOm :=
    accepted_shape_written (W := Common W₀ Rc TableKey) (X := X₀) e place_full
      [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] (by rw [B.made]) (fun v => v.key)
      colsOpened m.st.input (frontOf m)
  have hI : OnBytes.Means.InOrder s.st := u.2.2.1.2
  have hK : OnBytes.Means.OpenKinds s.st := openKinds_of_thr Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd w u
  have hs := omega_items_at_ten Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd w u []
  exact saysAt_of_omega_items _ _ _ _ s _ hst hg hI hK hs hsh
    (words_tied_at_ten K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ e hQ u [] c.2.1
      (lendRow_second hc))

include hK₀ in
/-- **It is accepted, at member 10**, where the field holds the columns that the fold read. -/
theorem accepted_at_ten_key (e : parKey Xs PF = QK) {layO : OnBytes.TreeLay}
    (hQ : Plan2 (parKey Xs PF) (sentKey Xs PF) layO) (hs : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hsp : K₁.lin.S.sharedSplitNeeded = true)
    (Said : ℕ → Coins (keyBook K₀) → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (hfield : ∀ k s m E, ThrS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 10 k s m E →
      ∀ cols, (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).colsTo 10 m E = .ok cols →
      m.opened = some cols)
    (fall : ℕ → St → List Fmt.Drawn → Option String) :
    AcceptedS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said fall 10 :=
  acceptedS_at_ten_key K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ e hs hsp Said hfield fall
    fun _ _ _ _ c u hc => says_at_ten_key K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ e hQ u.1
      (hfield _ _ _ _ u) c hc

end

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.says_at_ten_key
#print axioms ProofFile.Honest.K12.AtKey.accepted_at_ten_key
