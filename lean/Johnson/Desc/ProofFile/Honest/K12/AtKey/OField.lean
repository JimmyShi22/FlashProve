-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OField.lean: the letter that says which columns the field holds, at the filled
key thread: the five sentences at member 10 at that letter, with no premise on the field; and the letter's carrying.

  `field_of_letter`       at a stand at 10 the letter gives the field the columns that the fold read
  `members_of_thread`     the thread has twelve members
  `five_at_ten_letter`    the five at the letter
  `saidNext_at_member`    the letter is carried over a member, from the new trees there
  `saidNext_at_key`       the letter is carried over every member

Limits.
- NOT IN FRONT OF A LAW OVER COINS: `field_of_letter`, `five_at_ten_letter`, `saidNext_at_member`, `saidNext_at_key` bear this label; the rule is at its home, the
  head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Their ground: the thread's pair is a premise.
- `saidNext_at_key` takes the four sentences at every member and the no-stop at the members with new trees as premises.
- The clause on the field is true and empty at a state where no set of tables has `Thread.Hand`.
- The premises of `five_at_ten_letter` are paid as in OStep.lean's head; `TR` is told there too.
- That a stand at 10 is reached is not said.
- Nothing on completeness of the whole chain, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OStep
import Johnson.Desc.ProofFile.Honest.Thread.SaidField
import E2E.KeyOpensAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Grows)
open VerifiableInference.Desc.K1 (SmpStay)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source)
open Desc.K14 (St)
open Desc.K14.Honest (Eight)
open ProofFile.Honest
open ProofFile.Honest.K14 (Plan2 WitLens)
open AtPublicFiles.KeySharedThread (parKey randKey sentKey)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyTreesKey (tbKey)
open AtPublicFiles.AtFiles (flat₂)
open AtPublicFiles.AtFiles.Full (QK PF omega_full)
open AtPublicFiles.HalvesAreJobs (pU pO)
open AtPublicFiles.KeyLay (withTestsOnUAndOmega)
open AtPublicFiles.TableFilled (TR ttF depths_real opens_filled)

section
variable (K₀ : KeyPub) (hK₀ : fullPub = some K₀) {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₁ : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)
  (B : Eight (parKey Xs PF)) (own₀ : X₀)

/-- **At a stand at 10 the letter gives the field the columns that the fold read.** -/
theorem field_of_letter :
    ∀ k s m E, ThrS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀)
        (SaidField (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) BaseNil) 10 k s m E →
      ∀ cols, (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).colsTo 10 m E = .ok cols →
      m.opened = some cols := by
  intro k s m E u cols hc
  obtain ⟨base, cols', hB, hc', ho⟩ := opened_of_saidField _ u.1 u.2
  obtain rfl : base = [] := hB
  rw [hc] at hc'
  obtain rfl : cols = cols' := Except.ok.inj hc'
  exact ho

/-- **The five sentences at member 10, at the letter.** -/
theorem five_at_ten_letter (e : parKey Xs PF = QK) {layO : OnBytes.TreeLay} (hK₀ : fullPub = some K₀)
    (hQ : Plan2 (parKey Xs PF) (sentKey Xs PF) layO) (hs : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hsp : K₁.lin.S.sharedSplitNeeded = true)
    (hKp : ∀ s s', Kp 10 s s' ↔ Grows s.st s'.st ∧ SmpStay s.st s'.st)
    (fall : ℕ → St → List Fmt.Drawn → Option String) :
    PlaysS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀)
        (SaidField (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) BaseNil) 10 ∧
      BehindS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀)
        (SaidField (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) BaseNil) 10 ∧
      ExchangeS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀)
        (SaidField (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) BaseNil) 10 ∧
      RidesPastS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀)
        (SaidField (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) BaseNil) 10 ∧
      AcceptedS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀)
        (SaidField (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) BaseNil) fall 10 :=
  five_at_ten_key K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ _ e hQ hs hsp
    (field_of_letter K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) hKp fall

/-- **The thread has twelve members.** -/
theorem members_of_thread :
    (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).bs.length = 12 := by
  have hO := AtPublicFiles.KeySharedQuiet.over_key Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd w
  have hp : (H2K.JointK.keySharedPre Xs.chains PF ++ [H2K.JointK.keyGu PF]).length = 10 := by
    unfold H2K.JointK.keySharedPre
    rw [List.length_append, List.length_cons, List.length_map, AtPublicFiles.AtFiles.Full.blocksOr_eight B]
    rfl
  have hc : flat₂ Xs.chains PF = (H2K.JointK.keySharedPre Xs.chains PF ++ [H2K.JointK.keyGu PF]) ++
      H2K.JointK.keyOmega (PF.O.getD PF.U) :: [H2K.JointK.keySharedEnd Xs.chains PF] :=
    H2K.JointK.keyShared_cut_omega _ _ _ omega_full
  rw [hO.bs]
  show (flat₂ Xs.chains PF).length = 12
  rw [hc, List.length_append, hp]
  rfl

include hK₀ in
/-- **The letter is carried over a member**, from the new trees there. -/
theorem saidNext_at_member (e : parKey Xs PF = QK)
    (hp : (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr PF).planOk = true) {b : ℕ} (hb : b < 12)
    (hT : TreesNext (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀)
      (SaidField (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) BaseNil) b) :
    SaidNext (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀)
      (SaidField (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) BaseNil) b :=
  saidNext_field _ (n := 12)
    (AtPublicFiles.KeySharedQuiet.fits_key Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
      (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd w hp)
    (Nat.le_of_lt hb) hT (baseNil_kept _ b)
    (opens_filled K₀ Xs Nr K₁ ℓ Nm Mg₀ K₁.weights (randKey K₁) tk rest Kp Vd w B own₀ e (by omega))
    (fun k m => depths_real K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ e (by omega) k m)

include hK₀ in
/-- **The letter is carried over every member**, from the four sentences at every member and the no-stop at
the members with new trees. -/
theorem saidNext_at_key (e : parKey Xs PF = QK)
    (hp : (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr PF).planOk = true)
    (o : OwesS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀)
      (SaidField (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) BaseNil))
    (hst : ∀ b, b < (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).bs.length →
      (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).fresh b ≠ [] →
      ∀ blk, (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).bs[b]? = some blk →
      ∀ (m : Mid (Common W₀ Rc TableKey) X₀) (ds : List Fmt.Drawn),
        chainStopAt ((TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).φ.sees m.st.input) [blk]
          (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).hs m.loc ds = none) :
    ∀ b, SaidNext (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀)
      (SaidField (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) BaseNil) b := by
  have hl := members_of_thread K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀
  have hfit : (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).fits
      (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).bs.length = true := by
    rw [hl]
    exact AtPublicFiles.KeySharedQuiet.fits_key Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
      (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd w hp
  refine saidNext_field_of_owes _ hfit o hst (fun b _ => baseNil_kept _ b) (fun b hb => ?_)
    (fun b hb k m => ?_)
  · rw [hl] at hb
    exact opens_filled K₀ Xs Nr K₁ ℓ Nm Mg₀ K₁.weights (randKey K₁) tk rest Kp Vd w B own₀ e
      (by omega)
  · rw [hl] at hb
    exact depths_real K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ e (by omega) k m

end

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.field_of_letter
#print axioms ProofFile.Honest.K12.AtKey.five_at_ten_letter
#print axioms ProofFile.Honest.K12.AtKey.members_of_thread
#print axioms ProofFile.Honest.K12.AtKey.saidNext_at_member
#print axioms ProofFile.Honest.K12.AtKey.saidNext_at_key
