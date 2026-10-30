-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- placedB | placed_of_B stand in a light file of their own, Johnson/RunOne/KeyPlacedB.lean, which this file imports, and promise_at₁S is a call of KeyFillMeet.lean's promise_atG.
/-
Johnson/RunOne/KeyFillOn.lean: A BORDER's WHOLE PROMISE On₁ k, AT THE KEY FILE's OWN LETTERS AND THE WOVEN TABLES' READING, FROM TESTS ON THE STATE, ONE LAW's FACT AND THE STORED TABLE's SIDE. Every law of the key file's tables is guarded by On₁ k a: on₁ (Johnson/RunOne/KeyRows1At.lean).
  promise_at₁S · member_of_recordS   KeyFillMeet.lean's promise_at₁ | KeyFillRecord.lean's member_of_record WITH «every leaf is shown» BESIDE
  (placedB · placed_of_B: Placed (Johnson/Desc/Key/KeyTies.lean) as a plain test: in Johnson/RunOne/KeyPlacedB.lean)
  shownK                  Sound.ShownAt at a member gives the tables' own, where the seat fits
  on₁_of_tests            k ≤ 17: FOR EVERY RECORD a: the premises below ⟹ ∃ y', y'.1 = y₀.1 ∧ On₁ X N P D B atSix R coll k (a, y'); B := baseK csKey six numSix atSix decT recOf (plan₁ (oneAt X)).orc · R := kreadFam …
THE PREMISES: T1 shape₁ … k a.2 = true (a Bool on the state) · T2 Placed … (placedB) · T3 OnBytes.Means.InOrder a.2.d.st (inOrderB | inOrder_of_B: KeyFenceB.lean | KeyFenceOrder.lean) · T4 a.1.key.fits … = true · T5 2 ≤ k ≤ 15 → MaskWith … 1 2 (maskWithB | maskWith_of_B: Johnson/Desc/Key/KeyPubIn.lean | KeyFenceOrder.lean)
  · L1 at every open pin the state's statement holds the sending kind's row (SeedIs): NO BOOL (a row has no decidable equality): seedIs_behind (Johnson/Desc/K1/Law/SeedIs.lean) at a yes of the sending's decision, and SeedIs.travels · L2 THE STORED TABLE's SIDE: recOf a.1 = some r, and no collision at r whatever the trees hold
  · six closed tests on public data (KeyFillMeet.lean's n0 n1 n2 f0 f1 f2).
NO STATE IS SHOWN HERE TO MEET T1 … L2 TOGETHER: UNTIL ONE IS, THIS THEOREM MAY ITSELF BE TRUE AND EMPTY. THE ORACLES y' ARE BUILT: code words of messages chosen to fit the state's answers: not a run's own. k ≥ 18 wants EvalIs (no Bool): left out.
OBJECT: on₁ | On₁ | free₁ · USER: imported by Johnson/Top/Fire/Code/KeyFillStep.lean, Johnson/RunOne/KeyFillChains.lean · LETTERS: X N P D · a · decT · recOf · tab · coll.
Nothing on soundness.
-/
import Johnson.RunOne.KeyFillRecord
import Johnson.RunOne.KeyFenceOrder
import Johnson.RunOne.KeyPlacedB

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyRows23
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.Key (Xi FirstState)
open VerifiableInference.Desc.K1 (SeedIs Tie)
open Johnson.RunOne.KeyRows1 (plan₁ readers₁ book₁ n₁ slots₁ ties₁ tiesA open₁ on₁ free₁ meaning₁At)
open Cb Johnson.Pack OnBytes.Maker OnBytes.Slice

section
variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) (num : Fin l.length → ℕ) (at_ : Where)
  {Cells Rec : Type} (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec) (orc₁ : ℕ → Option ℕ)

/-- KeyFillMeet.lean's promise_at₁, WITH «every leaf is shown» BESIDE (its proof holds it; its statement did not say it). -/
theorem promise_at₁S {XI : Type} (F : FileDescription XI) (I : Fin l.length → Prop) (Fr : Sound.Frame) (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (hnum : Function.Injective num)
    (hS : ∀ i, I i → FitsAt cs l (seatAt l num at_) F i) (hFr : ∀ i, I i → HoldsAt cs l (seatAt l num at_) Fr i) (hT : ∀ i, I i → Tie cs (l.get i).1)
    (hB : ∀ i, I i → meetsB cs (l.get i).1 (l.get i).2 = true) (y₀ : Fr.E.Str) (a : Xi × FirstState) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg)
    (r₀ : ∀ i : Fin l.length, (OmAt cs l i).Rnd) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D)
    (hsend : ∀ i, Sendable cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i))
    (hs : ∀ i, I i → seedIsS cs l num (rowIsK cs l) (src₁ orc₁) i a (ρ i) ((OmAt cs l i).Z.val (ρ i) (m₀ i))) (c₀ : Cells) :
    ∃ (W : Wit Cells Unit Fill.Tab) (y' : Fr.E.Str), y'.1 = y₀.1 ∧ ∀ i : Fin l.length, I i →
      Sound.ShownAt F cs l (seatAt l num at_) (Sound.strsOf Fr y') i ∧
      PIN F (baseK cs l num at_ decT recOf orc₁).h₁ (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') W ∧
      hasSmp (baseK cs l num at_ decT recOf orc₁).h₁ (at_ (num i)).1 (at_ (num i)).2 a = true ∧
      NoColl F (baseK cs l num at_ decT recOf orc₁).h₁ (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') := by
  rw [h₁_eq]
  exact promise_atG cs l num at_ decT (fun a : Xi × FirstState => recOf a.1) (src₁ orc₁) F I Fr hinj hap hnum hS hFr hT hB y₀ a m₀ r₀ ρ hsend hs c₀


/-- KeyFillRecord.lean's member_of_record, with «every leaf is shown» beside. -/
theorem member_of_recordS {XI : Type} (F : FileDescription XI) (I : Fin l.length → Prop) (Fr : Sound.Frame) (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (hnum : Function.Injective num)
    (hS : ∀ i, I i → FitsAt cs l (seatAt l num at_) F i) (hFr : ∀ i, I i → HoldsAt cs l (seatAt l num at_) Fr i) (hT : ∀ i, I i → Tie cs (l.get i).1)
    (hB : ∀ i, I i → meetsB cs (l.get i).1 (l.get i).2 = true) (hE : ∀ i, I i → CaseE (l.get i).1) (hP : ∀ i, I i → hasPadB cs (l.get i).1 = true)
    (y₀ : Fr.E.Str) (a : Xi × FirstState) (hrec : ∀ i, I i → ∃ o ρ y, orc₁ (num i) = some o ∧ SeedIs cs (l.get i).1 a.2.d.st o ρ y) (c₀ : Cells) :
    ∃ (W : Wit Cells Unit Fill.Tab) (y' : Fr.E.Str), y'.1 = y₀.1 ∧ ∀ i : Fin l.length, I i →
      Sound.ShownAt F cs l (seatAt l num at_) (Sound.strsOf Fr y') i ∧
      PIN F (baseK cs l num at_ decT recOf orc₁).h₁ (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') W ∧
      hasSmp (baseK cs l num at_ decT recOf orc₁).h₁ (at_ (num i)).1 (at_ (num i)).2 a = true ∧
      NoColl F (baseK cs l num at_ decT recOf orc₁).h₁ (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') := by
  classical
  have key : ∀ i : Fin l.length, ∃ (ρ : (OmAt cs l i).Z.D) (m₀ : (OmAt cs l i).Msg), Sendable cs (l.get i).1 (l.get i).2 (m₀, fun _ => 0) ∧
      (I i → seedIsS cs l num (rowIsK cs l) (src₁ orc₁) i a ρ ((OmAt cs l i).Z.val ρ m₀)) := by
    intro i
    by_cases hi : I i
    · obtain ⟨o, ρ, y, ho, hy⟩ := hrec i hi
      obtain ⟨j₀, h₀⟩ := pad_of_B cs _ (hP i hi)
      obtain ⟨m₀, hs, hv⟩ := exists_msg_of_answer cs (l.get i).1 (l.get i).2 (hE i hi) j₀ h₀ ρ y
      exact ⟨ρ, m₀, hs, fun _ => (seedIsS_iff₁ cs l num orc₁ i a ρ _).2 ⟨o, ho, y, hy, hv⟩⟩
    · exact ⟨Classical.arbitrary _, fun _ => 0, sendable_zero cs _ _, fun h => absurd h hi⟩
  choose ρ m₀ hsend hs using key
  exact promise_at₁S cs l num at_ decT recOf orc₁ F I Fr hinj hap hnum hS hFr hT hB y₀ a m₀ (fun _ _ => 0) ρ hsend hs c₀

/-- Sound.ShownAt at a member gives the tables' own at its number, where the seat fits. -/
theorem shownK {XI : Type} (F : FileDescription XI) (i : Fin l.length) (hS : FitsAt cs l (seatAt l num at_) F i) (y : Strs) (h : Sound.ShownAt F cs l (seatAt l num at_) y i) :
    Key.ShownAt F at_ (num i) y := by
  obtain ⟨o, _, ho, _, hlog, _⟩ := hS
  intro o' ho' x hx
  obtain rfl : o' = o := Option.some.inj (ho'.symm.trans ho)
  exact h x (by rw [← hlog]; exact hx)

end

/-! ## The border's whole promise -/

section
open OnBytes.Params VerifiableInference.Desc.Sound
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (D : WholeD)
  {Cells Rec : Type} [Inhabited Cells] (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec) (tab : Cells → ℕ → ℕ → OnBytes.F) (coll : Strs → Rec → Prop)

/-- **A BORDER's WHOLE PROMISE, FROM TESTS ON THE STATE, ONE LAW's FACT AND THE STORED TABLE's SIDE.** -/
theorem on₁_of_tests (k : ℕ) (hk : k ≤ 17) (t0 t1 t2 : String)
    (n0 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t0 Johnson.Top.H.shIdx 0 0 = none)
    (n1 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t1 Johnson.Top.H.shMul 1 0 = none)
    (n2 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t2 Johnson.Top.H.shW 5 0 = none)
    (f0 : holdsB (fr₁ D) 0 (aOf Johnson.Top.H.csKey Johnson.Top.H.shIdx) = true)
    (f1 : holdsB (fr₁ D) 1 (aOf Johnson.Top.H.csKey Johnson.Top.H.shMul) = true)
    (f2 : holdsB (fr₁ D) 5 (aOf Johnson.Top.H.csKey Johnson.Top.H.shW) = true)
    (y₀ : (fr₁ D).E.Str) (a : Xi × FirstState)
    (T1 : shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) (n₁ (oneAt X)) (slots₁ (oneAt X)) k a.2 = true)
    (T2 : Placed (plan₁ (oneAt X)).orc (fun o => a.2.d.book.place[o]?) id atSix (pinned (open₁ 2 k)))
    (T3 : OnBytes.Means.InOrder a.2.d.st)
    (T4 : a.1.key.fits (oneAt X).lin.fold.index = true)
    (T5 : 2 ≤ k ∧ k ≤ 15 → MaskWith (fun o => a.2.d.book.place[o]?) 1 2)
    (L1 : ∀ i : Fin six.length, numSix i ∈ pinned (open₁ 2 k) → ∃ o ρ y, (plan₁ (oneAt X)).orc (numSix i) = some o ∧ SeedIs Johnson.Top.H.csKey (six.get i).1 a.2.d.st o ρ y)
    (r : Rec) (L2 : recOf a.1 = some r) (L2' : ∀ y' : (fr₁ D).E.Str, y'.1 = y₀.1 → ¬ coll (strsOf (fr₁ D) y') r) :
    ∃ y' : (fr₁ D).E.Str, y'.1 = y₀.1 ∧
      On₁ X N P D (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (plan₁ (oneAt X)).orc) atSix (kreadFam Johnson.Top.H.csKey six numSix atSix tab) coll k (a, y') := by
  have hn : n₁ (oneAt X) = 2 := by
    have ht : ties₁ (oneAt X) k a.2 = true := ((shape₁_iff _ _ _ _ _ _ _).1 T1).1
    unfold ties₁ tiesA at ht
    simp only [Bool.and_eq_true] at ht
    exact beq_iff_eq.1 ht.1.1.1.1.1.1
  have hI : ∀ i : Fin six.length, numSix i ∈ pinned (open₁ 2 k) → numSix i < 3 := fun i hi => open₁_le k _ hi
  have hFit : ∀ i : Fin six.length, numSix i ∈ pinned (open₁ 2 k) → FitsAt Johnson.Top.H.csKey six (seatAt six numSix atSix) (Fk X N P) i := by
    intro i hi
    obtain ⟨q, hq⟩ := i
    have h3 : q < 3 := hI _ hi
    interval_cases q
    · exact fitsAt_of_noFault _ six _ _ _ t0 n0
    · exact fitsAt_of_noFault _ six _ _ _ t1 n1
    · exact fitsAt_of_noFault _ six _ _ _ t2 n2
  have hHold : ∀ i : Fin six.length, numSix i ∈ pinned (open₁ 2 k) → HoldsAt Johnson.Top.H.csKey six (seatAt six numSix atSix) (fr₁ D) i := by
    intro i hi
    obtain ⟨q, hq⟩ := i
    have h3 : q < 3 := hI _ hi
    interval_cases q
    · exact holdsAt_of_B _ six _ _ _ f0
    · exact holdsAt_of_B _ six _ _ _ f1
    · exact holdsAt_of_B _ six _ _ _ f2
  obtain ⟨W, y', hy, h⟩ := member_of_recordS Johnson.Top.H.csKey six numSix atSix decT recOf (plan₁ (oneAt X)).orc (Fk X N P) (fun i => numSix i ∈ pinned (open₁ 2 k)) (fr₁ D)
    seat_inj_six shapesApart_six (fun a b h => Fin.ext h) hFit hHold (fun i _ => tie_six i) (fun i _ => List.all_eq_true.1 meets_six _ (List.get_mem six i))
    (fun i _ => of_decide_eq_true (List.all_eq_true.1 caseE_six _ (List.get_mem six i))) (fun i _ => List.all_eq_true.1 hasPad_six _ (List.get_mem six i)) y₀ a L1 default
  have at' : ∀ q ∈ pinned (open₁ 2 k), ∃ i : Fin six.length, numSix i = q := fun q hq =>
    ⟨⟨q, Nat.lt_of_lt_of_le (open₁_le k q hq) (by decide)⟩, rfl⟩
  refine ⟨y', hy, Or.inr ⟨T1, ?_, ?_, ?_⟩⟩
  · rw [hn]
    refine List.all_eq_true.2 fun q hq => ?_
    obtain ⟨i, rfl⟩ := at' q hq
    exact (h i hq).2.2.1
  · refine ⟨⟨r, L2, L2' y' hy⟩, ⟨arrOk_six₁ _ decT recOf _, readsPinned_h₁ _ six numSix atSix _ decT recOf _ _ rfl _⟩, T2, fun h18 => absurd h18 (by omega), fun j _ o _ => sampleIn_of_order T3 o,
      fun h18 => absurd h18 (by omega), T3, fun q hq => ?_, T4, T5, fun h18 => absurd h18 (by omega)⟩
    obtain ⟨i, rfl⟩ := at' q hq
    exact shownK _ six numSix atSix (Fk X N P) i (hFit i hq) _ (h i hq).1
  · rw [hn]
    intro q hq
    obtain ⟨i, rfl⟩ := at' q hq
    exact (h i hq).2.2.2

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.promise_at₁S
#print axioms Johnson.RunOne.KeyRows23.member_of_recordS
#print axioms Johnson.RunOne.KeyRows23.shownK
#print axioms Johnson.RunOne.KeyRows23.on₁_of_tests
