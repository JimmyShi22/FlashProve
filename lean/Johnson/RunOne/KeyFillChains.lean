-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyFillChains.lean: THE FILLING's PROMISE, AND «FOR EVERY STATE THAT HOLDS THE SENDING KIND's ROWS THERE IS A MEMBER», AT THE SHARED AND THE LAST CHAIN's READINGS. Johnson/RunOne/KeyFillMeet.lean's promise_atG is general in the chain's records, its reader of the instance and its source
of the messages' records; Johnson/RunOne/KeyFillOn.lean's promise_at₁S is its call at B.h₁. Here the two other calls, and the turn «given the state, find the messages» in the general form.
  promise_at₂S | promise_at₃S     the calls at B.h₂ | B.h₃, B := baseK
  member_of_recordG               for every record a with the tie seedIsS at I's members: ∃ ONE W, y': ShownAt ∧ PIN ∧ hasSmp ∧ NoColl at I's seats (KeyFillRecord.lean's exists_msg_of_answer called)
  member_of_record₂ | ₃           that at B.h₂ | B.h₃
  seedIsS_iff₂_lo | _hi · seedIsS_iff₃_lo | _border | _own | _none    the tie in the sending kind's own form (SeedIs), branch by branch of the tables' sources
THE PREMISES ON THE PLAN ARE ASKED AT THE MEMBERS OF I ALONE: the seat fits · the frame holds the tree · Tie, the sending kind's (Johnson/Desc/K1/Law/Port2.lean) · meetsB · CaseE · a pad's place.
THE ORACLES y' ARE BUILT: code words of messages chosen to fit the record's answers. NO STATE OF EITHER CHAIN IS SHOWN TO HOLD SUCH ROWS; no seat of the numbers 3 | 4 | 5 is shown to fit at the key file's description.
OBJECT: BaseSt.h₂ | h₃ (Johnson/RunOne/KeyOneReading.lean) and their sources; SeedIs (Johnson/Desc/K1/Law/SeedIs.lean) · USER: on₂_of_tests (Johnson/RunOne/KeyOn2Tests.lean; on a decision in this project); in this library Johnson/RunOne/KeyFillSeed2.lean, Johnson/RunOne/Law/K12Members29.lean and Johnson/RunOne/Law/K12Members32.lean call names of this file too · LETTERS: cs l num at_ decT recOf orc₁ · F Fr I · a. Nothing on soundness.
-/
import Johnson.RunOne.KeyFillOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyRows23
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.Key (Xi FirstState)
open VerifiableInference.Desc.K1 (SeedIs Tie)
open Cb Johnson.Pack OnBytes.Maker OnBytes.Slice

section
variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) (num : Fin l.length → ℕ) (at_ : Where)
  {Cells Rec : Type} (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec) (orc₁ : ℕ → Option ℕ)

/-- **The call at the shared chain's reading.** -/
theorem promise_at₂S {XI : Type} (F : FileDescription XI) (I : Fin l.length → Prop) (Fr : Sound.Frame) (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (hnum : Function.Injective num)
    (hS : ∀ i, I i → FitsAt cs l (seatAt l num at_) F i) (hFr : ∀ i, I i → HoldsAt cs l (seatAt l num at_) Fr i) (hT : ∀ i, I i → Tie cs (l.get i).1)
    (hB : ∀ i, I i → meetsB cs (l.get i).1 (l.get i).2 = true) (y₀ : Fr.E.Str) (a : P₂ × St₂) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg)
    (r₀ : ∀ i : Fin l.length, (OmAt cs l i).Rnd) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D)
    (hsend : ∀ i, Sendable cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i))
    (hs : ∀ i, I i → seedIsS cs l num (rowIsK cs l) (src₂ orc₁) i a (ρ i) ((OmAt cs l i).Z.val (ρ i) (m₀ i))) (c₀ : Cells) :
    ∃ (W : Wit Cells Unit Fill.Tab) (y' : Fr.E.Str), y'.1 = y₀.1 ∧ ∀ i : Fin l.length, I i →
      Sound.ShownAt F cs l (seatAt l num at_) (Sound.strsOf Fr y') i ∧
      PIN F (baseK cs l num at_ decT recOf orc₁).h₂ (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') W ∧
      hasSmp (baseK cs l num at_ decT recOf orc₁).h₂ (at_ (num i)).1 (at_ (num i)).2 a = true ∧
      NoColl F (baseK cs l num at_ decT recOf orc₁).h₂ (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') := by
  rw [h₂_eq]
  exact promise_atG cs l num at_ decT (fun a : P₂ × St₂ => recOf a.1.1) (src₂ orc₁) F I Fr hinj hap hnum hS hFr hT hB y₀ a m₀ r₀ ρ hsend hs c₀

/-- **The call at the last chain's reading.** -/
theorem promise_at₃S {XI : Type} (F : FileDescription XI) (I : Fin l.length → Prop) (Fr : Sound.Frame) (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (hnum : Function.Injective num)
    (hS : ∀ i, I i → FitsAt cs l (seatAt l num at_) F i) (hFr : ∀ i, I i → HoldsAt cs l (seatAt l num at_) Fr i) (hT : ∀ i, I i → Tie cs (l.get i).1)
    (hB : ∀ i, I i → meetsB cs (l.get i).1 (l.get i).2 = true) (y₀ : Fr.E.Str) (a : P₃ × St₃) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg)
    (r₀ : ∀ i : Fin l.length, (OmAt cs l i).Rnd) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D)
    (hsend : ∀ i, Sendable cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i))
    (hs : ∀ i, I i → seedIsS cs l num (rowIsK cs l) (src₃ orc₁) i a (ρ i) ((OmAt cs l i).Z.val (ρ i) (m₀ i))) (c₀ : Cells) :
    ∃ (W : Wit Cells Unit Fill.Tab) (y' : Fr.E.Str), y'.1 = y₀.1 ∧ ∀ i : Fin l.length, I i →
      Sound.ShownAt F cs l (seatAt l num at_) (Sound.strsOf Fr y') i ∧
      PIN F (baseK cs l num at_ decT recOf orc₁).h₃ (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') W ∧
      hasSmp (baseK cs l num at_ decT recOf orc₁).h₃ (at_ (num i)).1 (at_ (num i)).2 a = true ∧
      NoColl F (baseK cs l num at_ decT recOf orc₁).h₃ (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') := by
  rw [h₃_eq]
  exact promise_atG cs l num at_ decT (fun a : P₃ × St₃ => recOf a.1.1) (src₃ orc₁) F I Fr hinj hap hnum hS hFr hT hB y₀ a m₀ r₀ ρ hsend hs c₀

/-- **FOR EVERY RECORD THAT HOLDS THE KIND's ROWS AT I's MEMBERS, WHATEVER THE SOURCE.** -/
theorem member_of_recordG {A : Type} (recOf' : A → Option Rec) (src : A → ℕ → Option (OnBytes.Codes × ℕ × OnBytes.Oracle)) {XI : Type} (F : FileDescription XI) (I : Fin l.length → Prop) (Fr : Sound.Frame)
    (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (hnum : Function.Injective num)
    (hS : ∀ i, I i → FitsAt cs l (seatAt l num at_) F i) (hFr : ∀ i, I i → HoldsAt cs l (seatAt l num at_) Fr i) (hT : ∀ i, I i → Tie cs (l.get i).1)
    (hB : ∀ i, I i → meetsB cs (l.get i).1 (l.get i).2 = true) (hE : ∀ i, I i → CaseE (l.get i).1) (hP : ∀ i, I i → hasPadB cs (l.get i).1 = true)
    (y₀ : Fr.E.Str) (a : A) (hrec : ∀ i, I i → ∃ ρ y, seedIsS cs l num (rowIsK cs l) src i a ρ (fun _ => y)) (c₀ : Cells) :
    ∃ (W : Wit Cells Unit Fill.Tab) (y' : Fr.E.Str), y'.1 = y₀.1 ∧ ∀ i : Fin l.length, I i →
      Sound.ShownAt F cs l (seatAt l num at_) (Sound.strsOf Fr y') i ∧
      PIN F (gAt cs l num at_ (rowIsK cs l) decT recOf' src) (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') W ∧
      hasSmp (gAt cs l num at_ (rowIsK cs l) decT recOf' src) (at_ (num i)).1 (at_ (num i)).2 a = true ∧
      NoColl F (gAt cs l num at_ (rowIsK cs l) decT recOf' src) (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') := by
  classical
  have key : ∀ i : Fin l.length, ∃ (ρ : (OmAt cs l i).Z.D) (m₀ : (OmAt cs l i).Msg), Sendable cs (l.get i).1 (l.get i).2 (m₀, fun _ => 0) ∧
      (I i → seedIsS cs l num (rowIsK cs l) src i a ρ ((OmAt cs l i).Z.val ρ m₀)) := by
    intro i
    by_cases hi : I i
    · obtain ⟨ρ, y, hy⟩ := hrec i hi
      obtain ⟨j₀, h₀⟩ := pad_of_B cs _ (hP i hi)
      obtain ⟨m₀, hs, hv⟩ := exists_msg_of_answer cs (l.get i).1 (l.get i).2 (hE i hi) j₀ h₀ ρ y
      exact ⟨ρ, m₀, hs, fun _ => by rw [hv]; exact hy⟩
    · exact ⟨Classical.arbitrary _, fun _ => 0, sendable_zero cs _ _, fun h => absurd h hi⟩
  choose ρ m₀ hsend hs using key
  exact promise_atG cs l num at_ decT recOf' src F I Fr hinj hap hnum hS hFr hT hB y₀ a m₀ (fun _ _ => 0) ρ hsend hs c₀

/-- **That at the shared chain's reading.** -/
theorem member_of_record₂ {XI : Type} (F : FileDescription XI) (I : Fin l.length → Prop) (Fr : Sound.Frame) (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (hnum : Function.Injective num)
    (hS : ∀ i, I i → FitsAt cs l (seatAt l num at_) F i) (hFr : ∀ i, I i → HoldsAt cs l (seatAt l num at_) Fr i) (hT : ∀ i, I i → Tie cs (l.get i).1)
    (hB : ∀ i, I i → meetsB cs (l.get i).1 (l.get i).2 = true) (hE : ∀ i, I i → CaseE (l.get i).1) (hP : ∀ i, I i → hasPadB cs (l.get i).1 = true)
    (y₀ : Fr.E.Str) (a : P₂ × St₂) (hrec : ∀ i, I i → ∃ ρ y, seedIsS cs l num (rowIsK cs l) (src₂ orc₁) i a ρ (fun _ => y)) (c₀ : Cells) :
    ∃ (W : Wit Cells Unit Fill.Tab) (y' : Fr.E.Str), y'.1 = y₀.1 ∧ ∀ i : Fin l.length, I i →
      Sound.ShownAt F cs l (seatAt l num at_) (Sound.strsOf Fr y') i ∧
      PIN F (baseK cs l num at_ decT recOf orc₁).h₂ (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') W ∧
      hasSmp (baseK cs l num at_ decT recOf orc₁).h₂ (at_ (num i)).1 (at_ (num i)).2 a = true ∧
      NoColl F (baseK cs l num at_ decT recOf orc₁).h₂ (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') := by
  rw [h₂_eq]
  exact member_of_recordG cs l num at_ decT (fun a : P₂ × St₂ => recOf a.1.1) (src₂ orc₁) F I Fr hinj hap hnum hS hFr hT hB hE hP y₀ a hrec c₀

/-- **That at the last chain's reading.** -/
theorem member_of_record₃ {XI : Type} (F : FileDescription XI) (I : Fin l.length → Prop) (Fr : Sound.Frame) (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (hnum : Function.Injective num)
    (hS : ∀ i, I i → FitsAt cs l (seatAt l num at_) F i) (hFr : ∀ i, I i → HoldsAt cs l (seatAt l num at_) Fr i) (hT : ∀ i, I i → Tie cs (l.get i).1)
    (hB : ∀ i, I i → meetsB cs (l.get i).1 (l.get i).2 = true) (hE : ∀ i, I i → CaseE (l.get i).1) (hP : ∀ i, I i → hasPadB cs (l.get i).1 = true)
    (y₀ : Fr.E.Str) (a : P₃ × St₃) (hrec : ∀ i, I i → ∃ ρ y, seedIsS cs l num (rowIsK cs l) (src₃ orc₁) i a ρ (fun _ => y)) (c₀ : Cells) :
    ∃ (W : Wit Cells Unit Fill.Tab) (y' : Fr.E.Str), y'.1 = y₀.1 ∧ ∀ i : Fin l.length, I i →
      Sound.ShownAt F cs l (seatAt l num at_) (Sound.strsOf Fr y') i ∧
      PIN F (baseK cs l num at_ decT recOf orc₁).h₃ (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') W ∧
      hasSmp (baseK cs l num at_ decT recOf orc₁).h₃ (at_ (num i)).1 (at_ (num i)).2 a = true ∧
      NoColl F (baseK cs l num at_ decT recOf orc₁).h₃ (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') := by
  rw [h₃_eq]
  exact member_of_recordG cs l num at_ decT (fun a : P₃ × St₃ => recOf a.1.1) (src₃ orc₁) F I Fr hinj hap hnum hS hFr hT hB hE hP y₀ a hrec c₀

/-! ## The tie in the sending kind's own form, branch by branch -/

theorem seedIsS_iff₂_lo (i : Fin l.length) (h : num i < 3) (a : P₂ × St₂) (ρ : (OmAt cs l i).Z.D) (v : (OmAt cs l i).Z.S → GE) :
    seedIsS cs l num (rowIsK cs l) (src₂ orc₁) i a ρ v ↔ ∃ o, orc₁ (num i) = some o ∧ ∃ y₀, SeedIs cs (l.get i).1 a.1.2.d.st o ρ y₀ ∧ v = fun _ => y₀ := by
  have e : src₂ orc₁ a (num i) = (orc₁ (num i)).bind (stAt a.1.2.d.st) := if_pos h
  unfold seedIsS
  rw [e]
  exact seed_at cs l i a.1.2.d.st (orc₁ (num i)) ρ v

theorem seedIsS_iff₂_hi (i : Fin l.length) (h : ¬ num i < 3) (a : P₂ × St₂) (ρ : (OmAt cs l i).Z.D) (v : (OmAt cs l i).Z.S → GE) :
    seedIsS cs l num (rowIsK cs l) (src₂ orc₁) i a ρ v ↔ ∃ o, orc₂ (num i) = some o ∧ ∃ y₀, SeedIs cs (l.get i).1 a.2.st o ρ y₀ ∧ v = fun _ => y₀ := by
  have e : src₂ orc₁ a (num i) = (orc₂ (num i)).bind (stAt a.2.st) := if_neg h
  unfold seedIsS
  rw [e]
  exact seed_at cs l i a.2.st (orc₂ (num i)) ρ v

theorem seedIsS_iff₃_lo (i : Fin l.length) (h : num i < 3) (a : P₃ × St₃) (ρ : (OmAt cs l i).Z.D) (v : (OmAt cs l i).Z.S → GE) :
    seedIsS cs l num (rowIsK cs l) (src₃ orc₁) i a ρ v ↔ ∃ o, orc₁ (num i) = some o ∧ ∃ y₀, SeedIs cs (l.get i).1 a.2.st o ρ y₀ ∧ v = fun _ => y₀ := by
  have e : src₃ orc₁ a (num i) = (orc₁ (num i)).bind (stAt a.2.st) := if_pos h
  unfold seedIsS
  rw [e]
  exact seed_at cs l i a.2.st (orc₁ (num i)) ρ v

theorem seedIsS_iff₃_border (i : Fin l.length) (h : ¬ num i < 3) (a : P₃ × St₃) (b) (hb : a.2.loc.border = some b) (ρ : (OmAt cs l i).Z.D) (v : (OmAt cs l i).Z.S → GE) :
    seedIsS cs l num (rowIsK cs l) (src₃ orc₁) i a ρ v ↔ ∃ o, orc₂ (num i) = some o ∧ ∃ y₀, SeedIs cs (l.get i).1 b.shared.st o ρ y₀ ∧ v = fun _ => y₀ := by
  have e : src₃ orc₁ a (num i) = (orc₂ (num i)).bind (stAt b.shared.st) := by
    unfold src₃
    rw [if_neg h, hb]
  unfold seedIsS
  rw [e]
  exact seed_at cs l i b.shared.st (orc₂ (num i)) ρ v

theorem seedIsS_iff₃_own (i : Fin l.length) (h : num i = 4) (a : P₃ × St₃) (hb : a.2.loc.border = none) (ρ : (OmAt cs l i).Z.D) (v : (OmAt cs l i).Z.S → GE) :
    seedIsS cs l num (rowIsK cs l) (src₃ orc₁) i a ρ v ↔ ∃ y₀, SeedIs cs (l.get i).1 a.2.st (nOwn a.2) ρ y₀ ∧ v = fun _ => y₀ := by
  have e : src₃ orc₁ a (num i) = (some (nOwn a.2)).bind (stAt a.2.st) := by
    unfold src₃
    rw [h, if_neg (by decide), hb]
    rfl
  unfold seedIsS
  rw [e]
  refine (seed_at cs l i a.2.st (some (nOwn a.2)) ρ v).trans ⟨?_, fun hy => ⟨_, rfl, hy⟩⟩
  rintro ⟨o, ho, hy⟩
  obtain rfl : nOwn a.2 = o := Option.some.inj ho
  exact hy

/-- The source's sixth arm: no elder pin, no border, and not the own message: the source holds nothing, and the tie is false. -/
theorem seedIsS_iff₃_none (i : Fin l.length) (h : ¬ num i < 3) (h4 : num i ≠ 4) (a : P₃ × St₃) (hb : a.2.loc.border = none) (ρ : (OmAt cs l i).Z.D) (v : (OmAt cs l i).Z.S → GE) :
    seedIsS cs l num (rowIsK cs l) (src₃ orc₁) i a ρ v ↔ False := by
  have e : src₃ orc₁ a (num i) = none := by
    unfold src₃
    rw [if_neg h, hb]
    exact if_neg (by simpa using h4)
  unfold seedIsS
  rw [e]
  constructor
  · rintro ⟨_, _, h1, _⟩
    cases h1
  · exact False.elim

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.promise_at₂S
#print axioms Johnson.RunOne.KeyRows23.promise_at₃S
#print axioms Johnson.RunOne.KeyRows23.member_of_recordG
#print axioms Johnson.RunOne.KeyRows23.member_of_record₂
#print axioms Johnson.RunOne.KeyRows23.member_of_record₃
#print axioms Johnson.RunOne.KeyRows23.seedIsS_iff₂_lo
#print axioms Johnson.RunOne.KeyRows23.seedIsS_iff₂_hi
#print axioms Johnson.RunOne.KeyRows23.seedIsS_iff₃_lo
#print axioms Johnson.RunOne.KeyRows23.seedIsS_iff₃_border
#print axioms Johnson.RunOne.KeyRows23.seedIsS_iff₃_own
#print axioms Johnson.RunOne.KeyRows23.seedIsS_iff₃_none
