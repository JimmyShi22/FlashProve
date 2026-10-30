-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyFillRecord.lean: FOR EVERY STATE THAT HOLDS THE SENDING KIND's ROWS THERE IS A MEMBER. Johnson/RunOne/KeyFillMeet.lean lays a state to fit given messages. Here the other way round: given ANY state of the first chain whose statement holds, at the members' numbers, records
in the sending kind's own form (SeedIs), messages are found that fit its answers: THE PAD MAKES EVERY ANSWER REACHABLE.
  mat_pad                 under CaseE the library's sample matrix at a pad's place is the seed's factor
  exists_msg_of_answer    so, for every seed ρ and every answer y₀: a message that can be sent has the answer y₀ at ρ: y₀ / ρ.2 at one pad's place, 0 elsewhere
  hasPadB · pad_of_B · hasPad_six   a pad's place exists: a plain test; at the six by the kernel
  member_of_record        KeyFillMeet.lean's promise_at₁ with its premise on the record replaced by «SeedIs at I's numbers»: FOR EVERY STATE, laid by nobody: ∃ a witness and oracles of the rule's own type: PIN ∧ hasSmp ∧ NoColl at B.h₁ at I's seats
  member_fk_rec₁          the same at descriptionFromSource X N P · fr₁ D · the woven tables' reading
  ToyR.member             a control: at the toy's record WITH ITS TARGET TURNED BY ANY d there is still a member
THE ORACLES ARE BUILT HERE: the code words of messages that are CHOSEN TO FIT THE STATE's ANSWERS: NOT A RUN's OWN ORACLES; many messages have one answer, and the one chosen is 0 off the pad. So this shows that a promise can be met at such a state; it says nothing of what a prover committed to.
OBJECT: the library's portZ; SeedIs (Johnson/Desc/K1/Law/SeedIs.lean); BaseSt.h₁ · USER: imported by Johnson/RunOne/KeyFillCells.lean, Johnson/RunOne/KeyFillOn.lean (meant: a border's whole promise at a state that the blocks reach) · LETTERS: a · X N P D · decT · recOf.
Nothing on soundness.
-/
import Johnson.RunOne.KeyFillMeet

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyRows23
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.Key (Xi FirstState)
open VerifiableInference.Desc.K1 (SeedIs Tie)
open Cb Johnson.Pack OnBytes.Maker OnBytes.Slice

section
variable (cs : OnBytes.Codes) (s : OnBytes.OracleShape) (e : ℕ)

/-- **Under CaseE the sample matrix at a pad's place is the seed's factor.** -/
theorem mat_pad (hE : CaseE s) (j₀ : (portCode cs s).J) (h₀ : padP cs s j₀) (ρ : (portOmZ cs s e).Z.D) (u : (portOmZ cs s e).Z.S) :
    (portOmZ cs s e).Z.mat ρ u j₀ = ((ρ.2 : GEˣ) : GE) := by
  have es : sigmaZ cs s j₀ = Sum.inr ⟨j₀, h₀⟩ := by
    simp [sigmaZ, Equiv.sumCompl, h₀]
  show Sum.elim _ (fun i => ((ρ.2 : GEˣ) : GE) * wZ cs s i) (sigmaZ cs s j₀) = _
  rw [es]
  show ((ρ.2 : GEˣ) : GE) * wZ cs s ⟨j₀, h₀⟩ = _
  rw [wZ_one cs s hE, mul_one]

open Classical in
/-- **THE PAD MAKES EVERY ANSWER REACHABLE.** -/
theorem exists_msg_of_answer (hE : CaseE s) (j₀ : (portCode cs s).J) (h₀ : padP cs s j₀) (ρ : (portOmZ cs s e).Z.D) (y₀ : GE) :
    ∃ m₀ : (portOmZ cs s e).Msg, Sendable cs s e (m₀, fun _ => 0) ∧ (portOmZ cs s e).Z.val ρ m₀ = fun _ => y₀ := by
  refine ⟨fun j => if j = j₀ then (((ρ.2 : GEˣ)⁻¹ : GEˣ) : GE) * y₀ else 0, fun h1 => ⟨fun x => ?_, fun _ => ⟨0, map_zero _⟩⟩, ?_⟩
  · have hne : (Sum.inl x : (portCode cs s).J) ≠ j₀ := by
      rintro rfl
      have hm0 : s.maskRows = 0 := h₀.1
      rcases hE with h | h <;> omega
    show (if (Sum.inl x : (portCode cs s).J) = j₀ then _ else (0 : GE)) ∈ _
    rw [if_neg hne]
    exact ⟨0, map_zero _⟩
  · funext u
    show ∑ j, (portOmZ cs s e).Z.mat ρ u j * (if j = j₀ then (((ρ.2 : GEˣ)⁻¹ : GEˣ) : GE) * y₀ else 0) = y₀
    refine (Finset.sum_eq_single j₀ (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ j₀) h)).trans ?_
    · split_ifs with h
      · exact absurd h hj
      · exact mul_zero _
    · split_ifs with h
      · rw [mat_pad cs s e hE j₀ h₀, ← mul_assoc, Units.mul_inv, one_mul]
      · exact absurd rfl h

/-- Has the shape a pad's place. A PLAIN TEST. -/
def hasPadB : Bool := if 0 < s.maskRows then decide (0 < (pMask cs s).ell) else decide (0 < s.mainRows) && decide (0 < (pMain cs s).ell)

theorem pad_of_B (h : hasPadB cs s = true) : ∃ j₀, padP cs s j₀ := by
  unfold hasPadB at h
  by_cases hm : 0 < s.maskRows
  · rw [if_pos hm, decide_eq_true_eq] at h
    have hl : (cMask cs s).l = (pMask cs s).ell := rfl
    exact ⟨.inr (⟨s.maskRows - 1, by omega⟩, ⟨(pMask cs s).ell - 1, by omega⟩), by show s.maskRows - 1 + 1 = s.maskRows; omega, by show (pMask cs s).ell - 1 + 1 = (pMask cs s).ell; omega⟩
  · rw [if_neg hm, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
    exact pad_exists cs s (by omega) h.1 h.2

end

theorem hasPad_six : (six.all fun p => hasPadB Johnson.Top.H.csKey p.1) = true := by decide +kernel

/-- A PLANT: a shape without rows. -/
theorem hasPad_plant : hasPadB Johnson.Top.H.csKey { Johnson.Top.H.shIdx with maskRows := 0 } = false := by decide +kernel

section
variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) (num : Fin l.length → ℕ) (at_ : Where)
  {Cells Rec : Type} (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec) (orc₁ : ℕ → Option ℕ)

/-- **FOR EVERY STATE THAT HOLDS THE KIND's ROWS AT I's NUMBERS: A MEMBER OF PIN · hasSmp · NoColl AT B.h₁.** -/
theorem member_of_record {XI : Type} (F : FileDescription XI) (I : Fin l.length → Prop) (Fr : Sound.Frame) (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (hnum : Function.Injective num)
    (hS : ∀ i, I i → FitsAt cs l (seatAt l num at_) F i) (hFr : ∀ i, I i → HoldsAt cs l (seatAt l num at_) Fr i) (hT : ∀ i, I i → Tie cs (l.get i).1)
    (hB : ∀ i, I i → meetsB cs (l.get i).1 (l.get i).2 = true) (hE : ∀ i, I i → CaseE (l.get i).1) (hP : ∀ i, I i → hasPadB cs (l.get i).1 = true)
    (y₀ : Fr.E.Str) (a : Xi × FirstState) (hrec : ∀ i, I i → ∃ o ρ y, orc₁ (num i) = some o ∧ SeedIs cs (l.get i).1 a.2.d.st o ρ y) (c₀ : Cells) :
    ∃ (W : Wit Cells Unit Fill.Tab) (y' : Fr.E.Str), y'.1 = y₀.1 ∧ ∀ i : Fin l.length, I i →
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
  exact promise_at₁ cs l num at_ decT recOf orc₁ F I Fr hinj hap hnum hS hFr hT hB y₀ a m₀ (fun _ _ => 0) ρ hsend hs c₀

end

/-! ## At the key file's own letters -/

section
open OnBytes.Params VerifiableInference.Desc.Sound
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (D : WholeD)
  {Cells Rec : Type} (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec)

/-- **AT descriptionFromSource X N P · fr₁ D · THE WOVEN TABLES' READING: FOR EVERY STATE THAT HOLDS THE KIND's ROWS AT THE NUMBERS OF A SET I OF THE FIRST CHAIN's THREE.** -/
theorem member_fk_rec₁ (I : Fin six.length → Prop) (hI : ∀ i, I i → numSix i < 3) (t0 t1 t2 : String)
    (n0 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t0 Johnson.Top.H.shIdx 0 0 = none)
    (n1 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t1 Johnson.Top.H.shMul 1 0 = none)
    (n2 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t2 Johnson.Top.H.shW 5 0 = none)
    (f0 : holdsB (fr₁ D) 0 (aOf Johnson.Top.H.csKey Johnson.Top.H.shIdx) = true)
    (f1 : holdsB (fr₁ D) 1 (aOf Johnson.Top.H.csKey Johnson.Top.H.shMul) = true)
    (f2 : holdsB (fr₁ D) 5 (aOf Johnson.Top.H.csKey Johnson.Top.H.shW) = true)
    (y₀ : (fr₁ D).E.Str) (a : Xi × FirstState)
    (hrec : ∀ i, I i → ∃ o ρ y, (KeyRows1.plan₁ (oneAt X)).orc (numSix i) = some o ∧ SeedIs Johnson.Top.H.csKey (six.get i).1 a.2.d.st o ρ y) (c₀ : Cells) :
    ∃ (W : Wit Cells Unit Fill.Tab) (y' : (fr₁ D).E.Str), y'.1 = y₀.1 ∧ ∀ i : Fin six.length, I i →
      PIN (Fk X N P) (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 a (strsOf (fr₁ D) y') W ∧
      hasSmp (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 a = true ∧
      NoColl (Fk X N P) (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 a (strsOf (fr₁ D) y') := by
  refine member_of_record Johnson.Top.H.csKey six numSix atSix decT recOf (KeyRows1.plan₁ (oneAt X)).orc (Fk X N P) I (fr₁ D) seat_inj_six shapesApart_six
    (fun a b h => Fin.ext h) ?_ ?_ (fun i _ => tie_six i) (fun i _ => List.all_eq_true.1 meets_six _ (List.get_mem six i))
    (fun i _ => of_decide_eq_true (List.all_eq_true.1 caseE_six _ (List.get_mem six i))) (fun i _ => List.all_eq_true.1 hasPad_six _ (List.get_mem six i)) y₀ a hrec c₀
  · intro i hi
    obtain ⟨a, ha⟩ := i
    have h3 : a < 3 := hI _ hi
    interval_cases a
    · exact fitsAt_of_noFault _ six _ _ _ t0 n0
    · exact fitsAt_of_noFault _ six _ _ _ t1 n1
    · exact fitsAt_of_noFault _ six _ _ _ t2 n2
  · intro i hi
    obtain ⟨a, ha⟩ := i
    have h3 : a < 3 := hI _ hi
    interval_cases a
    · exact holdsAt_of_B _ six _ _ _ f0
    · exact holdsAt_of_B _ six _ _ _ f1
    · exact holdsAt_of_B _ six _ _ _ f2

end

/-! ## A control -/

namespace ToyR
open VerifiableInference.Desc.Key.Fill.Toy
open Johnson.RunOne.KeyRows23.ToyB (num at_ apartT)

/-- **CLOSED: AT THE TOY's RECORD WITH ITS FIRST TARGET TURNED BY ANY d THERE IS STILL A MEMBER**: another message fits the turned answer. (ToyK.turned: the honest table is pinned by no witness there.) -/
theorem member (d : GE) : ∃ (W : Wit Unit Unit Fill.Tab) (y' : (FrD 1).E.Str), ∀ i : Fin l.length,
      PIN (FW 15) (baseK (Rec := Unit) cs l num at_ (fun _ _ => none) (fun _ => none) some).h₁ (at_ (num i)).1 (at_ (num i)).2 (⟨{}⟩, ToyK.sK d) (Sound.strsOf (FrD 1) y') W ∧
      hasSmp (baseK (Rec := Unit) (Cells := Unit) cs l num at_ (fun _ _ => none) (fun _ => none) some).h₁ (at_ (num i)).1 (at_ (num i)).2 (⟨{}⟩, ToyK.sK d) = true ∧
      NoColl (FW 15) (baseK (Rec := Unit) (Cells := Unit) cs l num at_ (fun _ _ => none) (fun _ => none) some).h₁ (at_ (num i)).1 (at_ (num i)).2 (⟨{}⟩, ToyK.sK d) (Sound.strsOf (FrD 1) y') := by
  obtain ⟨W, y', _, h⟩ := member_of_record cs l num at_ (fun _ _ => none) (fun _ => none) some (FW 15) (fun _ => True) (FrD 1) seat_inj apartT Fin.val_injective
    (fun i _ => fits i) (fun i _ => holds i) (fun i _ => ToyK.tieT i) (fun i _ => List.all_eq_true.1 meets _ (List.get_mem l i))
    (fun i _ => (by decide : ∀ i : Fin l.length, CaseE (l.get i).1) i) (fun i _ => (by decide +kernel : ∀ i : Fin l.length, hasPadB cs (l.get i).1 = true) i)
    ((fun _ => (0, []), fun _ => []) : (FrD 1).E.Str) (⟨{}⟩, ToyK.sK d)
    (by
      rintro ⟨k, hk⟩ _
      have hk' : k < 2 := hk
      interval_cases k
      · obtain ⟨o, ho, y, hy, _⟩ := (seedIsS_iff₁ cs l num some _ _ _ _).1 (ToyK.spells₀ d)
        exact ⟨o, _, y, ho, hy⟩
      · obtain ⟨o, ho, y, hy, _⟩ := (seedIsS_iff₁ cs l num some _ _ _ _).1 (ToyK.spells₁ d)
        exact ⟨o, _, y, ho, hy⟩) ()
  exact ⟨W, y', fun i => h i trivial⟩

end ToyR

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.mat_pad
#print axioms Johnson.RunOne.KeyRows23.exists_msg_of_answer
#print axioms Johnson.RunOne.KeyRows23.pad_of_B
#print axioms Johnson.RunOne.KeyRows23.hasPad_six
#print axioms Johnson.RunOne.KeyRows23.hasPad_plant
#print axioms Johnson.RunOne.KeyRows23.member_of_record
#print axioms Johnson.RunOne.KeyRows23.member_fk_rec₁
#print axioms Johnson.RunOne.KeyRows23.ToyR.member
