-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/KeyFillSent.lean: THE FIRST MEMBERS (Johnson/Desc/Key/KeyFillStrs.lean) WITH THE LIBRARY's OWN PREMISE ON WHAT CAN BE SENT IN PLACE OF A WORD AS SENT. «AT AN ENCODING OF ANY MESSAGE» IS NOT FREE: where a shape's main rows go over the
base field, a message with an entry outside it is the lift of no word as sent. Johnson/Pack/TwoPads.lean names just that: Sendable; its sent_of gives the word.
  sendable_of_deg3 | sendable_zero   Sendable is free where the main rows go over the extension field; and at the zero message with the zero tail, at every shape
  fam_members_of_sendable   ONE y, ONE record: at every member a told tree, a sample and a Member: for all messages and tails that can be sent
  fam_pins_of_sendable      and all PINs at one witness whose tables at the seats are the messages' (a premise)
  fam_form_is_met           UNDER PUBLIC PREMISES ALONE (seat injective · SeatFits · Sendable): THERE IS a seedIs that meets (uniq), at which all members exist together. ITS seedIs IS A SILLY ONE: it reads no record (A := Unit) AND IS MADE OF THE VERY MESSAGE AND SEED THAT IT IS TO WITNESS: Member's second half («meets») is true there BY FIAT; what bears weight is the first half (near), at strings: it shows that the
                            premises on the letter seedIs are not contradictory, no more
OBJECT: none: a filling of letters · USER: Johnson/Desc/Key/KeyFillToy.lean · LETTERS: F · cs · l · seat · cell · seedIs · a.
NOT SAID: that a run of the programs lays such strings or such a record; that SeatFits holds at a real description; that no two members meet one sample. At l := [] all is true for nothing.
Nothing on soundness.
-/
import Johnson.Desc.Key.KeyFillStrs
import Johnson.Pack.TwoPads

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open Cb Johnson.Pack OnBytes.Slice Prob

variable (cs : OnBytes.Codes)

theorem sendable_of_deg3 (s : OnBytes.OracleShape) (e : ℕ) (h : s.mainDeg = 3) (w : (portOmZ cs s e).Wit) : Sendable cs s e w := fun h1 => by omega

theorem sendable_zero (s : OnBytes.OracleShape) (e : ℕ) : Sendable cs s e ((fun _ => 0, fun _ => 0) : (portOmZ cs s e).Wit) :=
  fun _ => ⟨fun _ => ⟨0, map_zero _⟩, fun _ => ⟨0, map_zero _⟩⟩

variable (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ) {XI : Type} (F : FileDescription XI)
  {A Cells Rec : Type} (seedIs : ∀ i : Fin l.length, A → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop)
  (arr : ℕ → ℕ → ℕ) (lay : ℕ → ℕ → Tab → Tab → Tab) (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : A → Option Rec)

/-- **ONE y, ONE RECORD: A MEMBER AT EVERY SEAT, FOR ALL MESSAGES AND TAILS THAT CAN BE SENT.** -/
theorem fam_members_of_sendable (hinj : Function.Injective seat) (hS : SeatFits F cs l seat)
    (uniq : ∀ i a ρ v ρ' v', seedIs i a ρ v → seedIs i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v')
    (cell : ℕ → Option (ℕ × List UInt64)) (a : A) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg)
    (r₀ : ∀ i : Fin l.length, (OmAt cs l i).Rnd) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D)
    (hsend : ∀ i, Sendable cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i)) (hs : ∀ i, seedIs i a (ρ i) ((OmAt cs l i).Z.val (ρ i) (m₀ i))) :
    ∃ y : Strs, y.cell = cell ∧ ∀ i : Fin l.length, ∃ o z, F.oracleAt (seat i).1 = some o ∧
      (famG cs l seat seedIs arr lay decT recOf).smp a (seat i).1 (seat i).2 = some z ∧
      Member F (famG cs l seat seedIs arr lay decT recOf) o (seat i).1 (seat i).2 y z (ofU cs (l.get i).1 (l.get i).2 (m₀ i)) := by
  choose f hf using fun i => sent_of cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i) (hsend i)
  exact fam_members_exist cs l seat F seedIs arr lay decT recOf hinj hS uniq cell a f m₀ r₀ ρ hf hs

/-- **AND ALL PINS TOGETHER.** -/
theorem fam_pins_of_sendable {Tok : Type} (hinj : Function.Injective seat) (hS : SeatFits F cs l seat)
    (uniq : ∀ i a ρ v ρ' v', seedIs i a ρ v → seedIs i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v')
    (cell : ℕ → Option (ℕ × List UInt64)) (a : A) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg)
    (r₀ : ∀ i : Fin l.length, (OmAt cs l i).Rnd) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D)
    (hsend : ∀ i, Sendable cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i)) (hs : ∀ i, seedIs i a (ρ i) ((OmAt cs l i).Z.val (ρ i) (m₀ i)))
    (W : Wit Cells Tok Tab) (hW : ∀ i, msgOf (famG cs l seat seedIs arr lay decT recOf) W (seat i).1 (seat i).2 = ofU cs (l.get i).1 (l.get i).2 (m₀ i)) :
    ∃ y : Strs, y.cell = cell ∧ ∀ i : Fin l.length, PIN F (famG cs l seat seedIs arr lay decT recOf) (seat i).1 (seat i).2 a y W := by
  choose f hf using fun i => sent_of cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i) (hsend i)
  exact fam_pins_together cs l seat F seedIs arr lay decT recOf hinj hS uniq cell a f m₀ r₀ ρ hf hs W hW

/-- **UNDER PUBLIC PREMISES ALONE THE FORM IS MET**, at a seedIs that reads no record. -/
theorem fam_form_is_met (recOf' : Unit → Option Rec) (hinj : Function.Injective seat) (hS : SeatFits F cs l seat)
    (cell : ℕ → Option (ℕ × List UInt64)) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg)
    (r₀ : ∀ i : Fin l.length, (OmAt cs l i).Rnd) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D)
    (hsend : ∀ i, Sendable cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i)) :
    ∃ seedIs' : ∀ i : Fin l.length, Unit → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop,
      (∀ i a ρ v ρ' v', seedIs' i a ρ v → seedIs' i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v') ∧
      ∃ y : Strs, y.cell = cell ∧ ∀ i : Fin l.length, ∃ o z, F.oracleAt (seat i).1 = some o ∧
        (famG cs l seat seedIs' arr lay decT recOf').smp () (seat i).1 (seat i).2 = some z ∧
        Member F (famG cs l seat seedIs' arr lay decT recOf') o (seat i).1 (seat i).2 y z (ofU cs (l.get i).1 (l.get i).2 (m₀ i)) := by
  have hu : ∀ (i : Fin l.length) (a : Unit) (ρ₁ : (OmAt cs l i).Z.D) (v : (OmAt cs l i).Z.S → GE) (ρ' : (OmAt cs l i).Z.D) (v' : (OmAt cs l i).Z.S → GE),
      (ρ₁ = ρ i ∧ v = (OmAt cs l i).Z.val (ρ i) (m₀ i)) → (ρ' = ρ i ∧ v' = (OmAt cs l i).Z.val (ρ i) (m₀ i)) →
      (OmAt cs l i).Z.val ρ₁ = (OmAt cs l i).Z.val ρ' ∧ v = v' := by
    rintro i _ ρ₁ v ρ' v' ⟨rfl, rfl⟩ ⟨h, rfl⟩
    exact ⟨by rw [h], rfl⟩
  exact ⟨fun i _ ρ₁ v => ρ₁ = ρ i ∧ v = (OmAt cs l i).Z.val (ρ i) (m₀ i), hu,
    fam_members_of_sendable cs l seat F _ arr lay decT recOf' hinj hS hu cell () m₀ r₀ ρ hsend fun i => ⟨rfl, rfl⟩⟩

end VerifiableInference.Desc.Key.Fill

#print axioms VerifiableInference.Desc.Key.Fill.sendable_of_deg3
#print axioms VerifiableInference.Desc.Key.Fill.sendable_zero
#print axioms VerifiableInference.Desc.Key.Fill.fam_members_of_sendable
#print axioms VerifiableInference.Desc.Key.Fill.fam_pins_of_sendable
#print axioms VerifiableInference.Desc.Key.Fill.fam_form_is_met
