-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/KeyFillNoCollAt.lean: A SHEET TO Johnson/Desc/Key/KeyFillNoColl.lean: ITS PREMISE ON NUMBERS AT THE REAL SIZES; ITS PREMISE ON THE WITNESS AT A SILLY LAYING; AND A CLOSED CONTROL AT THE TOY.
  allMeet_six · rad_lt_six   at the library's typed csKey and the key file's six sampled messages with their radii (six, Johnson/Desc/Key/KeyFillAtSizes.lean): the library's allMeet holds (it is that file's meets_six); so each radius lies below its code's distance
  rad_lt_six_eval            the same comparison evaluated outright by the kernel · rad_plant: A PLANT: at a radius equal to the distance the library's test says no, at all six
  padW · msgOf_padW          AT lay := THE SECOND TABLE (a silly laying: the witness's message component is read by nobody) the premise hW of fam_pins_… | fam_promise_met is met: the pads hold the tables
  fam_promise_form_is_met    UNDER PUBLIC PREMISES ALONE (seat injective · SeatFits · allMeet · Sendable): there are a sample's tie that meets (uniq), a witness and strings at which PIN ∧ hasSmp ∧ NoColl hold AT ALL SEATS. THE TIE READS NO RECORD AND IS MADE OF
                             THE VERY MESSAGE AND SEED THAT IT IS TO WITNESS: «meets» is true there by fiat; THE LAYING IS SILLY. What bears weight: near, at strings; and that the list of a code word has one member
  Toy.meets · Toy.meets_plant · Toy.promise   the same, closed, at the toy of KeyFillToy.lean
OBJECT: the library's typed constants csKey | the six shapes (none of F_K's text); else none · USER: none: a sheet · LETTERS: arr · decT · recOf.
NOT SAID: that F_K's sendings send these shapes at these radii; NoColl at a word that is not a code word. Nothing on soundness.
-/
import Johnson.Desc.Key.KeyFillNoColl
import Johnson.Desc.Key.KeyFillToy
import Johnson.Desc.Key.KeyFillAtSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open Cb Johnson.Pack OnBytes.Slice Prob
open Johnson.Top.H Johnson.Top.H.Rows

/-! ## At the real sizes -/

theorem allMeet_six : allMeet csKey six = true := meets_six

theorem rad_lt_six : ∀ p ∈ six, p.2 < dOf csKey p.1 := fun p hp =>
  rad_lt_of_meetsAt csKey p.1 p.2 _ _ (meetsB_sound csKey p.1 p.2 (List.all_eq_true.1 meets_six p hp))

theorem rad_lt_six_eval : (six.all fun p => decide (p.2 < dOf csKey p.1)) = true := by decide +kernel

/-- A PLANT. -/
theorem rad_plant : (six.any fun p => meetsB csKey p.1 (dOf csKey p.1)) = false := by decide +kernel

/-! ## The witness, at a silly laying -/

section
variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)

open Classical in
/-- A witness whose pads hold the messages' tables, seat by seat. -/
def padW {Cells : Type} (c₀ : Cells) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg) : Wit Cells Unit Tab where
  cells := c₀
  tok := ()
  msg := fun _ _ _ => 0
  pad := fun j t => if h : ∃ i : Fin l.length, seat i = (j, t) then ofU cs (l.get h.choose).1 (l.get h.choose).2 (m₀ h.choose) else fun _ _ => 0

variable {A Cells Rec : Type} (seedIs : ∀ i : Fin l.length, A → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop)
  (arr : ℕ → ℕ → ℕ) (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : A → Option Rec)

theorem msgOf_padW (hinj : Function.Injective seat) (c₀ : Cells) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg) (i : Fin l.length) :
    msgOf (famG cs l seat seedIs arr (fun _ _ _ p => p) decT recOf) (padW cs l seat c₀ m₀) (seat i).1 (seat i).2 = ofU cs (l.get i).1 (l.get i).2 (m₀ i) := by
  classical
  have h : ∃ i' : Fin l.length, seat i' = ((seat i).1, (seat i).2) := ⟨i, rfl⟩
  show (if h : ∃ i' : Fin l.length, seat i' = ((seat i).1, (seat i).2) then ofU cs (l.get h.choose).1 (l.get h.choose).2 (m₀ h.choose) else fun _ _ => 0) = _
  rw [dif_pos h]
  have hc := choose_seat l seat hinj i h
  generalize h.choose = i' at hc
  subst hc
  rfl

end

/-- **UNDER PUBLIC PREMISES ALONE THE PROMISE's FORM (PIN · hasSmp · NoColl) IS MET AT ALL SEATS**: at a tie made of the message itself and a silly laying. -/
theorem fam_promise_form_is_met (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ) {XI Cells Rec : Type} (F : FileDescription XI)
    (arr : ℕ → ℕ → ℕ) (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Unit → Option Rec) (c₀ : Cells)
    (hinj : Function.Injective seat) (hS : SeatFits F cs l seat) (hB : allMeet cs l = true)
    (cell : ℕ → Option (ℕ × List UInt64)) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg)
    (r₀ : ∀ i : Fin l.length, (OmAt cs l i).Rnd) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D)
    (hsend : ∀ i, Sendable cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i)) :
    ∃ seedIs' : ∀ i : Fin l.length, Unit → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop,
      (∀ i a ρ v ρ' v', seedIs' i a ρ v → seedIs' i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v') ∧
      ∃ (W : Wit Cells Unit Tab) (y : Strs), y.cell = cell ∧ ∀ i : Fin l.length,
        PIN F (famG cs l seat seedIs' arr (fun _ _ _ p => p) decT recOf) (seat i).1 (seat i).2 () y W ∧
        hasSmp (famG cs l seat seedIs' arr (fun _ _ _ p => p) decT recOf) (seat i).1 (seat i).2 () = true ∧
        NoColl F (famG cs l seat seedIs' arr (fun _ _ _ p => p) decT recOf) (seat i).1 (seat i).2 () y := by
  have hu : ∀ (i : Fin l.length) (a : Unit) (ρ₁ : (OmAt cs l i).Z.D) (v : (OmAt cs l i).Z.S → GE) (ρ' : (OmAt cs l i).Z.D) (v' : (OmAt cs l i).Z.S → GE),
      (ρ₁ = ρ i ∧ v = (OmAt cs l i).Z.val (ρ i) (m₀ i)) → (ρ' = ρ i ∧ v' = (OmAt cs l i).Z.val (ρ i) (m₀ i)) →
      (OmAt cs l i).Z.val ρ₁ = (OmAt cs l i).Z.val ρ' ∧ v = v' := by
    rintro i _ ρ₁ v ρ' v' ⟨rfl, rfl⟩ ⟨h, rfl⟩
    exact ⟨by rw [h], rfl⟩
  refine ⟨fun i _ ρ₁ v => ρ₁ = ρ i ∧ v = (OmAt cs l i).Z.val (ρ i) (m₀ i), hu, padW cs l seat c₀ m₀, ?_⟩
  exact fam_promise_met cs l seat F _ arr (fun _ _ _ p => p) decT recOf hinj hS hu hB cell () m₀ r₀ ρ hsend (fun i => ⟨rfl, rfl⟩) (padW cs l seat c₀ m₀)
    (msgOf_padW cs l seat _ arr decT recOf hinj c₀ m₀)

/-! ## The toy -/

namespace Toy

theorem meets : allMeet cs l = true := by decide +kernel

/-- A PLANT: the first member's radius raised to its code's distance. -/
theorem meets_plant : allMeet cs [(sA, 2), (sB, 0)] = false := by decide +kernel

/-- **CLOSED: AT THE TOY, PIN · hasSmp · NoColl AT BOTH MEMBERS, AT ONE y AND ONE WITNESS.** -/
theorem promise {Rec : Type} (arr : ℕ → ℕ → ℕ) (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Unit) (recOf : Unit → Option Rec) :
    ∃ seedIs' : ∀ i : Fin l.length, Unit → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop,
      (∀ i a ρ v ρ' v', seedIs' i a ρ v → seedIs' i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v') ∧
      ∃ (W : Wit Unit Unit Tab) (y : Strs), y.cell = (fun _ => none) ∧ ∀ i : Fin l.length,
        PIN (FW 15) (famG cs l seat seedIs' arr (fun _ _ _ p => p) decT recOf) (seat i).1 (seat i).2 () y W ∧
        hasSmp (famG cs l seat seedIs' arr (fun _ _ _ p => p) decT recOf) (seat i).1 (seat i).2 () = true ∧
        NoColl (FW 15) (famG cs l seat seedIs' arr (fun _ _ _ p => p) decT recOf) (seat i).1 (seat i).2 () y :=
  fam_promise_form_is_met cs l seat (FW 15) arr decT recOf () seat_inj fits meets (fun _ => none) (fun _ _ => 1) (fun _ _ => 0) (fun _ => Classical.arbitrary _)
    (fun _ _ => ⟨fun _ => ⟨1, map_one _⟩, fun _ => ⟨0, map_zero _⟩⟩)

end Toy

end VerifiableInference.Desc.Key.Fill

#print axioms VerifiableInference.Desc.Key.Fill.allMeet_six
#print axioms VerifiableInference.Desc.Key.Fill.rad_lt_six
#print axioms VerifiableInference.Desc.Key.Fill.rad_lt_six_eval
#print axioms VerifiableInference.Desc.Key.Fill.rad_plant
#print axioms VerifiableInference.Desc.Key.Fill.msgOf_padW
#print axioms VerifiableInference.Desc.Key.Fill.fam_promise_form_is_met
#print axioms VerifiableInference.Desc.Key.Fill.Toy.meets
#print axioms VerifiableInference.Desc.Key.Fill.Toy.meets_plant
#print axioms VerifiableInference.Desc.Key.Fill.Toy.promise
