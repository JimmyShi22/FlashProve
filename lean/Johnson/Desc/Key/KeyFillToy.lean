-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- In Johnson/Desc/Block.lean Chain has first · front · links · back · last; FileDescription has wanted | owed.
/-
Johnson/Desc/Key/KeyFillToy.lean: A CONTROL: THE PREMISES OF Johnson/Desc/Key/KeyFillStrs.lean | KeyFillSent.lean CAN BE MET TOGETHER, AT A FAMILY THAT IS NOT EMPTY: A TOY DESCRIPTION, WITHOUT ANY PREMISE LEFT. One tree of two leaves and fifteen words a
leaf, three tenants: a member (one main row over the base field, one mask row) · A STRANGER that is no member · a second member (two main rows over the extension field, no mask row).
  Toy.fits          SeatFits holds at the toy: by the kernel, closed
  Toy.not_fits      A PLANT: the same tree told with fourteen words: SeatFits is FALSE (so it is no empty test)
  Toy.members       CLOSED: A THEOREM OF EXISTENCE: there are a seedIs that meets (uniq) and strings y at which BOTH members have a told tree, a sample and a Member: the table of the message that is 1 everywhere
  Toy.fits1 · Toy.fill_member   the like at fillG, one tenant (the first member's seat)
THE TOY IS NO DESCRIPTION OF A PROTOCOL: its one block is quiet, its plan empty; none of Block.lean's tests on a plan is claimed of it. Its seedIs reads no record AND IS MADE OF THE VERY MESSAGE AND SEED THAT IT IS TO WITNESS: «meets» is true there BY FIAT; what bears weight is «near», at strings.
OBJECT: none: a toy · USER: none: a control · LETTERS: arr · lay · decT · recOf.
Nothing on soundness.
-/
import Johnson.Desc.Key.KeyFillSent

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Key.Fill.Toy
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open Cb Johnson.Pack OnBytes.Slice Prob

def cs : OnBytes.Codes := { base := #[⟨1, 1, 0⟩], mask := #[⟨1, 1, 0⟩] }
def sA : OnBytes.OracleShape := { code := 0, mainRows := 1, mainDeg := 1, maskRows := 1, maskCode := 0 }
def sB : OnBytes.OracleShape := { code := 0, mainRows := 2, mainDeg := 3, maskRows := 0, maskCode := 0 }
def tA : SymbolComponent := ⟨1, 3, 1, true, []⟩
def tN : SymbolComponent := ⟨2, 3, 1, false, []⟩
def tB : SymbolComponent := ⟨6, 0, 3, true, []⟩
/-- The tree, told with w words a leaf. The tenants' words add up to 15. -/
def oW (w : ℕ) : Oracle := ⟨1, w, [tA, tN, tB]⟩

def FW (w : ℕ) : FileDescription Unit where
  S₁ := Unit
  S₂ := Unit
  S₃ := Unit
  Cl := Unit
  plans := ([], [], [])
  tableDepth := 0
  wanted := []
  owed := []
  fileOk := true
  okStart := fun _ => true
  XiPub := Unit
  pub := fun _ => ()
  start₁ := fun _ => ()
  start₂ := fun _ => ()
  start₃ := fun _ _ _ => .ok ()
  first := ⟨{ roundlessBlock "toy" 1 none 0 (fun s => .ok s) with oracles := [[oW w]] }, [], [], [], roundlessBlock "toy: end" 1 none 1 (fun s => .ok s)⟩
  shared := ⟨roundlessBlock "toy" 2 none 0 (fun s => .ok s), [], [], [], roundlessBlock "toy: end" 2 none 1 (fun s => .ok s)⟩
  second := ⟨roundlessBlock "toy" 3 none 0 (fun s => .ok s), [], [], [], roundlessBlock "toy: end" 3 none 1 (fun s => .ok s)⟩
  fin := fun _ _ _ _ => true

def l : List (OnBytes.OracleShape × ℕ) := [(sA, 0), (sB, 0)]
def seat : Fin l.length → ℕ × ℕ := fun i => (0, 2 * i.val)

theorem seat_inj : Function.Injective seat := fun a b h => Fin.ext (by
  have h2 : 2 * a.val = 2 * b.val := congrArg Prod.snd h
  omega)

theorem told (w : ℕ) : (FW w).oracleAt 0 = some (oW w) := rfl

/-- **SeatFits holds at the toy.** -/
theorem fits : SeatFits (FW 15) cs l seat := by
  rintro ⟨k, hk⟩
  have hk' : k < 2 := hk
  interval_cases k
  · exact ⟨oW 15, tA, rfl, rfl, rfl, rfl, rfl, Or.inr rfl, rfl, Or.inl rfl⟩
  · exact ⟨oW 15, tB, rfl, rfl, rfl, rfl, rfl, Or.inr rfl, rfl, Or.inr rfl⟩

/-- **A PLANT: told with fourteen words, the seats do not fit.** -/
theorem not_fits : ¬ SeatFits (FW 14) cs l seat := by
  intro h
  obtain ⟨o', _, ho, _, _, _, _, _, hsum, _⟩ := h ⟨0, by decide⟩
  obtain rfl : oW 14 = o' := Option.some.inj ((told 14).symm.trans ho)
  exact absurd hsum (by decide)

/-- **CLOSED: BOTH MEMBERS OF THE TOY HAVE A MEMBER, AT ONE y.** -/
theorem members {Cells Rec : Type} (arr : ℕ → ℕ → ℕ) (lay : ℕ → ℕ → Tab → Tab → Tab) (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Unit → Option Rec) :
    ∃ seedIs' : ∀ i : Fin l.length, Unit → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop,
      (∀ i a ρ v ρ' v', seedIs' i a ρ v → seedIs' i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v') ∧
      ∃ y : Strs, y.cell = (fun _ => none) ∧ ∀ i : Fin l.length, ∃ o z, (FW 15).oracleAt (seat i).1 = some o ∧
        (famG cs l seat seedIs' arr lay decT recOf).smp () (seat i).1 (seat i).2 = some z ∧
        Member (FW 15) (famG cs l seat seedIs' arr lay decT recOf) o (seat i).1 (seat i).2 y z (ofU cs (l.get i).1 (l.get i).2 fun _ => 1) :=
  fam_form_is_met cs l seat (FW 15) arr lay decT recOf seat_inj fits (fun _ => none) (fun _ _ => 1) (fun _ _ => 0) (fun _ => Classical.arbitrary _)
    (fun _ _ => ⟨fun _ => ⟨1, map_one _⟩, fun _ => ⟨0, map_zero _⟩⟩)

/-- SeatFits at the first member alone. -/
theorem fits1 : SeatFits (FW 15) cs [(sA, 0)] fun _ => (0, 0) := by
  rintro ⟨k, hk⟩
  have hk' : k < 1 := hk
  interval_cases k
  exact ⟨oW 15, tA, rfl, rfl, rfl, rfl, rfl, Or.inr rfl, rfl, Or.inl rfl⟩

/-- **CLOSED, AT fillG: A THEOREM OF EXISTENCE: the first member's seat has a Member.** -/
theorem fill_member {Cells Rec : Type} (arr : ℕ → ℕ → ℕ) (lay : ℕ → ℕ → Tab → Tab → Tab) (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Unit → Option Rec) :
    ∃ seedIs' : Unit → (portOmZ cs sA 0).Z.D → ((portOmZ cs sA 0).Z.S → GE) → Prop,
      (∀ a ρ v ρ' v', seedIs' a ρ v → seedIs' a ρ' v' → (portOmZ cs sA 0).Z.val ρ = (portOmZ cs sA 0).Z.val ρ' ∧ v = v') ∧
      ∃ (y : Strs) (o : Oracle) (z : (portOmZ cs sA 0).Smp), (FW 15).oracleAt 0 = some o ∧ (fillG cs sA 0 0 0 seedIs' arr lay decT recOf).smp () 0 0 = some z ∧
        Member (FW 15) (fillG cs sA 0 0 0 seedIs' arr lay decT recOf) o 0 0 y z (ofU cs sA 0 fun _ => 1) := by
  obtain ⟨f, hf⟩ := sent_of cs sA 0 ((fun _ => 1, fun _ => 0) : (portOmZ cs sA 0).Wit) (fun _ => ⟨fun _ => ⟨1, map_one _⟩, fun _ => ⟨0, map_zero _⟩⟩)
  have ρ₀ : (portOmZ cs sA 0).Z.D := Classical.arbitrary _
  have hu : ∀ (a : Unit) (ρ₁ : (portOmZ cs sA 0).Z.D) (v : (portOmZ cs sA 0).Z.S → GE) (ρ' : (portOmZ cs sA 0).Z.D) (v' : (portOmZ cs sA 0).Z.S → GE),
      (ρ₁ = ρ₀ ∧ v = (portOmZ cs sA 0).Z.val ρ₀ fun _ => 1) → (ρ' = ρ₀ ∧ v' = (portOmZ cs sA 0).Z.val ρ₀ fun _ => 1) →
      (portOmZ cs sA 0).Z.val ρ₁ = (portOmZ cs sA 0).Z.val ρ' ∧ v = v' := by
    rintro _ ρ₁ v ρ' v' ⟨rfl, rfl⟩ ⟨h, rfl⟩
    exact ⟨by rw [h], rfl⟩
  obtain ⟨y, _, o, z, h⟩ := fill_member_exists cs sA 0 0 0 (fun _ ρ₁ v => ρ₁ = ρ₀ ∧ v = (portOmZ cs sA 0).Z.val ρ₀ fun _ => 1) arr lay decT recOf (FW 15) fits1 hu (fun _ => none) ()
    f (fun _ => 1) (fun _ => 0) ρ₀ hf ⟨rfl, rfl⟩
  exact ⟨_, hu, y, o, z, h⟩

end VerifiableInference.Desc.Key.Fill.Toy

#print axioms VerifiableInference.Desc.Key.Fill.Toy.fits
#print axioms VerifiableInference.Desc.Key.Fill.Toy.not_fits
#print axioms VerifiableInference.Desc.Key.Fill.Toy.members
#print axioms VerifiableInference.Desc.Key.Fill.Toy.fits1
#print axioms VerifiableInference.Desc.Key.Fill.Toy.fill_member
