-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyFillBaseAt.lean: A SHEET TO Johnson/RunOne/KeyFillBase.lean: THE TABLES' OTHER READER AT M := Tab; THE JOINT's PUBLIC PREMISES AT THE SIX; A CONTROL AT THE TOY.
  readE · kreadFam · read_val · sameLaws_fam · readsPinned_fam   KRead at M := Tab: val := the canonical words of the table's entry · same := «read as one element of the field» (toE of the triple) · of := the table that PIN pins; tab: a letter.
                      SameLaws holds of that same: sameLaws_of_read (Johnson/Desc/Key/KeySumRead.lean) at addE_triple | mulE_triple | toE_addE | toE_mulE: AT ALL WORDS, below the prime or not
  orc_fam             AtFk.orc is met by definition
  numSix · atSix · seat_inj_six · shapesApart_six · arrOk_six…   at the library's six shapes (six, Johnson/Desc/Key/KeyFillAtSizes.lean) and the seats (0,0) (1,0) (5,0) (6,0) (7,0) (8,0) [THE SEATS ARE TYPED HERE BY HAND, from an evaluation of the description: NOT HELD AGAINST IT HERE]
  shapes_plant        A PLANT: one shape twice: ShapesApart is false
  plan₁_orc_none · all_six_empty₁   THE FIRST CHAIN's PLAN GIVES THE NUMBERS 3 | 4 | 5 NOTHING: so at the six, at orc₁ := that plan's (which AtFk.orc forces), no record of the first chain holds the sample of the last three members: «EVERY MEMBER AT ONCE» IS UNMEETABLE THERE: hence the set I
  Toy.promise_h₁      A CONTROL: at the toy of KeyFillToy.lean and A REAL VALUE OF THE FIRST CHAIN's STATE (its start, with two messages of the members' shapes laid into the statement): PIN ∧ hasSmp ∧ NoColl at both seats AT B.h₁: for every instance x and every maker's record b; ToyB.there: both types have a value; promise_h₁_closed: at these.
  ToyB.orcP · promise_part · second_never   THE SAME WITH A PARTIAL orc₁ (number 0 alone), AS AT THE REAL LETTERS: I := the first member: closed · A PLANT: the second member's sample is in no record
                      A THEOREM OF EXISTENCE; rowIs there reads no record and IS MADE OF THE VERY MESSAGE AND SEED THAT IT IS TO WITNESS («meets» by fiat); the toy is no protocol's description; the state is no state of a run
OBJECT: KRead (Johnson/Desc/Key/KeyWords.lean) | BaseSt.h₁ (Johnson/RunOne/KeyOneReading.lean); the library's six shapes · USER: none: a sheet · LETTERS: tab · decT · recOf.
Nothing on soundness.
-/
import Johnson.RunOne.KeyFillBase
import Johnson.Desc.Key.KeySumRead
import OnBytes.Field.ExtEq
import Johnson.RunOne.KeyReaders1

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyRows23
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.Key (Xi FirstState)
open Cb Johnson.Pack OnBytes.Maker OnBytes.Slice

/-! ## The tables' other reader -/

/-- A machine element, read as an element of the field. -/
def readE (a : OnBytes.E) : GE := toE a.triple

theorem readE_add (a b : OnBytes.E) : readE (OnBytes.addE a b) = readE a + readE b := by
  unfold readE
  rw [OnBytes.addE_triple, toE_addE]

theorem readE_mul (a b : OnBytes.E) : readE (OnBytes.mulE a b) = readE a * readE b := by
  unfold readE
  rw [OnBytes.mulE_triple, toE_mulE]

theorem sameLaws_fam : SameLaws fun a b => readE a = readE b := sameLaws_of_read readE readE_add readE_mul

section
variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) (num : Fin l.length → ℕ) (at_ : Where) {Cells Rec : Type}

/-- **KRead at M := Tab.** -/
def kreadFam (tab : Cells → ℕ → ℕ → OnBytes.F) : KRead Cells Tab where
  tab := tab
  val := fun m part i => OnBytes.E.ofTriple (ofE (m part i))
  of := ofFam cs l num at_
  same := fun a b => readE a = readE b

theorem read_val (tab : Cells → ℕ → ℕ → OnBytes.F) (m : Tab) (part : OnBytes.Part) (i : ℕ) : readE ((kreadFam cs l num at_ tab).val m part i) = m part i := by
  show toE (OnBytes.E.ofTriple (ofE (m part i))).triple = m part i
  exact toE_ofE (m part i)

variable (rowIs : ∀ i : Fin l.length, ℕ → OnBytes.Oracle → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec) (orc₁ : ℕ → Option ℕ)

theorem readsPinned_fam (tab : Cells → ℕ → ℕ → OnBytes.F) (ks : List ℕ) :
    ReadsPinned (baseFam cs l num at_ rowIs decT recOf orc₁).h₁ at_ (kreadFam cs l num at_ tab) ks ∧
    ReadsPinned (baseFam cs l num at_ rowIs decT recOf orc₁).h₂ at_ (kreadFam cs l num at_ tab) ks ∧
    ReadsPinned (baseFam cs l num at_ rowIs decT recOf orc₁).h₃ at_ (kreadFam cs l num at_ tab) ks :=
  ⟨readsPinned_h₁ cs l num at_ rowIs decT recOf orc₁ _ rfl ks, readsPinned_h₂ cs l num at_ rowIs decT recOf orc₁ _ rfl ks, readsPinned_h₃ cs l num at_ rowIs decT recOf orc₁ _ rfl ks⟩

theorem orc_fam : (baseFam cs l num at_ rowIs decT recOf orc₁).orc₁ = orc₁ := rfl

end

/-! ## At the six -/

def numSix : Fin six.length → ℕ := fun i => i.val

/-- The six seats, by the tables' numbers. TYPED BY HAND. -/
def atSix : Where := fun k => match k with
  | 0 => (0, 0)
  | 1 => (1, 0)
  | 2 => (5, 0)
  | 3 => (6, 0)
  | 4 => (7, 0)
  | _ => (8, 0)

theorem seat_inj_six : Function.Injective (seatAt six numSix atSix) := by
  show ∀ a b : Fin six.length, seatAt six numSix atSix a = seatAt six numSix atSix b → a = b
  decide +kernel

theorem shapesApart_six : ShapesApart six := by
  show ∀ i i' : Fin six.length, (six.get i).1 = (six.get i').1 → i = i'
  decide +kernel

/-- A PLANT. -/
theorem shapes_plant : ¬ ShapesApart [(Toy.sA, 0), (Toy.sA, 1)] := fun h => by
  have e : (⟨0, by decide⟩ : Fin [(Toy.sA, 0), (Toy.sA, 1)].length) = ⟨1, by decide⟩ := h _ _ rfl
  exact absurd (congrArg Fin.val e) (by decide)

section
variable {Cells Rec : Type} (rowIs : ∀ i : Fin six.length, ℕ → OnBytes.Oracle → (OmAt Johnson.Top.H.csKey six i).Z.D → ((OmAt Johnson.Top.H.csKey six i).Z.S → GE) → Prop)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec) (orc₁ : ℕ → Option ℕ)

theorem num_six (k : ℕ) (hk : k < 6) : ∃ i, numSix i = k := ⟨⟨k, hk⟩, rfl⟩

/-- FirstLetters.arr. -/
theorem arrOk_six₁ : ArrOk (baseFam Johnson.Top.H.csKey six numSix atSix rowIs decT recOf orc₁).h₁ atSix [0, 1, 2] :=
  arrOk_h₁ _ six numSix atSix rowIs decT recOf orc₁ seat_inj_six _ fun k hk => num_six k (by
    have : ∀ k ∈ [0, 1, 2], k < 6 := by decide
    exact this k hk)

/-- AtFk.arr | Free₂.arr. -/
theorem arrOk_six₂ : ArrOk (baseFam Johnson.Top.H.csKey six numSix atSix rowIs decT recOf orc₁).h₂ atSix [0, 2, 3, 4, 5] :=
  arrOk_h₂ _ six numSix atSix rowIs decT recOf orc₁ seat_inj_six _ fun k hk => num_six k (by
    have : ∀ k ∈ [0, 2, 3, 4, 5], k < 6 := by decide
    exact this k hk)

/-- The first chain's plan gives the tables' numbers from 3 on nothing. -/
theorem plan₁_orc_none (one : OnBytes.Params.OneTime) (k : ℕ) (hk : 3 ≤ k) : (KeyRows1.plan₁ one).orc k = none := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
  rfl

/-- **AT THE SIX, AT THE FIRST CHAIN's OWN PLAN, «EVERY MEMBER AT ONCE» IS UNMEETABLE**: no record holds the sample of a member with a number from 3 on. -/
theorem all_six_empty₁ (one : OnBytes.Params.OneTime) (i : Fin six.length) (hi : 3 ≤ numSix i) (a : Xi × FirstState) (ρ : (OmAt Johnson.Top.H.csKey six i).Z.D)
    (v : (OmAt Johnson.Top.H.csKey six i).Z.S → GE) : ¬ seedIsS Johnson.Top.H.csKey six numSix rowIs (src₁ (KeyRows1.plan₁ one).orc) i a ρ v :=
  not_seedIsS₁ _ six numSix rowIs _ i (plan₁_orc_none one _ hi) a ρ v

end

/-! ## The toy -/

namespace ToyB
open VerifiableInference.Desc.Key.Fill.Toy

def num : Fin l.length → ℕ := fun i => i.val
def at_ : Where := fun k => (0, 2 * k)

/-- A value of the first chain's state: its start at the toy's codes, with two messages of the members' shapes laid into the statement. -/
def s₀ (b : LookupRecord) : FirstState :=
  { chainStart cs b with d := { (chainStart cs b).d with st := { codes := cs, oracles := #[{ shape := sA }, { shape := sB }] } } }

theorem apartT : ShapesApart l := by
  show ∀ i i' : Fin l.length, (l.get i).1 = (l.get i').1 → i = i'
  decide +kernel

/-- **A CONTROL: PIN · hasSmp · NoColl AT BOTH SEATS AT B.h₁, at a value of the first chain's state.** -/
theorem promise_h₁ {Rec : Type} (x : Xi) (b : LookupRecord) (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Unit) (recOf : Xi → Option Rec) :
    ∃ rowIs : ∀ i : Fin l.length, ℕ → OnBytes.Oracle → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop,
      (∀ i o x ρ v ρ' v', rowIs i o x ρ v → rowIs i o x ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v') ∧
      ∃ (W : Wit Unit Unit Tab) (y' : (FrD 1).E.Str), ∀ i : Fin l.length,
        PIN (FW 15) (baseFam cs l num at_ rowIs decT recOf some).h₁ (at_ (num i)).1 (at_ (num i)).2 (x, s₀ b) (Sound.strsOf (FrD 1) y') W ∧
        hasSmp (baseFam cs l num at_ rowIs decT recOf some).h₁ (at_ (num i)).1 (at_ (num i)).2 (x, s₀ b) = true ∧
        NoColl (FW 15) (baseFam cs l num at_ rowIs decT recOf some).h₁ (at_ (num i)).1 (at_ (num i)).2 (x, s₀ b) (Sound.strsOf (FrD 1) y') := by
  have ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D := fun _ => Classical.arbitrary _
  have hu : ∀ (i : Fin l.length) (o : ℕ) (x : OnBytes.Oracle) (ρ₁ : (OmAt cs l i).Z.D) (v : (OmAt cs l i).Z.S → GE) (ρ' : (OmAt cs l i).Z.D) (v' : (OmAt cs l i).Z.S → GE),
      (ρ₁ = ρ i ∧ v = (OmAt cs l i).Z.val (ρ i) fun _ => 1) → (ρ' = ρ i ∧ v' = (OmAt cs l i).Z.val (ρ i) fun _ => 1) →
      (OmAt cs l i).Z.val ρ₁ = (OmAt cs l i).Z.val ρ' ∧ v = v' := by
    rintro i _ _ ρ₁ v ρ' v' ⟨rfl, rfl⟩ ⟨h, rfl⟩
    exact ⟨by rw [h], rfl⟩
  refine ⟨fun i _ _ ρ₁ v => ρ₁ = ρ i ∧ v = (OmAt cs l i).Z.val (ρ i) fun _ => 1, hu, ?_⟩
  obtain ⟨W, y', _, h⟩ := KeyRows23.promise_h₁ cs l num at_ (fun i _ _ ρ₁ v => ρ₁ = ρ i ∧ v = (OmAt cs l i).Z.val (ρ i) fun _ => 1) decT recOf some (FW 15) (fun _ => True) (FrD 1) seat_inj apartT
    Fin.val_injective fits holds hu meets ((fun _ => (0, []), fun _ => []) : (FrD 1).E.Str) (x, s₀ b) (fun _ _ => 1) (fun _ _ => 0) ρ
    (fun _ _ => ⟨fun _ => ⟨1, map_one _⟩, fun _ => ⟨0, map_zero _⟩⟩)
    (by
      rintro ⟨k, hk⟩ _
      have hk' : k < 2 := hk
      interval_cases k
      · exact ⟨0, { shape := sA }, rfl, rfl, rfl, rfl⟩
      · exact ⟨1, { shape := sB }, rfl, rfl, rfl, rfl⟩) ()
  exact ⟨W, y', fun i => h i trivial⟩

/-- The two letters x and b of the control have values. -/
theorem there : Nonempty (Xi × LookupRecord) := ⟨(⟨{}⟩, {})⟩

/-- **THE CONTROL, CLOSED**: at the instance with the empty key and the empty maker's record. -/
theorem promise_h₁_closed : ∃ rowIs : ∀ i : Fin l.length, ℕ → OnBytes.Oracle → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop,
      (∀ i o x ρ v ρ' v', rowIs i o x ρ v → rowIs i o x ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v') ∧
      ∃ (W : Wit Unit Unit Tab) (y' : (FrD 1).E.Str), ∀ i : Fin l.length,
        PIN (FW 15) (baseFam (Rec := Unit) cs l num at_ rowIs (fun _ _ => none) (fun _ => none) some).h₁ (at_ (num i)).1 (at_ (num i)).2 (⟨{}⟩, s₀ {}) (Sound.strsOf (FrD 1) y') W ∧
        hasSmp (baseFam (Rec := Unit) (Cells := Unit) cs l num at_ rowIs (fun _ _ => none) (fun _ => none) some).h₁ (at_ (num i)).1 (at_ (num i)).2 (⟨{}⟩, s₀ {}) = true ∧
        NoColl (FW 15) (baseFam (Rec := Unit) (Cells := Unit) cs l num at_ rowIs (fun _ _ => none) (fun _ => none) some).h₁ (at_ (num i)).1 (at_ (num i)).2 (⟨{}⟩, s₀ {}) (Sound.strsOf (FrD 1) y') :=
  promise_h₁ ⟨{}⟩ {} (fun _ _ => none) (fun _ => none)

/-- A partial plan, as the real first chain's is: the number 0 alone. -/
def orcP : ℕ → Option ℕ := fun k => if k = 0 then some 0 else none

/-- **THE CONTROL WITH A PARTIAL PLAN, CLOSED**: I := the first member. -/
theorem promise_part : ∃ rowIs : ∀ i : Fin l.length, ℕ → OnBytes.Oracle → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop,
      (∀ i o x ρ v ρ' v', rowIs i o x ρ v → rowIs i o x ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v') ∧
      ∃ (W : Wit Unit Unit Tab) (y' : (FrD 1).E.Str), ∀ i : Fin l.length, i.val = 0 →
        PIN (FW 15) (baseFam (Rec := Unit) cs l num at_ rowIs (fun _ _ => none) (fun _ => none) orcP).h₁ (at_ (num i)).1 (at_ (num i)).2 (⟨{}⟩, s₀ {}) (Sound.strsOf (FrD 1) y') W ∧
        hasSmp (baseFam (Rec := Unit) (Cells := Unit) cs l num at_ rowIs (fun _ _ => none) (fun _ => none) orcP).h₁ (at_ (num i)).1 (at_ (num i)).2 (⟨{}⟩, s₀ {}) = true ∧
        NoColl (FW 15) (baseFam (Rec := Unit) (Cells := Unit) cs l num at_ rowIs (fun _ _ => none) (fun _ => none) orcP).h₁ (at_ (num i)).1 (at_ (num i)).2 (⟨{}⟩, s₀ {}) (Sound.strsOf (FrD 1) y') := by
  have ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D := fun _ => Classical.arbitrary _
  have hu : ∀ (i : Fin l.length) (o : ℕ) (x : OnBytes.Oracle) (ρ₁ : (OmAt cs l i).Z.D) (v : (OmAt cs l i).Z.S → GE) (ρ' : (OmAt cs l i).Z.D) (v' : (OmAt cs l i).Z.S → GE),
      (ρ₁ = ρ i ∧ v = (OmAt cs l i).Z.val (ρ i) fun _ => 1) → (ρ' = ρ i ∧ v' = (OmAt cs l i).Z.val (ρ i) fun _ => 1) →
      (OmAt cs l i).Z.val ρ₁ = (OmAt cs l i).Z.val ρ' ∧ v = v' := by
    rintro i _ _ ρ₁ v ρ' v' ⟨rfl, rfl⟩ ⟨h, rfl⟩
    exact ⟨by rw [h], rfl⟩
  refine ⟨fun i _ _ ρ₁ v => ρ₁ = ρ i ∧ v = (OmAt cs l i).Z.val (ρ i) fun _ => 1, hu, ?_⟩
  obtain ⟨W, y', _, h⟩ := KeyRows23.promise_h₁ cs l num at_ (fun i _ _ ρ₁ v => ρ₁ = ρ i ∧ v = (OmAt cs l i).Z.val (ρ i) fun _ => 1) (fun _ _ => none) (fun _ => none) orcP (FW 15)
    (fun i => i.val = 0) (FrD 1) seat_inj apartT
    Fin.val_injective fits holds hu meets ((fun _ => (0, []), fun _ => []) : (FrD 1).E.Str) (⟨{}⟩, s₀ {}) (fun _ _ => 1) (fun _ _ => 0) ρ
    (fun _ _ => ⟨fun _ => ⟨1, map_one _⟩, fun _ => ⟨0, map_zero _⟩⟩)
    (by
      rintro ⟨k, hk⟩ (h0 : k = 0)
      subst h0
      exact ⟨0, { shape := sA }, rfl, rfl, rfl, rfl⟩) ()
  exact ⟨W, y', h⟩

/-- **A PLANT: at the partial plan the second member's sample is in no record**: so «every member at once» cannot be met there. -/
theorem second_never (rowIs : ∀ i : Fin l.length, ℕ → OnBytes.Oracle → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop) (a : Xi × FirstState)
    (ρ : (OmAt cs l ⟨1, by decide⟩).Z.D) (v : (OmAt cs l ⟨1, by decide⟩).Z.S → GE) : ¬ seedIsS cs l num rowIs (src₁ orcP) ⟨1, by decide⟩ a ρ v :=
  not_seedIsS₁ cs l num rowIs orcP ⟨1, by decide⟩ rfl a ρ v

end ToyB

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.sameLaws_fam
#print axioms Johnson.RunOne.KeyRows23.read_val
#print axioms Johnson.RunOne.KeyRows23.readsPinned_fam
#print axioms Johnson.RunOne.KeyRows23.orc_fam
#print axioms Johnson.RunOne.KeyRows23.seat_inj_six
#print axioms Johnson.RunOne.KeyRows23.shapesApart_six
#print axioms Johnson.RunOne.KeyRows23.shapes_plant
#print axioms Johnson.RunOne.KeyRows23.arrOk_six₁
#print axioms Johnson.RunOne.KeyRows23.arrOk_six₂
#print axioms Johnson.RunOne.KeyRows23.ToyB.apartT
#print axioms Johnson.RunOne.KeyRows23.ToyB.promise_h₁
#print axioms Johnson.RunOne.KeyRows23.ToyB.there
#print axioms Johnson.RunOne.KeyRows23.ToyB.promise_h₁_closed
#print axioms Johnson.RunOne.KeyRows23.plan₁_orc_none
#print axioms Johnson.RunOne.KeyRows23.all_six_empty₁
#print axioms Johnson.RunOne.KeyRows23.ToyB.promise_part
#print axioms Johnson.RunOne.KeyRows23.ToyB.second_never
