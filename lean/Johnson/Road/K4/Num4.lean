-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/Num4.lean: A NUMBERING OF THE END VALUES OF THE BATCHED SUMCHECK OF A LAYERS'
SUB-PROOF's OWN ROUNDS, IN THE ORDER IN WHICH K4's TEXT HEARS THEM, and that it meets what
Johnson/Road/K4/ClaimsHeard.lean asks of a numbering (`Nums4`); AND THE NUMBERINGS OF ALL SEVEN
SUMCHECKS' END VALUES, as one record. Definitions and short statements.

K4's text (`hearStack`, OnBytes/Desc/First/K4/Hear.lean) lays the values that the round of the end
values sent under slots that follow one another: the first side's own value (sA0); the gated
products' (sH1); the routed experts', one for each layer with experts; the second side's own value
(sB0); the weight claims' (from sV on).

  `panA`: 1 for the panel D, 2 + l for the panel Dr l.
  `num4 D num`, `num4K V` (at the value's sizes and numbering): on the library's names
    `IA D ⊕ IB D` of these values: 0 · `panA` of the panel ·
    2 + ne · 2 + (1 + ne) + the claim's number in the value's own numbering `V.num`.
  `nums4_num4K`: `Nums4 V (num4K V)`.
  `num4K_lt`: every number is below 2 + (1 + ne) + nW.
  `num4K_inj`: no two names have one number.
  `numsK V`: the record `TailNums` (OnBytes/Desc/First/P1/OwnMapsPlan.lean) at the value's chain: a
    product layer's two end values: false 0, true 1; the row products': field k of norm ν has
    number 4 ν + k (`finProdFinEquiv`); the terms': `numA` (Cb/Pv/Lay/End/TermsPay.lean);
    the batched sumcheck's: `num4K`; the merge's one value: 0. `nums4_numsK`.

Limits. That the value's own numbering `V.num` of the weight claims is the order in which K4's text
lists its claims is NOT said: V.num is a letter of the value. Numbers alone.
-/
import Johnson.Road.K4.ClaimsHeard
import Cb.Pv.Lay.End.TermsPay
import OnBytes.Desc.First.P1.OwnMapsPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes.Slice
open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (Pan Dim)

/-- The number of a never-sent vector's value, by its panel. -/
def panA : Pan → ℕ
  | .D => 1
  | .Dr l => 2 + l
  | _ => 0

/-! ### At any sizes and any numbering of the weight claims -/

section General
variable (D : Dim) {nW : ℕ} (num : Fin nW ≃ Piece D)

/-- The numbering, at sizes D and a numbering num of the weight claims. -/
def num4 : IA D ⊕ IB D → ℕ :=
  Sum.elim (Sum.elim (fun _ => 0) fun a => panA a.1.1)
    (Sum.elim (fun _ => 2 + D.ne) fun pc => 2 + (1 + D.ne) + (num.symm pc).val)

/-- On the first side's names. -/
theorem num4_inl (a : IA D) :
    (a = .inl () ∧ num4 D num (.inl a) = 0) ∨ (a = aH1 D ∧ num4 D num (.inl a) = 1) ∨
      ∃ i : Fin D.ne, a = aH2 D i ∧ num4 D num (.inl a) = 2 + i.val := by
  rcases ia_cases D a with rfl | rfl | ⟨i, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨i, rfl, rfl⟩)

/-- On the second side's names. -/
theorem num4_inr (b : IB D) :
    (b = .inl () ∧ num4 D num (.inr b) = 2 + D.ne) ∨
      ∃ pc : Piece D, b = .inr pc ∧ num4 D num (.inr b) = 2 + (1 + D.ne) + (num.symm pc).val := by
  rcases b with _ | pc
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨pc, rfl, rfl⟩

/-- Every number is below the number of the values. -/
theorem num4_lt (a : IA D ⊕ IB D) : num4 D num a < 2 + (1 + D.ne) + nW := by
  rcases a with a | b
  · rcases num4_inl D num a with ⟨_, h⟩ | ⟨_, h⟩ | ⟨i, _, h⟩
    · omega
    · omega
    · have := i.isLt
      omega
  · rcases num4_inr D num b with ⟨_, h⟩ | ⟨pc, _, h⟩
    · omega
    · have := (num.symm pc).isLt
      omega

/-- No two names have one number. -/
theorem num4_inj : Function.Injective (num4 D num) := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b
  · rcases num4_inl D num a with ⟨rfl, ha⟩ | ⟨rfl, ha⟩ | ⟨i, rfl, ha⟩ <;>
      rcases num4_inl D num b with ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨j, rfl, hb⟩
    · rfl
    · omega
    · omega
    · omega
    · rfl
    · omega
    · omega
    · omega
    · have e : i = j := Fin.ext (by omega)
      rw [e]
  · exfalso
    rcases num4_inl D num a with ⟨_, ha⟩ | ⟨_, ha⟩ | ⟨i, _, ha⟩ <;>
      rcases num4_inr D num b with ⟨_, hb⟩ | ⟨pc, _, hb⟩ <;>
      omega
  · exfalso
    rcases num4_inl D num b with ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨i, _, hb⟩ <;>
      rcases num4_inr D num a with ⟨_, ha⟩ | ⟨pc, _, ha⟩ <;>
      omega
  · rcases num4_inr D num a with ⟨rfl, ha⟩ | ⟨pa, rfl, ha⟩ <;>
      rcases num4_inr D num b with ⟨rfl, hb⟩ | ⟨pb, rfl, hb⟩
    · rfl
    · omega
    · omega
    · have e : num.symm pa = num.symm pb := Fin.ext (by omega)
      rw [num.symm.injective e]

end General

/-! ### At the value -/

variable [scl : Scl] {M X0 : Type} (V : FullPar GE M X0)

/-- **The numbering, in the order in which K4's text hears the values.** -/
noncomputable def num4K : IA V.D ⊕ IB V.D → ℕ := num4 V.D V.num

/-- **It meets what the claims ask.** -/
theorem nums4_num4K : Nums4 V (num4K V) where
  h1 := rfl
  h2 := fun _ => rfl
  h3 := fun a => by
    show 2 + (1 + V.D.ne) + (V.num.symm (V.num a)).val = _
    rw [Equiv.symm_apply_apply]

/-- Every number is below the number of the values. -/
theorem num4K_lt (a : IA V.D ⊕ IB V.D) : num4K V a < 2 + (1 + V.D.ne) + V.nW :=
  num4_lt V.D V.num a

/-- No two names have one number. -/
theorem num4K_inj : Function.Injective (num4K V) := num4_inj V.D V.num

/-- **The numberings of all seven sumchecks' end values.** -/
noncomputable def numsK : OnBytes.Desc.First.P1.TailNums V.own.toOwn.tail where
  n1 := fun b : Bool => if b then 1 else 0
  n2 := fun q : Fin V.D.nNu × Fin 4 => (finProdFinEquiv q : ℕ)
  n3 := Cb.Pv.Lay.End.numA V.D
  n4 := num4K V
  n5 := fun b : Bool => if b then 1 else 0
  n6 := fun b : Bool => if b then 1 else 0
  n7 := fun _ => 0

/-- Its fourth member meets what the claims ask. -/
theorem nums4_numsK : Nums4 V (numsK V).n4 := nums4_num4K V

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.nums4_numsK
#print axioms OnBytes.Road.K4.nums4_num4K
#print axioms OnBytes.Road.K4.num4K_lt
#print axioms OnBytes.Road.K4.num4K_inj
