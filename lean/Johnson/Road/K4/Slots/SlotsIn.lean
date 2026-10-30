-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Slots/SlotsIn.lean: WHICH SLOTS A FORM NAMES, through the operations by which forms
are made: the twin, for slots, of Johnson/Road/K4/Reads/EntsIn.lean (which entries a form names). A
definition, statements and proofs.

`SlotsIn S f`: each slot that the form f names has S. The rules: `slotsIn_mono`, `slotsIn_ofConst`,
`slotsIn_slot`, `slotsIn_empty`, `slotsIn_ent`, `slotsIn_addMul`, `slotsIn_scale`, `slotsIn_add`,
`slotsIn_sub`, `slotsIn_foldl`, `slotsIn_foldl_mem`; `slotsIn_addSlots` (a run of slots from `first`
on);
`slotsIn_rowForm`: THE CLAIM THAT A SUMCHECK LEAVES (`Psc.rowForm`) names the slots of its window
(from `p.first` on, as many as `p.walk.1` has members), those of its start form and those of what
is kept.

Limits. No form of a sub-proof is treated here. One direction: a form may name fewer slots. Nothing
on whether a slot is filled. Nothing on soundness.
-/
import OnBytes.Tie.Pv.Led.LedAdds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Slots
open OnBytes OnBytes.Model
open OnBytes.Road.Rows

/-- Each slot that the form names has S. -/
def SlotsIn (S : Nat → Prop) (f : Aff) : Prop := ∀ x ∈ f.slots.toList, S x.1

variable {S : Nat → Prop}

theorem slotsIn_mono {S' : Nat → Prop} (h : ∀ j, S j → S' j) {f : Aff} (a : SlotsIn S f) :
    SlotsIn S' f := fun x hx => h _ (a x hx)

theorem slotsIn_ofConst (v : E) : SlotsIn S (Aff.ofConst v) := fun x hx => by
  simp [Aff.ofConst] at hx

theorem slotsIn_slot {j : Nat} (h : S j) : SlotsIn S (Aff.slot j) := fun x hx => by
  have e : x = (j, oneE) := by simpa [Aff.slot] using hx
  rw [e]
  exact h

theorem slotsIn_empty : SlotsIn S ({} : Aff) := fun x hx => by
  simp at hx

theorem slotsIn_ent (t r i : Nat) : SlotsIn S (Aff.ent t r i) := fun x hx => by
  simp [Aff.ent] at hx

theorem slotsIn_addMul {a b : Aff} (k : E) (ha : SlotsIn S a) (hb : SlotsIn S b) :
    SlotsIn S (Aff.addMul a b k) := fun y hy => by
  simp only [Aff.addMul, foldl_push_toList, List.mem_append, List.mem_map] at hy
  rcases hy with hy | ⟨x, hx, rfl⟩
  · exact ha y hy
  · exact hb x hx

theorem slotsIn_scale {a : Aff} (k : E) (ha : SlotsIn S a) : SlotsIn S (Aff.scale a k) :=
  slotsIn_addMul k slotsIn_empty ha

theorem slotsIn_add {a b : Aff} (ha : SlotsIn S a) (hb : SlotsIn S b) : SlotsIn S (a + b) :=
  slotsIn_addMul oneE ha hb

theorem slotsIn_sub {a b : Aff} (ha : SlotsIn S a) (hb : SlotsIn S b) : SlotsIn S (a - b) :=
  slotsIn_addMul (subE zeroE oneE) ha hb

/-- A sum over a list. -/
theorem slotsIn_foldl {α : Type} (step : Aff → α → Aff)
    (hs : ∀ f x, SlotsIn S f → SlotsIn S (step f x)) :
    ∀ (l : List α) (f : Aff), SlotsIn S f → SlotsIn S (l.foldl step f)
  | [], _, h => h
  | x :: l, f, h => slotsIn_foldl step hs l (step f x) (hs f x h)

/-- A sum over a list, the step's law asked at the list's members alone. -/
theorem slotsIn_foldl_mem {α : Type} (step : Aff → α → Aff) :
    ∀ (l : List α), (∀ f, ∀ x ∈ l, SlotsIn S f → SlotsIn S (step f x)) →
      ∀ (f : Aff), SlotsIn S f → SlotsIn S (l.foldl step f)
  | [], _, _, h => h
  | x :: l, hs, f, h =>
    slotsIn_foldl_mem step l (fun f y hy => hs f y (List.mem_cons_of_mem _ hy)) (step f x)
      (hs f x List.mem_cons_self h)

/-- A run of slots from `first` on. -/
theorem slotsIn_addSlots {a : Aff} (first : Nat) (form : Array E) (ha : SlotsIn S a)
    (hw : ∀ i, i < form.size → S (first + i)) : SlotsIn S (addSlots a first form) := by
  unfold addSlots
  rw [← Array.foldl_toList]
  have key : ∀ (l : List E) (s : Nat × Aff), SlotsIn S s.2 → (∀ i, i < l.length → S (s.1 + i)) →
      SlotsIn S (l.foldl addSlot s).2 := by
    intro l
    induction l with
    | nil => exact fun _ h _ => h
    | cons x l ih =>
      rintro ⟨j, u⟩ h hj
      refine ih (j + 1, Aff.addMul u (Aff.slot j) x)
        (slotsIn_addMul x h (slotsIn_slot (hj 0 (Nat.succ_pos _)))) fun i hi => ?_
      have e : j + 1 + i = j + (i + 1) := by omega
      show S (j + 1 + i)
      rw [e]
      exact hj (i + 1) (Nat.succ_lt_succ hi)
  exact key _ _ ha (by simpa using hw)

/-- **The claim that a sumcheck leaves.** -/
theorem slotsIn_rowForm (p : Psc) (S0 : E) {kept : Aff}
    (hw : ∀ i, i < p.walk.1.length → S (p.first + i)) (hs : SlotsIn S p.start)
    (hk : SlotsIn S kept) : SlotsIn S (p.rowForm S0 kept) := by
  unfold Psc.rowForm
  exact slotsIn_addMul _ (slotsIn_addMul _
    (slotsIn_addSlots _ _ (slotsIn_ofConst _) (by simpa using hw))
    (slotsIn_sub (slotsIn_ofConst _) hs)) hk

end OnBytes.Desc.First.K4.Slots

#print axioms OnBytes.Desc.First.K4.Slots.slotsIn_rowForm
