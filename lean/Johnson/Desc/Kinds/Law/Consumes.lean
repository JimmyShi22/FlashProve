-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Consumes.lean: A HEARING IS FIXED BY THE ROUNDS THAT IT CONSUMES; and three small tools for making one
rule on a block's rounds out of the rules of its stretches. No chance in it; it names no block and no seat.
  Consumes; consumes_...   where a hearing returns at a list of rounds, that list is what it consumed and what it
      left, and at the consumed rounds with any other list behind them it returns the same and leaves that list.
      Closed under bind; shown of every hearing of HeadParts.lean (round, stretch, hide, heardBy, sumcheck, level,
      drawPoint, sendThenBatch) and of Norm.lean's hearRest and hear.
  ceil_tail   a ceiling of the form "the last round's scalars and one" goes from a tail to the whole front.
  noBad_sub   a rule on the block's fronts that is b on the fronts of a stretch: no bad draw under it on the
      block's rounds: none under b on the stretch.
IMPORTED: Law/Cut.lean (Quiet and its closure; bind_eq); Law/Sum2b.lean (bind_some).

-/
import Mathlib
import Johnson.Desc.Kinds.Law.Cut

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E)
open OnBytes.Model (Fork)

/-! ## 1. A hearing is fixed by the rounds that it consumes -/

def Consumes {α : Type} (x : Hear α) : Prop :=
  ∀ F rs a G left, x F rs = some (a, G, left) →
    ∃ pre, rs = pre ++ left ∧ ∀ l, x F (pre ++ l) = some (a, G, l)

theorem consumes_bind {α β : Type} {x : Hear α} {f : α → Hear β} (hx : Consumes x)
    (hf : ∀ a, Consumes (f a)) : Consumes (x >>= f) := by
  intro F rs b G left h
  obtain ⟨a, G1, l1, h1, h2⟩ := bind_some h
  obtain ⟨p1, rfl, e1⟩ := hx _ _ _ _ _ h1
  obtain ⟨p2, rfl, e2⟩ := hf a _ _ _ _ _ h2
  refine ⟨p1 ++ p2, (List.append_assoc _ _ _).symm, fun l => ?_⟩
  rw [List.append_assoc, bind_eq (e1 (p2 ++ l))]
  exact e2 l

theorem consumes_of_quiet {α : Type} {x : Hear α} (h : Quiet x) : Consumes x := by
  intro F rs a G left hx
  obtain ⟨rfl, e⟩ := h _ _ _ _ _ hx
  exact ⟨[], rfl, fun l => e l⟩

theorem consumes_pure {α : Type} (a : α) : Consumes (pure a : Hear α) := consumes_of_quiet (quiet_pure a)
theorem consumes_need {α : Type} (x : Option α) : Consumes (Hear.need x) := consumes_of_quiet (quiet_need x)
theorem consumes_hide (v : List E) : Consumes (hide v) := consumes_of_quiet (quiet_hide v)

theorem consumes_round (n k : Nat) : Consumes (Hear.round n k) := by
  intro F rs a G left h
  unfold Hear.round at h
  cases rs with
  | nil => cases h
  | cons r l =>
    dsimp only at h
    cases hr : Part.MaskedSum.roundOf n k r with
    | none => rw [hr] at h; cases h
    | some v =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨[r], rfl, fun l' => ?_⟩
      show (Part.MaskedSum.roundOf n k r).map _ = _
      rw [hr]
      rfl

theorem consumes_stretch (n : Nat) : Consumes (Hear.stretch n) := by
  intro F rs a G left h
  unfold Hear.stretch at h
  split at h
  · cases h
  · rename_i hlt
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨rs.take n, (List.take_append_drop n rs).symm, fun l => ?_⟩
    have hl : (rs.take n).length = n := by rw [List.length_take]; omega
    unfold Hear.stretch
    rw [if_neg (by rw [List.length_append, hl]; omega),
      List.take_append_of_le_length (by omega), List.take_take, Nat.min_self,
      List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega), List.nil_append]

theorem consumes_heardBy (lead : Nat) (C : Array Hid → Form) (z : Point) (ends : Nat) :
    Consumes (heardBy lead C z ends) := by
  unfold heardBy
  refine consumes_bind (consumes_stretch _) fun rs => consumes_of_quiet ?_
  refine quiet_bind (quiet_need _) fun _ => quiet_bind (quiet_hide _) fun _ =>
    quiet_bind quiet_ledger fun _ => quiet_bind (quiet_need _) fun y => ?_
  obtain ⟨hd, G'⟩ := y
  exact quiet_bind (quiet_need _) fun _ => quiet_bind (quiet_lay _) fun _ =>
    quiet_bind (quiet_hiddenFrom _ _) fun _ => quiet_pure _

theorem consumes_sumcheck (z : Point) (ends : Nat) : Consumes (sumcheck z ends) := by
  unfold sumcheck
  refine consumes_bind (consumes_heardBy _ _ _ _) fun x => ?_
  obtain ⟨c, s⟩ := x
  exact consumes_pure _

theorem consumes_level (z : Point) (start : Form) : Consumes (level z start) := by
  unfold level
  refine consumes_bind (consumes_heardBy _ _ _ _) fun x => ?_
  obtain ⟨c, s⟩ := x
  refine consumes_bind (consumes_round 0 1) fun y => ?_
  obtain ⟨a, g⟩ := y
  exact consumes_bind (consumes_need _) fun _ => consumes_pure _

theorem consumes_drawPoint (n : Nat) : Consumes (drawPoint n) :=
  consumes_bind (consumes_round 0 n) fun _ => consumes_pure _

theorem consumes_sendThenBatch (n rows : Nat) : Consumes (sendThenBatch n rows) := by
  unfold sendThenBatch
  refine consumes_bind (consumes_round n 1) fun x => ?_
  obtain ⟨v, g⟩ := x
  exact consumes_bind (consumes_hide v) fun _ => consumes_bind (consumes_need _) fun _ => consumes_pure _

section Classes
variable [Sizes] [FinalNorm.In]

theorem consumes_normRest (pV : Point) : Consumes (Norm.hearRest pV) := by
  unfold Norm.hearRest
  refine consumes_bind (consumes_sendThenBatch _ _) fun x => ?_
  obtain ⟨W, gam⟩ := x
  refine consumes_bind ?_ fun rhoI => consumes_bind (consumes_level _ _) fun _ =>
    consumes_bind (consumes_sendThenBatch _ _) fun y => ?_
  · first
      | exact consumes_pure _
      | (split
         · exact consumes_pure _
         · exact consumes_drawPoint _)
  · obtain ⟨P, om⟩ := y
    exact consumes_bind (consumes_sumcheck _ _) fun _ => consumes_pure _

theorem consumes_norm : Consumes Norm.hear :=
  consumes_bind (consumes_drawPoint _) fun _ => consumes_normRest _

end Classes

/-! ## 2. From a stretch's rule to the block's -/

theorem getLast_append_ne {α : Type} (p l : List α) (h : l ≠ []) :
    (p ++ l).getLast? = l.getLast? := by
  rw [List.getLast?_append]
  cases hl : l.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.1 hl) h
  | some x => rfl

/-- A ceiling of the form "the last round's scalars and one" goes from a tail to the whole front. -/
theorem ceil_tail (b : List Fmt.RoundView → List E)
    (hb : ∀ h, (b h).length ≤ ((h.getLast?.map fun r => r.vals.length).getD 0) + 1)
    (p l : List Fmt.RoundView) :
    (b l).length ≤ (((p ++ l).getLast?.map fun r => r.vals.length).getD 0) + 1 := by
  by_cases hl : l = []
  · subst hl
    have h0 := hb []
    simp only [List.getLast?_nil, Option.map_none, Option.getD_none] at h0
    omega
  · rw [getLast_append_ne p l hl]
    exact hb l

/-- A rule on the block's fronts that is b on the fronts of a stretch. -/
theorem noBad_sub {rule b : List Fmt.RoundView → List E} {pre t post : List Fmt.RoundView}
    (he : ∀ i r, t[i]? = some r →
      rule (pre ++ (t.take i ++ [{ r with drawn := ⟨[], [], [], none⟩ }]))
        = b (t.take i ++ [{ r with drawn := ⟨[], [], [], none⟩ }]))
    (h : NoBad rule (pre ++ t ++ post)) : NoBad b t := by
  intro i r hi x hx
  have hil : i < t.length := (List.getElem?_eq_some_iff.mp hi).1
  have h1 : (pre ++ t ++ post)[pre.length + i]? = some r := by
    rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left hil]
    exact hi
  have h2 := h (pre.length + i) r h1 x hx
  have h3 : (pre ++ t ++ post).take (pre.length + i) = pre ++ t.take i := by
    rw [List.append_assoc, List.take_append, List.take_of_length_le (by omega),
      Nat.add_sub_cancel_left, List.take_append, Nat.sub_eq_zero_of_le (Nat.le_of_lt hil),
      List.take_zero, List.append_nil]
  rw [h3, List.append_assoc, he i r hi] at h2
  exact h2

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.consumes_norm
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.consumes_level
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.noBad_sub
