-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- Johnson/Desc/First/Att/Door/ShapeSame.lean: A YES OF THE TEST ON TWO SHAPES (sameShapeAll, Johnson/Desc/First/Look/K3Borders.lean: "every field, by the whole constructor") GIVES THAT THE TWO SHAPES ARE ONE. So a yes of look m's Bool at an attention segment (lookAttB) gives: the two homes of what the lookup on the calls returned hold ONE SHAPE: whatever reads the shape alone (the pad's three) reads one thing. No Mathlib.
import Johnson.Desc.First.Att.Door.LookGives

set_option autoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K3 (sameCall sameShapeAll)

theorem sameCall_eq {a b : Call} (h : sameCall a b = true) : a = b := by
  cases a
  cases b
  simp only [sameCall, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  rfl

theorem list_eq_of_zip {α : Type} (f : α → α → Bool) (hf : ∀ a b, f a b = true → a = b) :
    ∀ (l l' : List α), l.length = l'.length → (l.zip l').all (fun x => f x.1 x.2) = true → l = l'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l, b :: l', h, hz => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hz
    rw [hf a b hz.1, list_eq_of_zip f hf l l' (by simpa using h) hz.2]

theorem sameShapeAll_eq {a b : Forest.Shape} (h : sameShapeAll a b = true) : a = b := by
  cases a with
  | mk a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 =>
  cases b with
  | mk b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 =>
  simp only [sameShapeAll, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  have e1 : a1 = b1 := by
    apply Array.ext'
    exact list_eq_of_zip sameCall (fun _ _ => sameCall_eq) _ _ (by simpa using h0) h1
  subst e1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  rfl

/-- **A yes of sameHeardB gives one shape.** -/
theorem sameHeard_shape_eq {g h : Forest.Heard} (e : sameHeardB g h = true) : g.shape = h.shape :=
  sameShapeAll_eq (sameHeard_shape e)

#print axioms sameCall_eq
#print axioms sameShapeAll_eq
#print axioms sameHeard_shape_eq

end H2K5.Door
