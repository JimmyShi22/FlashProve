-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/Corner.lean: SMALL LAWS ON POINTS OF ZEROS AND ONES.

Not shown here. Nothing on any protocol. No property is claimed.

Where the coordinates of a point are the words 0 and 1, the verifier's table of equality weights
(eqTab, OnBytes/Model/Frame.lean) reads as 1 at the number that the point spells and as 0
elsewhere. cornerOf (Johnson/Desc/K4/Honest/Cells.lean) is the honest side's function from such a
point to that number.

  cstep, cornerOf_list, foldl_cstep_none   cornerOf as a loop over a list.
  corner_bits    what the loop returns: the number's bits are the coordinates.
  corner_pt      the same for cornerOf, in the notation of eqN_bool
                 (Johnson/Road/FormsKeysFac.lean).
  eqTab_corner   the table at such a point.
-/
import Johnson.Desc.K4.Honest.Cells
import Johnson.Road.FormsKeysFac

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Desc.First.K4.Honest (cornerOf)

/-- One step of cornerOf. -/
def cstep (s : Option ℕ) (c : E) : Option ℕ :=
  s.bind fun x =>
    if c == zeroE then some (2 * x) else if c == oneE then some (2 * x + 1) else none

/-- cornerOf is that loop. -/
theorem cornerOf_list (z : Array E) : cornerOf z = z.toList.foldl cstep (some 0) := by
  unfold cornerOf
  rw [← Array.foldl_toList]
  rfl

/-- From nothing the loop returns nothing. -/
theorem foldl_cstep_none : ∀ l : List E, l.foldl cstep none = none
  | [] => rfl
  | _ :: l => foldl_cstep_none l

/-- What the loop returns: the number's bits are the coordinates, the first being the highest. -/
theorem corner_bits : ∀ (l : List E) (x t : ℕ), l.foldl cstep (some x) = some t →
    ∃ t', t = 2 ^ l.length * x + t' ∧ t' < 2 ^ l.length ∧ ∀ s, s < l.length →
      Reading.gl.val (l.getD s zeroE) = if t'.testBit (l.length - 1 - s) then 1 else 0
  | [], x, t, h => by
    have e : x = t := Option.some.inj h
    exact ⟨0, by simp [e], by simp, fun s hs => absurd hs (Nat.not_lt_zero _)⟩
  | c :: l, x, t, h => by
    rw [List.foldl_cons] at h
    by_cases c0 : (c == zeroE) = true
    · have e : cstep (some x) c = some (2 * x) := by
        show (if (c == zeroE) = true then some (2 * x) else _) = _
        rw [if_pos c0]
      rw [e] at h
      obtain ⟨t', a1, a2, a3⟩ := corner_bits l (2 * x) t h
      refine ⟨t', ?_, ?_, ?_⟩
      · rw [a1, List.length_cons, pow_succ]
        ring
      · rw [List.length_cons, pow_succ]
        omega
      · intro s hs
        rw [List.length_cons] at hs ⊢
        cases s with
        | zero =>
          rw [List.getD_cons_zero, eq_of_beq c0, Reading.gl.zero,
            show l.length + 1 - 1 - 0 = l.length by omega, Nat.testBit_lt_two_pow a2]
          rfl
        | succ s =>
          rw [List.getD_cons_succ, a3 s (by omega),
            show l.length + 1 - 1 - (s + 1) = l.length - 1 - s by omega]
    · by_cases c1 : (c == oneE) = true
      · have e : cstep (some x) c = some (2 * x + 1) := by
          show (if (c == zeroE) = true then _ else if (c == oneE) = true then some (2 * x + 1)
            else _) = _
          rw [if_neg c0, if_pos c1]
        rw [e] at h
        obtain ⟨t', a1, a2, a3⟩ := corner_bits l (2 * x + 1) t h
        refine ⟨2 ^ l.length * 1 + t', ?_, ?_, ?_⟩
        · rw [a1, List.length_cons, pow_succ]
          ring
        · rw [List.length_cons, pow_succ]
          omega
        · intro s hs
          rw [List.length_cons] at hs ⊢
          cases s with
          | zero =>
            rw [List.getD_cons_zero, eq_of_beq c1, Reading.gl.one,
              show l.length + 1 - 1 - 0 = l.length by omega,
              Nat.testBit_two_pow_mul_add _ a2, if_neg (Nat.lt_irrefl _), Nat.sub_self]
            rfl
          | succ s =>
            have hb : (2 ^ l.length * 1 + t').testBit (l.length - 1 - s) =
                t'.testBit (l.length - 1 - s) := by
              rw [Nat.testBit_two_pow_mul_add _ a2, if_pos (by omega)]
            rw [List.getD_cons_succ, a3 s (by omega),
              show l.length + 1 - 1 - (s + 1) = l.length - 1 - s by omega, hb]
      · have e : cstep (some x) c = none := by
          show (if (c == zeroE) = true then _ else if (c == oneE) = true then _ else none) = _
          rw [if_neg c0, if_neg c1]
        rw [e, foldl_cstep_none] at h
        cases h

/-- The number that a point of zeros and ones spells. -/
theorem corner_pt {z : Array E} {t : ℕ} (h : cornerOf z = some t) :
    t < 2 ^ z.size ∧ ∀ s, s < z.size →
      pt Reading.gl z (0 + s) = if t.testBit (z.size - 1 - s) then 1 else 0 := by
  rw [cornerOf_list] at h
  obtain ⟨t', a1, a2, a3⟩ := corner_bits z.toList 0 t h
  rw [Array.length_toList] at a1 a2 a3
  have e : t = t' := by rw [a1]; omega
  subst e
  refine ⟨a2, fun s hs => ?_⟩
  have := a3 s hs
  unfold pt
  rw [Nat.zero_add, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList,
    ← List.getD_eq_getElem?_getD]
  exact this

/-- The table of equality weights at such a point. -/
theorem eqTab_corner {z : Array E} {t : ℕ} (h : cornerOf z = some t) {i : ℕ}
    (hi : i < 2 ^ z.size) :
    Reading.gl.val ((eqTab z).getD i zeroE) = if i = t then 1 else 0 := by
  obtain ⟨h1, h2⟩ := corner_pt h
  rw [eqTab_value Reading.gl z i hi]
  exact eqN_bool z.size 0 _ h1 hi h2

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.cornerOf_list
#print axioms OnBytes.Road.K4.C.foldl_cstep_none
#print axioms OnBytes.Road.K4.C.corner_bits
#print axioms OnBytes.Road.K4.C.corner_pt
#print axioms OnBytes.Road.K4.C.eqTab_corner
