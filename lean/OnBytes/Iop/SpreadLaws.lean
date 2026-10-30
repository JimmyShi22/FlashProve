-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/SpreadLaws.lean: what Tensor.addTo adds, entry by entry.

Tensor.addTo (OnBytes/Iop/Tensor.lean) adds a vector of product form to a written-out vector. The
law: under any reading of the program's field elements in a commutative ring (Model.Reading, see
OnBytes/Iop/TensorLaws.lean), entry J of the result reads as entry J of the vector plus entry J of
the tensor, for J within both; every other entry reads as before, and the length stays
(Tensor.addTo_size).

Main definitions: pairsValHigh, spreadVal.
Main theorems: spreadTo_size, spreadTo_val, Tensor.addTo_size, Tensor.addTo_val.

What is not claimed. Every equation but those on lengths is between readings, not between the
program's words. Nothing on soundness. The program does not import this file.
-/
import OnBytes.Iop.TensorLaws

namespace OnBytes

open Model (Reading)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The product of the pairs' halves that the bits of j pick, for pairs from the highest variable
down. -/
def pairsValHigh : List (E × E) → Nat → K
  | [], _ => 1
  | p :: ps, j =>
    ρ.val (if j / 2 ^ ps.length % 2 == 1 then p.2 else p.1) * pairsValHigh ps (j % 2 ^ ps.length)

/-- From the highest variable down or from the lowest up, the product is the same. -/
theorem pairsValHigh_eq : ∀ (qs : List (E × E)) (j : Nat),
    pairsValHigh ρ qs j = pairsVal ρ qs.reverse j
  | [], _ => rfl
  | p :: qs, j => by
    have h := pairsVal_mod ρ qs.reverse j
    rw [List.length_reverse] at h
    rw [pairsValHigh, pairsValHigh_eq qs, h, List.reverse_cons, pairsVal_append,
      List.length_reverse]
    simp only [pairsVal, mul_one]
    ring

/-- What spreadTo adds at the index J of a vector of the given length, as a value of K. sK: what
the factor so far reads as. -/
def spreadVal (v : Tensor) (ps : List (E × E)) (off : Nat) (sK : K) (size J : Nat) : K :=
  if off ≤ J ∧ J < off + 2 ^ ps.length ∧ J < size then
    sK * pairsValHigh ρ ps (J - off) * v.denseVal ρ J
  else 0

/-- What is added for a list of pairs is what is added for the rest of the list on the low half of
the range, with the factor times the first pair's low half, plus the same on the high half with its
high half. -/
theorem spreadVal_cons (v : Tensor) (p : E × E) (ps : List (E × E)) (off : Nat) (sK : K)
    (size J : Nat) :
    spreadVal ρ v (p :: ps) off sK size J =
      spreadVal ρ v ps off (sK * ρ.val p.1) size J +
        spreadVal ρ v ps (off + 2 ^ ps.length) (sK * ρ.val p.2) size J := by
  unfold spreadVal
  have hp := Nat.two_pow_pos ps.length
  have hw : 2 ^ (p :: ps).length = 2 ^ ps.length + 2 ^ ps.length := by
    rw [List.length_cons, Nat.pow_succ]
    omega
  rw [hw]
  by_cases hs : J < size
  · by_cases h1 : off ≤ J
    · by_cases h2 : J < off + 2 ^ ps.length
      · have a1 : (J - off) / 2 ^ ps.length = 0 := Nat.div_eq_of_lt (by omega)
        have a2 : (J - off) % 2 ^ ps.length = J - off := Nat.mod_eq_of_lt (by omega)
        have c1 : off ≤ J ∧ J < off + (2 ^ ps.length + 2 ^ ps.length) ∧ J < size :=
          ⟨h1, by omega, hs⟩
        have c2 : off ≤ J ∧ J < off + 2 ^ ps.length ∧ J < size := ⟨h1, h2, hs⟩
        have c3 : ¬ (off + 2 ^ ps.length ≤ J ∧ J < off + 2 ^ ps.length + 2 ^ ps.length ∧
            J < size) := by omega
        rw [if_pos c1, if_pos c2, if_neg c3, pairsValHigh, a1, a2]
        simp
        ring
      · by_cases h3 : J < off + (2 ^ ps.length + 2 ^ ps.length)
        · have a1 : (J - off) / 2 ^ ps.length = 1 :=
            Nat.div_eq_of_lt_le (by omega) (by omega)
          have a2 : (J - off) % 2 ^ ps.length = J - (off + 2 ^ ps.length) := by
            have d := Nat.mod_add_div (J - off) (2 ^ ps.length)
            rw [a1] at d
            omega
          have c1 : off ≤ J ∧ J < off + (2 ^ ps.length + 2 ^ ps.length) ∧ J < size :=
            ⟨h1, h3, hs⟩
          have c2 : ¬ (off ≤ J ∧ J < off + 2 ^ ps.length ∧ J < size) := by omega
          have c3 : off + 2 ^ ps.length ≤ J ∧ J < off + 2 ^ ps.length + 2 ^ ps.length ∧
              J < size := ⟨by omega, by omega, hs⟩
          rw [if_pos c1, if_neg c2, if_pos c3, pairsValHigh, a1, a2]
          simp
          ring
        · have c1 : ¬ (off ≤ J ∧ J < off + (2 ^ ps.length + 2 ^ ps.length) ∧ J < size) := by
            omega
          have c2 : ¬ (off ≤ J ∧ J < off + 2 ^ ps.length ∧ J < size) := by omega
          have c3 : ¬ (off + 2 ^ ps.length ≤ J ∧ J < off + 2 ^ ps.length + 2 ^ ps.length ∧
              J < size) := by omega
          rw [if_neg c1, if_neg c2, if_neg c3, add_zero]
    · have c1 : ¬ (off ≤ J ∧ J < off + (2 ^ ps.length + 2 ^ ps.length) ∧ J < size) := by omega
      have c2 : ¬ (off ≤ J ∧ J < off + 2 ^ ps.length ∧ J < size) := by omega
      have c3 : ¬ (off + 2 ^ ps.length ≤ J ∧ J < off + 2 ^ ps.length + 2 ^ ps.length ∧
          J < size) := by omega
      rw [if_neg c1, if_neg c2, if_neg c3, add_zero]
  · have c1 : ¬ (off ≤ J ∧ J < off + (2 ^ ps.length + 2 ^ ps.length) ∧ J < size) := by omega
    have c2 : ¬ (off ≤ J ∧ J < off + 2 ^ ps.length ∧ J < size) := by omega
    have c3 : ¬ (off + 2 ^ ps.length ≤ J ∧ J < off + 2 ^ ps.length + 2 ^ ps.length ∧
        J < size) := by omega
    rw [if_neg c1, if_neg c2, if_neg c3, add_zero]

/-- A factor that reads as 0 adds nothing. -/
theorem spreadVal_zero (v : Tensor) (ps : List (E × E)) (off size J : Nat) :
    spreadVal ρ v ps off 0 size J = 0 := by
  unfold spreadVal
  split <;> simp

/-- An element whose three words are 0 reads as 0. -/
theorem val_of_isZeroE (a : E) (h : isZeroE a = true) : ρ.val a = 0 := by
  unfold isZeroE at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have e : a = zeroE := E.ext3 h.1.1 h.1.2 h.2
  rw [e, ρ.zero]

/-- timesOne reads as the product. -/
theorem timesOne_val (s p : E) : ρ.val (timesOne s p) = ρ.val s * ρ.val p := by
  unfold timesOne
  split
  · rename_i h
    rw [beq_iff_eq.1 h, ρ.one, mul_one]
  · rw [ρ.mul]

/-- Entry j of an array after modify at i: f of the old entry if i = j and j is within the array,
else the old entry. -/
theorem getD_modify (a : Array E) (i : Nat) (f : E → E) (j : Nat) :
    (a.modify i f).getD j zeroE =
      if i = j ∧ j < a.size then f (a.getD j zeroE) else a.getD j zeroE := by
  by_cases hj : j < a.size
  · by_cases hi : i = j
    · subst hi
      simp [Array.getD, hj, Array.getElem_modify]
    · simp [Array.getD, hj, hi, Array.getElem_modify]
  · simp [Array.getD, hj]

/-- One step of spreadTo, as an equation between functions of the last three arguments. (Lean's
kernel compares the arguments of one function from the last on; see pairsAt_cons_fun.) -/
theorem spreadTo_cons_fun (v : Tensor) (p : E × E) (ps : List (E × E)) (w : Nat) :
    Tensor.spreadTo v (p :: ps) w = fun off s out =>
      let out1 := if isZeroE p.1 then out else Tensor.spreadTo v ps (w / 2) off (timesOne s p.1) out
      if isZeroE p.2 then out1
      else Tensor.spreadTo v ps (w / 2) (off + w / 2) (timesOne s p.2) out1 := rfl

/-- The end of spreadTo, as an equation between functions. -/
theorem spreadTo_nil_fun (v : Tensor) (w : Nat) :
    Tensor.spreadTo v [] w = fun off s out =>
      out.modify off fun y =>
        addE y (if v.denseVars.isEmpty then s
          else mulE s (v.values.getD (v.first + denseIndex v.denseVars 0 off) zeroE)) := rfl

/-- spreadTo keeps the vector's length. -/
theorem spreadTo_size (v : Tensor) : ∀ (ps : List (E × E)) (w off : Nat) (s : E) (out : Array E),
    (Tensor.spreadTo v ps w off s out).size = out.size
  | [], w, off, s, out => by
    rw [spreadTo_nil_fun]
    simp
  | p :: ps, w, off, s, out => by
    rw [spreadTo_cons_fun]
    dsimp only
    split <;> split <;> simp [spreadTo_size v ps]

/-- If w is 2 to the number of pairs, entry J after spreadTo reads as the old entry plus spreadVal
at J. -/
theorem spreadTo_val (v : Tensor) : ∀ (ps : List (E × E)) (w off : Nat) (s : E) (out : Array E)
    (J : Nat), w = 2 ^ ps.length →
    ρ.val ((Tensor.spreadTo v ps w off s out).getD J zeroE) =
      ρ.val (out.getD J zeroE) + spreadVal ρ v ps off (ρ.val s) out.size J
  | [], w, off, s, out, J, _ => by
    rw [spreadTo_nil_fun]
    dsimp only
    rw [getD_modify]
    unfold spreadVal Tensor.denseVal
    by_cases h : off = J ∧ J < out.size
    · obtain ⟨rfl, h2⟩ := h
      have c : off ≤ off ∧ off < off + 2 ^ ([] : List (E × E)).length ∧ off < out.size :=
        ⟨Nat.le_refl _, by simp, h2⟩
      rw [if_pos ⟨rfl, h2⟩, if_pos c, ρ.add, pairsValHigh]
      split
      · simp
      · rw [ρ.mul]
        ring
    · have c : ¬ (off ≤ J ∧ J < off + 2 ^ ([] : List (E × E)).length ∧ J < out.size) := by
        simp only [List.length_nil, Nat.pow_zero]
        omega
      rw [if_neg h, if_neg c, add_zero]
  | p :: ps, w, off, s, out, J, hw => by
    have hw2 : w / 2 = 2 ^ ps.length := by
      rw [hw, List.length_cons, Nat.pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2)]
    rw [spreadTo_cons_fun, spreadVal_cons]
    dsimp only
    rw [hw2]
    by_cases z1 : isZeroE p.1 = true
    · by_cases z2 : isZeroE p.2 = true
      · simp only [z1, z2, if_true, val_of_isZeroE ρ _ z1, val_of_isZeroE ρ _ z2, mul_zero,
          spreadVal_zero, add_zero]
      · simp only [z1, z2, if_true, Bool.false_eq_true, if_false, val_of_isZeroE ρ _ z1, mul_zero,
          spreadVal_zero, zero_add, spreadTo_val v ps _ _ _ _ J rfl, timesOne_val]
    · by_cases z2 : isZeroE p.2 = true
      · simp only [z1, z2, if_true, Bool.false_eq_true, if_false, val_of_isZeroE ρ _ z2, mul_zero,
          spreadVal_zero, add_zero, spreadTo_val v ps _ _ _ _ J rfl, timesOne_val]
      · simp only [z1, z2, Bool.false_eq_true, if_false, spreadTo_val v ps _ _ _ _ J rfl,
          timesOne_val, spreadTo_size, add_assoc]

/-- Tensor.addTo keeps the vector's length. -/
theorem Tensor.addTo_size (v : Tensor) (out : Array E) : (v.addTo out).size = out.size := by
  unfold Tensor.addTo
  split
  · rfl
  · exact spreadTo_size v _ _ _ _ _

/-- What Tensor.addTo adds: entry J of the tensor at every index J within the tensor and the
vector, and nothing elsewhere. -/
theorem Tensor.addTo_val (v : Tensor) (out : Array E) (J : Nat) :
    ρ.val ((v.addTo out).getD J zeroE) =
      ρ.val (out.getD J zeroE) +
        if J < 2 ^ v.vars ∧ J < out.size then ρ.val (v.entry J) else 0 := by
  unfold Tensor.addTo
  by_cases z : isZeroE v.scalar = true
  · simp only [z, if_true, Tensor.entry_val, val_of_isZeroE ρ _ z, zero_mul]
    simp
  · simp only [z, Bool.false_eq_true, if_false]
    rw [spreadTo_val ρ v _ _ _ _ _ J (by rw [List.length_reverse]; rfl)]
    unfold spreadVal
    simp only [Nat.zero_le, true_and, Nat.zero_add, List.length_reverse, Nat.sub_zero,
      pairsValHigh_eq, List.reverse_reverse, Tensor.entry_val]
    rfl

end OnBytes

#print axioms OnBytes.Tensor.addTo_val
