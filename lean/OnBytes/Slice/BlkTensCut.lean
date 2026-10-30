-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkTensCut.lean: the program's cut of a structured vector at a length, from any
variable on.

The program keeps a vector of coefficients as a tensor: a scalar times, for each binary digit of the
index, one half of a pair (OnBytes/Iop/Tensor.lean). `tensorBelow v start count len` returns tensors
whose sum is v, but with 0 at every index whose digits start, .., start + count - 1 give a number
that is not below len. OnBytes/Slice/BlkForm.lean proves this for start = 0 (`sum_tensorBelow`), for
tensors without a written-out factor. This file carries that law to any start: the pairs below start
take no part in the cut, so the cut of v is the cut, from variable 0 on, of the tensor on the
variables from start on, with the lower pairs put back.

Main definitions: `upper`, `under`, `cutFrom`.
Main theorems: `tensorBelow_plain_at`, `cutFrom_eq`, `tensorBelow_shift`, `entry_under`,
`sum_tensorBelow_at`, `tensorBelow_shape_at`.

Not claimed. Nothing on a tensor with a written-out factor.

-/
import OnBytes.Slice.BlkForm

set_option autoImplicit false

namespace OnBytes.Slice
open OnBytes.Model (Reading)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The tensor on the variables of v from start on. -/
def upper (v : Tensor) (start : ℕ) : Tensor := { v with pairs := v.pairs.drop start }

/-- The tensor w, with the pairs of v below start put before its own. -/
def under (v : Tensor) (start : ℕ) (w : Tensor) : Tensor :=
  { w with pairs := v.pairs.take start ++ w.pairs }

/-- A tensor of which all entries are struck out but those whose digits from start on are below len
for the reason q. -/
def cutFrom (v : Tensor) (start count len q : ℕ) : Tensor :=
  { v with
    pairs := v.pairs.mapIdx fun i p =>
      if i < start + q || start + count ≤ i then p
      else if i == start + q then (p.1, zeroE)
      else if len.testBit (i - start) then (zeroE, p.2)
      else (p.1, zeroE) }

/-- The program's cut of a tensor without a written-out factor. -/
theorem tensorBelow_plain_at (v : Tensor) (hv : v.denseVars = []) (start count len : ℕ) :
    tensorBelow v start count len =
      if v.vars < start + count || 2 ^ count < len then none
      else if len == 2 ^ count then some [v]
      else if bitSum (fun t => !isZeroE (v.pairs.getD (start + t) (zeroE, zeroE)).2) count < len
        then some [v]
      else if len ≤ bitSum (fun t => isZeroE (v.pairs.getD (start + t) (zeroE, zeroE)).1) count
        then some []
      else some (((List.range count).filter fun q => len.testBit q).map fun q =>
        cutFrom v start count len q) := by
  unfold tensorBelow bitSum cutFrom
  simp [hv]

/-- The upper part of a tensor, with the lower pairs put back, is the tensor. -/
theorem under_upper (v : Tensor) (start : ℕ) : under v start (upper v start) = v := by
  unfold under upper
  simp only [List.take_append_drop]

/-- The cut from start on, for the reason q, is the cut of the upper part from 0 on, with the lower
pairs put back. -/
theorem cutFrom_eq (v : Tensor) (start count len q : ℕ) (hs : start ≤ v.vars) :
    cutFrom v start count len q = under v start (cutAt (upper v start) count len q) := by
  have hp : (v.pairs.mapIdx fun i p =>
      if i < start + q || start + count ≤ i then p
      else if i == start + q then (p.1, zeroE)
      else if len.testBit (i - start) then (zeroE, p.2)
      else (p.1, zeroE)) =
      v.pairs.take start ++ (v.pairs.drop start).mapIdx fun i p =>
        if i < q || count ≤ i then p
        else if i == q then (p.1, zeroE)
        else if len.testBit i then (zeroE, p.2)
        else (p.1, zeroE) := by
    have hlen : (v.pairs.take start).length = start := by
      rw [List.length_take]
      exact Nat.min_eq_left hs
    refine List.ext_getElem? fun i => ?_
    rw [List.getElem?_mapIdx]
    by_cases hi : i < start
    · rw [List.getElem?_append_left (by rw [hlen]; exact hi), List.getElem?_take_of_lt hi]
      have h1 : (decide (i < start + q) || decide (start + count ≤ i)) = true := by
        rw [decide_eq_true (by omega : i < start + q)]
        rfl
      cases v.pairs[i]? with
      | none => rfl
      | some p =>
        show some (if (decide (i < start + q) || decide (start + count ≤ i)) = true then p
          else _) = some p
        rw [if_pos h1]
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hi)
      rw [List.getElem?_append_right (by rw [hlen]; omega), hlen, Nat.add_sub_cancel_left,
        List.getElem?_mapIdx, List.getElem?_drop]
      have e1 : decide (start + k < start + q) = decide (k < q) :=
        decide_eq_decide.2 (by omega)
      have e2 : decide (start + count ≤ start + k) = decide (count ≤ k) :=
        decide_eq_decide.2 (by omega)
      have e3 : (start + k == start + q) = (k == q) := by
        by_cases hkq : k = q
        · rw [hkq, beq_self_eq_true, beq_self_eq_true]
        · rw [beq_eq_false_iff_ne.2 hkq, beq_eq_false_iff_ne.2 (by omega)]
      simp only [e1, e2, e3]
  unfold cutFrom under cutAt upper
  simp only [hp]

/-- **The cut from start on is the cut of the upper part from 0 on, with the lower pairs put
back.** -/
theorem tensorBelow_shift (v : Tensor) (hv : v.denseVars = []) (start count len : ℕ)
    (hs : start ≤ v.vars) :
    tensorBelow v start count len =
      (tensorBelow (upper v start) 0 count len).map (·.map (under v start)) := by
  have e1 : (upper v start).vars = v.vars - start := by
    unfold upper Tensor.vars
    exact List.length_drop
  have e2 : ∀ t, (upper v start).pairs.getD t (zeroE, zeroE) =
      v.pairs.getD (start + t) (zeroE, zeroE) := fun t => by
    unfold upper
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
  have e3 : decide (v.vars < start + count) = decide ((upper v start).vars < count) := by
    rw [e1]
    exact decide_eq_decide.2 (by omega)
  rw [tensorBelow_plain_at v hv, tensorBelow_plain (upper v start) hv]
  simp only [e2, e3]
  split
  · rfl
  · split
    · exact congrArg some (by
        show [v] = [under v start (upper v start)]
        rw [under_upper])
    · split
      · exact congrArg some (by
        show [v] = [under v start (upper v start)]
        rw [under_upper])
      · split
        · rfl
        · refine congrArg some ?_
          show _ = List.map (under v start) (List.map _ _)
          rw [List.map_map]
          exact List.map_congr_left fun q _ => cutFrom_eq v start count len q hs

/-- An entry of a tensor with lower pairs put before its own. -/
theorem entry_under (v w : Tensor) (hw : w.denseVars = []) (start : ℕ) (hs : start ≤ v.vars)
    (j : ℕ) :
    ρ.val ((under v start w).entry j) =
      pairsVal ρ (v.pairs.take start) j * ρ.val (w.entry (j / 2 ^ start)) := by
  have hlen : (v.pairs.take start).length = start := by
    rw [List.length_take]
    exact Nat.min_eq_left hs
  rw [entry_plain ρ (under v start w) hw, entry_plain ρ w hw]
  show ρ.val w.scalar * pairsVal ρ (v.pairs.take start ++ w.pairs) j = _
  rw [pairsVal_append, hlen]
  ring

/-- **The program's cut of a vector at a length, from any variable on.** For a tensor without a
written-out factor: the sum of the parts' entries at j is the tensor's entry if the count digits of
j from start on give a number below len, else 0. -/
theorem sum_tensorBelow_at (v : Tensor) (hv : v.denseVars = []) (start count len : ℕ)
    (l : List Tensor) (h : tensorBelow v start count len = some l) (j : ℕ) :
    (l.map fun w => ρ.val (w.entry j)).sum =
      if j / 2 ^ start % 2 ^ count < len then ρ.val (v.entry j) else 0 := by
  have hs : start ≤ v.vars := by
    by_contra hno
    rw [tensorBelow_plain_at v hv, if_pos (by rw [decide_eq_true (by omega)]; rfl)] at h
    cases h
  rw [tensorBelow_shift v hv start count len hs] at h
  cases hl : tensorBelow (upper v start) 0 count len with
  | none => rw [hl] at h; cases h
  | some l' =>
    rw [hl] at h
    obtain rfl := Option.some.inj h
    have hsh := tensorBelow_shape (upper v start) hv count len l' hl
    have hsum := sum_tensorBelow ρ (upper v start) hv count len l' hl (j / 2 ^ start)
    rw [List.map_map]
    have e : (l'.map ((fun w => ρ.val (w.entry j)) ∘ under v start)) =
        l'.map fun w => pairsVal ρ (v.pairs.take start) j * ρ.val (w.entry (j / 2 ^ start)) :=
      List.map_congr_left fun w hw => entry_under ρ v w (hsh w hw).2 start hs j
    rw [e, List.sum_map_mul_left, hsum]
    have hv' : ρ.val (v.entry j) =
        pairsVal ρ (v.pairs.take start) j * ρ.val ((upper v start).entry (j / 2 ^ start)) := by
      rw [← entry_under ρ v (upper v start) hv start hs j, under_upper]
    rw [hv']
    split
    · rfl
    · exact mul_zero _

/-- The parts of a cut have the tensor's number of variables and no written-out factor. -/
theorem tensorBelow_shape_at (v : Tensor) (hv : v.denseVars = []) (start count len : ℕ)
    (l : List Tensor) (h : tensorBelow v start count len = some l) :
    ∀ w ∈ l, w.vars = v.vars ∧ w.denseVars = [] := by
  have hs : start ≤ v.vars := by
    by_contra hno
    rw [tensorBelow_plain_at v hv, if_pos (by rw [decide_eq_true (by omega)]; rfl)] at h
    cases h
  rw [tensorBelow_shift v hv start count len hs] at h
  cases hl : tensorBelow (upper v start) 0 count len with
  | none => rw [hl] at h; cases h
  | some l' =>
    rw [hl] at h
    obtain rfl := Option.some.inj h
    intro w hw
    obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hw
    obtain ⟨a1, a2⟩ := tensorBelow_shape (upper v start) hv count len l' hl w' hw'
    refine ⟨?_, a2⟩
    show (v.pairs.take start ++ w'.pairs).length = v.pairs.length
    have a1' : w'.pairs.length = (v.pairs.drop start).length := a1
    rw [List.length_append, a1', ← List.length_append, List.take_append_drop]

end OnBytes.Slice
