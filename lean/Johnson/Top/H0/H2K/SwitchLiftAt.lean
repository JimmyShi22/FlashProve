-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H0/H2K/SwitchLiftAt.lean: the entries of `switchLift` (OnBytes/Iop/Cs.lean), read in
the field, at a block of rows that need not be the whole table.

switchLift carries a coefficient vector on 2 ^ vars entries to a table of 2 ^ tb entries that is
filled row index first: entry j of the vector goes to the index cutIndex q R j = q.firstRow + j % 2
^ q.bits + (j / 2 ^ q.bits) * 2 ^ R. The library's `formAt_switchLift`
(OnBytes/Slice/BlkCsRows.lean) is stated at q = ⟨.main, k, 0⟩ and R = k: there the block is the
whole table and the vector lies side by side from index 0 on. Statements and proofs, on the
program's pure functions alone.
Does that lemma reach firstRow = 0 with q.bits < R? No. Its statement fixes R = q.bits, and its
right-hand side (the vector side by side) need not hold there: `lift_gap` shows that at the index 2
^ q.bits the lifted form is 0, where the vector side by side would have its entry number 2 ^ q.bits.
Main names:
  `formAt_switchLift_at`: at any index J below 2 ^ tb the lifted form has the entry number J % 2 ^
    q.bits + 2 ^ q.bits * (J / 2 ^ R) of the vector if J < 2 ^ (vars + (R - q.bits)) and the row
    bits of J above the block pick the block; else 0.
  `cutIndex_parts`: the index cutIndex q R j taken apart.
  `formAt_switchLift_cutIndex`: at the index cutIndex q R j, for j < 2 ^ vars, the lifted form has
    the vector's entry j.
  `formAt_switchLift_off`: at an index below 2 ^ tb that is cutIndex q R j for no j < 2 ^ vars it is
    0.
  `lift_gap`: the answer above.
Limits: No soundness is claimed, and nothing is said on hiding.
Premises: every tensor of the form has vars variables; q.bits ≤ vars; q.bits ≤ R; vars + (R -
q.bits) ≤ tb; the block lies in the table (q.firstRow / 2 ^ q.bits < 2 ^ (R - q.bits)); for the two
laws at cutIndex, that q.firstRow is a multiple of 2 ^ q.bits (switchTargetCheck tests it). Nothing
is said on which cuts a switch has.
Of the library it calls Form.entry_insertChoice (OnBytes/Iop/TensorLaws.lean) and vars_insertChoice
(OnBytes/Slice/BlkTens.lean).
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import OnBytes.Slice.BlkCsRows

set_option autoImplicit false
namespace H2K.Lift
open OnBytes OnBytes.Slice

theorem formAt_switchLift_at (c : Form) (vars : ℕ) (q : RowCut) (R tb : ℕ)
    (hc : ∀ v ∈ c.tensors, v.vars = vars) (hb : q.bits ≤ vars) (hR : q.bits ≤ R)
    (hv : vars + (R - q.bits) ≤ tb) (hf : q.firstRow / 2 ^ q.bits < 2 ^ (R - q.bits)) (J : ℕ)
    (hJ : J < 2 ^ tb) :
    formAt (switchLift c vars q R tb) J =
      if J < 2 ^ (vars + (R - q.bits)) ∧
          J / 2 ^ q.bits % 2 ^ (R - q.bits) = q.firstRow / 2 ^ q.bits
      then formAt c (J % 2 ^ q.bits + 2 ^ q.bits * (J / 2 ^ R)) else 0 := by
  have h1 : ∀ v ∈ c.tensors, q.bits ≤ v.vars := fun v hv' => by rw [hc v hv']; exact hb
  have h2 : ∀ v ∈ (c.insertChoice q.bits (R - q.bits) (q.firstRow / 2 ^ q.bits)).tensors,
      vars + (R - q.bits) ≤ v.vars := by
    intro v hv'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hv'
    rw [vars_insertChoice u _ _ _ (h1 u hu), hc u hu]
  show readE (((c.insertChoice q.bits (R - q.bits) (q.firstRow / 2 ^ q.bits)).insertChoice
    (vars + (R - q.bits)) (tb - (vars + (R - q.bits))) 0).entry J) = _
  refine (Form.entry_insertChoice rdE _ _ _ _ J h2).trans ?_
  have hin : ∀ i, rdE.val ((c.insertChoice q.bits (R - q.bits)
      (q.firstRow / 2 ^ q.bits)).entry i) =
      (if i / 2 ^ q.bits % 2 ^ (R - q.bits) = q.firstRow / 2 ^ q.bits % 2 ^ (R - q.bits)
        then 1 else 0) * formAt c (unshift q.bits (R - q.bits) i) :=
    fun i => Form.entry_insertChoice rdE c _ _ _ i h1
  rw [hin]
  by_cases hlt : J < 2 ^ (vars + (R - q.bits))
  · have hu : unshift (vars + (R - q.bits)) (tb - (vars + (R - q.bits))) J = J := by
      unfold unshift
      rw [Nat.mod_eq_of_lt hlt, Nat.add_sub_cancel' hv, Nat.div_eq_of_lt hJ, Nat.mul_zero,
        Nat.add_zero]
    rw [Nat.div_eq_of_lt hlt, Nat.zero_mod, if_pos rfl, one_mul, hu, Nat.mod_eq_of_lt hf]
    unfold unshift
    rw [Nat.add_sub_cancel' hR]
    by_cases h3 : J / 2 ^ q.bits % 2 ^ (R - q.bits) = q.firstRow / 2 ^ q.bits
    · rw [if_pos h3, one_mul, if_pos ⟨hlt, h3⟩]
    · rw [if_neg h3, zero_mul, if_neg fun h => h3 h.2]
  · have hpos : 0 < 2 ^ (vars + (R - q.bits)) := Nat.two_pow_pos _
    have hq : J / 2 ^ (vars + (R - q.bits)) < 2 ^ (tb - (vars + (R - q.bits))) :=
      Nat.div_lt_of_lt_mul (by rw [← pow_add, Nat.add_sub_cancel' hv]; exact hJ)
    have hge : 1 ≤ J / 2 ^ (vars + (R - q.bits)) :=
      (Nat.le_div_iff_mul_le hpos).2 (by rw [Nat.one_mul]; exact Nat.le_of_not_lt hlt)
    rw [Nat.mod_eq_of_lt hq, Nat.zero_mod, if_neg (by omega), zero_mul,
      if_neg fun h => hlt h.1]

/-- The index cutIndex q R j taken apart, for an aligned block inside the table. -/
theorem cutIndex_parts (q : RowCut) (R j : ℕ) (hR : q.bits ≤ R)
    (hal : 2 ^ q.bits ∣ q.firstRow) (hf : q.firstRow / 2 ^ q.bits < 2 ^ (R - q.bits)) :
    cutIndex q R j % 2 ^ q.bits = j % 2 ^ q.bits ∧
      cutIndex q R j / 2 ^ q.bits % 2 ^ (R - q.bits) = q.firstRow / 2 ^ q.bits ∧
      cutIndex q R j / 2 ^ R = j / 2 ^ q.bits := by
  obtain ⟨φ, hφ⟩ := hal
  have hpb : 0 < 2 ^ q.bits := Nat.two_pow_pos _
  have hpa : 0 < 2 ^ (R - q.bits) := Nat.two_pow_pos _
  have hφ' : q.firstRow / 2 ^ q.bits = φ := by rw [hφ, Nat.mul_div_cancel_left _ hpb]
  rw [hφ'] at hf ⊢
  have hRR : 2 ^ R = 2 ^ q.bits * 2 ^ (R - q.bits) := by
    rw [← pow_add, Nat.add_sub_cancel' hR]
  have hx : cutIndex q R j =
      j % 2 ^ q.bits + 2 ^ q.bits * (φ + 2 ^ (R - q.bits) * (j / 2 ^ q.bits)) := by
    unfold cutIndex
    rw [hφ, hRR]
    ring
  have hj0 : j % 2 ^ q.bits < 2 ^ q.bits := Nat.mod_lt _ hpb
  have hd : cutIndex q R j / 2 ^ q.bits = φ + 2 ^ (R - q.bits) * (j / 2 ^ q.bits) := by
    rw [hx, Nat.add_mul_div_left _ _ hpb, Nat.div_eq_of_lt hj0, Nat.zero_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [hx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj0]
  · rw [hd, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hf]
  · rw [hRR, ← Nat.div_div_eq_div_mul, hd, Nat.add_mul_div_left _ _ hpa, Nat.div_eq_of_lt hf,
      Nat.zero_add]

/-- At the index of entry j the lifted form has the vector's entry j. -/
theorem formAt_switchLift_cutIndex (c : Form) (vars : ℕ) (q : RowCut) (R tb : ℕ)
    (hc : ∀ v ∈ c.tensors, v.vars = vars) (hb : q.bits ≤ vars) (hR : q.bits ≤ R)
    (hv : vars + (R - q.bits) ≤ tb) (hal : 2 ^ q.bits ∣ q.firstRow)
    (hf : q.firstRow / 2 ^ q.bits < 2 ^ (R - q.bits)) (j : ℕ) (hj : j < 2 ^ vars) :
    formAt (switchLift c vars q R tb) (cutIndex q R j) = formAt c j := by
  obtain ⟨p1, p2, p3⟩ := cutIndex_parts q R j hR hal hf
  have hpR : 0 < 2 ^ R := Nat.two_pow_pos _
  have hlt : cutIndex q R j < 2 ^ (vars + (R - q.bits)) := by
    have e : 2 ^ (vars + (R - q.bits)) = 2 ^ (vars - q.bits) * 2 ^ R := by
      rw [← pow_add]
      congr 1
      omega
    rw [e]
    apply (Nat.div_lt_iff_lt_mul hpR).1
    rw [p3]
    apply Nat.div_lt_of_lt_mul
    rw [← pow_add, Nat.add_sub_cancel' hb]
    exact hj
  have hJ : cutIndex q R j < 2 ^ tb := lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) hv)
  rw [formAt_switchLift_at c vars q R tb hc hb hR hv hf _ hJ, if_pos ⟨hlt, p2⟩, p1, p3,
    Nat.mod_add_div]

/-- At an index that is the index of no entry the lifted form is 0. -/
theorem formAt_switchLift_off (c : Form) (vars : ℕ) (q : RowCut) (R tb : ℕ)
    (hc : ∀ v ∈ c.tensors, v.vars = vars) (hb : q.bits ≤ vars) (hR : q.bits ≤ R)
    (hv : vars + (R - q.bits) ≤ tb) (hal : 2 ^ q.bits ∣ q.firstRow)
    (hf : q.firstRow / 2 ^ q.bits < 2 ^ (R - q.bits)) (J : ℕ) (hJ : J < 2 ^ tb)
    (h : ∀ j, j < 2 ^ vars → cutIndex q R j ≠ J) :
    formAt (switchLift c vars q R tb) J = 0 := by
  rw [formAt_switchLift_at c vars q R tb hc hb hR hv hf J hJ]
  apply if_neg
  rintro ⟨hlt, h3⟩
  have hpb : 0 < 2 ^ q.bits := Nat.two_pow_pos _
  have hpR : 0 < 2 ^ R := Nat.two_pow_pos _
  have hRR : 2 ^ R = 2 ^ q.bits * 2 ^ (R - q.bits) := by
    rw [← pow_add, Nat.add_sub_cancel' hR]
  have hj0 : J % 2 ^ q.bits < 2 ^ q.bits := Nat.mod_lt _ hpb
  have hq : J / 2 ^ R < 2 ^ (vars - q.bits) := by
    apply Nat.div_lt_of_lt_mul
    rw [← pow_add]
    have : R + (vars - q.bits) = vars + (R - q.bits) := by omega
    rw [this]
    exact hlt
  refine h (J % 2 ^ q.bits + 2 ^ q.bits * (J / 2 ^ R)) ?_ ?_
  · have e : 2 ^ vars = 2 ^ q.bits * 2 ^ (vars - q.bits) := by
      rw [← pow_add, Nat.add_sub_cancel' hb]
    rw [e]
    calc J % 2 ^ q.bits + 2 ^ q.bits * (J / 2 ^ R)
        < 2 ^ q.bits + 2 ^ q.bits * (J / 2 ^ R) := Nat.add_lt_add_right hj0 _
      _ = 2 ^ q.bits * (J / 2 ^ R + 1) := by ring
      _ ≤ 2 ^ q.bits * 2 ^ (vars - q.bits) := Nat.mul_le_mul_left _ hq
  · unfold cutIndex
    rw [Nat.add_mul_mod_self_left, Nat.mod_mod, Nat.add_mul_div_left _ _ hpb,
      Nat.div_eq_of_lt hj0, Nat.zero_add]
    have e1 : q.firstRow = 2 ^ q.bits * (J / 2 ^ q.bits % 2 ^ (R - q.bits)) := by
      rw [h3, Nat.mul_div_cancel' hal]
    have e2 : J / 2 ^ R = J / 2 ^ q.bits / 2 ^ (R - q.bits) := by
      rw [hRR, Nat.div_div_eq_div_mul]
    have e3 := Nat.mod_add_div (J / 2 ^ q.bits) (2 ^ (R - q.bits))
    have e4 := Nat.mod_add_div J (2 ^ q.bits)
    rw [e1, e2, hRR]
    calc 2 ^ q.bits * (J / 2 ^ q.bits % 2 ^ (R - q.bits)) + J % 2 ^ q.bits +
          J / 2 ^ q.bits / 2 ^ (R - q.bits) * (2 ^ q.bits * 2 ^ (R - q.bits))
        = J % 2 ^ q.bits + 2 ^ q.bits * (J / 2 ^ q.bits % 2 ^ (R - q.bits) +
            2 ^ (R - q.bits) * (J / 2 ^ q.bits / 2 ^ (R - q.bits))) := by ring
      _ = J := by rw [e3, e4]

/-- Where the block begins at row 0 and is not the whole table, the vector does not lie side by
side: at the index 2 ^ q.bits the lifted form is 0. -/
theorem lift_gap (c : Form) (vars : ℕ) (part : Part) (b R tb : ℕ)
    (hc : ∀ v ∈ c.tensors, v.vars = vars) (hb : b ≤ vars) (hR : b < R)
    (hv : vars + (R - b) ≤ tb) :
    formAt (switchLift c vars ⟨part, b, 0⟩ R tb) (2 ^ b) = 0 := by
  have hpb : 0 < 2 ^ b := Nat.two_pow_pos _
  have h2 : 1 < 2 ^ (R - b) := Nat.one_lt_two_pow (by omega)
  have hJ : 2 ^ b < 2 ^ tb := Nat.pow_lt_pow_right (by decide) (by omega)
  rw [formAt_switchLift_at c vars ⟨part, b, 0⟩ R tb hc hb (Nat.le_of_lt hR) hv
    (by show 0 / 2 ^ b < _; rw [Nat.zero_div]; exact Nat.two_pow_pos _) _ hJ]
  apply if_neg
  rintro ⟨_, h3⟩
  have h3' : 2 ^ b / 2 ^ b % 2 ^ (R - b) = 0 / 2 ^ b := h3
  rw [Nat.div_self hpb, Nat.mod_eq_of_lt h2, Nat.zero_div] at h3'
  cases h3'

end H2K.Lift

#print axioms H2K.Lift.formAt_switchLift_at
#print axioms H2K.Lift.formAt_switchLift_cutIndex
#print axioms H2K.Lift.formAt_switchLift_off
#print axioms H2K.Lift.lift_gap
