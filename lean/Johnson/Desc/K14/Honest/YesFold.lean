--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/YesFold.lean: the constraint (fold) of the linear claim's shared rounds can
be made, and the two groups take the two constraints that "SPLIT" makes of it.

(fold) ties the message o_omega to the message o_u (Johnson/Desc/K14/Text.lean: fold). The two
messages lie in two groups, so "SPLIT" cuts the constraint in two: the part on o_omega, plus an
entry kappa of the mask message o_sp, goes to the group of o_omega; the part on o_u, minus kappa,
goes to the group of o_u (Johnson/Desc/K14/Law/Base.lean: onOmega, onU).

Main names:
  fold_makes, fold_made   (fold) can be made where the two points have the planned numbers of
                      coordinates; what it is made of
  fold_coefficient, fold_far   its coefficient on an entry; it reads as 0 behind the matrix's rows
                      in o_omega's table, behind the matrix in o_u's table, and on every other table
  part_names, part_off, part_on   the part of a constraint on some messages names these alone; it
                      reads as 0 on the others, and as the constraint on these
  SplitFacts          facts on the statement, the two groups and kappa
  onOmega_fits, onU_fits   **the two groups take the two constraints** (Fits)

What is not claimed. That SplitFacts holds at any statement. Nothing on what the constraints mean,
on soundness, on completeness or on hiding.

-/
import Johnson.Desc.K14.Honest.YesRec
import Johnson.Desc.K14.Law.Carry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Model (Reading)
open OnBytes.Means (Fits)
open OnBytes.Slice (index_entryAt entryAt_lt)
open VerifiableInference.Desc.Ground (ok)
open Desc.K14.Law (coefficient_addLaid coefficient_empty coefficient_addUnit coefficient_off
  le_two_pow_ceilLog2 tensorBelow_mem part_add onOmega onU)

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## (fold) -/

/-- **(fold) can be made.** -/
theorem fold_makes (S : LinShape) (l : Lin) (lay : VectorLay) (hpsi : l.psiSh.length = S.kCol)
    (hz : l.zFd.length = S.kRow) : ∃ row, fold S l lay = some row := by
  have hok : ok (foldL S l) = true := by
    simp only [ok, foldL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq]
    exact ⟨hpsi, hz⟩
  obtain ⟨A, hA⟩ := tensorBelow_makes (Tensor.eq l.zFd) rfl 0 S.kRow S.matrixRows
    (by rw [vars_eq, hz]; omega) (le_two_pow_ceilLog2 _)
  obtain ⟨B, hB⟩ := tensorBelow_makes (Tensor.eq (l.psiSh.take S.kLo ++ l.zFd) (negE oneE)) rfl
    S.kLo S.kRow S.matrixRows
    (by
      rw [vars_eq, List.length_append, List.length_take, hz, hpsi]
      unfold LinShape.kCol
      omega)
    (le_two_pow_ceilLog2 _)
  refine ⟨l.oU.addAll (addLaid {} l.oOmega lay A) B, ?_⟩
  unfold fold
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq]
  exact ⟨(), by simp [guard, hok], A, hA, B, hB, rfl⟩

/-- What (fold) is made of. -/
theorem fold_made (S : LinShape) (l : Lin) (lay : VectorLay) (row : Row)
    (h : fold S l lay = some row) :
    ∃ A B : List Tensor, l.psiSh.length = S.kCol ∧ l.zFd.length = S.kRow ∧
      tensorBelow (Tensor.eq l.zFd) 0 S.kRow S.matrixRows = some A ∧
      tensorBelow (Tensor.eq (l.psiSh.take S.kLo ++ l.zFd) (negE oneE)) S.kLo S.kRow
        S.matrixRows = some B ∧
      row = l.oU.addAll (addLaid {} l.oOmega lay A) B := by
  unfold fold at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨u0, hg, A, hA, B, hB, hrow⟩ := h
  have hok : ok (foldL S l) = true := by
    by_contra hne
    simp [guard, hne] at hg
  simp only [ok, foldL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq] at hok
  exact ⟨A, B, hok.1, hok.2, hA, hB, hrow.symm⟩

/-- (fold)'s coefficient on an entry. -/
theorem fold_coefficient (l : Lin) (lay : VectorLay) (A B : List Tensor) (o : Nat) (pt : Part)
    (i : Nat) :
    ρ.val ((l.oU.addAll (addLaid {} l.oOmega lay A) B).coefficient o pt i) =
      (if l.oOmega = o ∧ Part.main = pt then
        (A.map fun t => ρ.val ((lay.onTable t).entry i)).sum else 0) +
      (if l.oU.oracle = o ∧ Part.main = pt then
        (B.map fun t => ρ.val ((l.oU.lay.onTable t).entry i)).sum else 0) := by
  unfold FoldedRow.addAll
  rw [coefficient_addLaid, coefficient_addLaid, coefficient_empty, zero_add]

/-- (fold) reads as 0 behind the matrix's rows in o_omega's table, behind the matrix in o_u's table,
and on every other table. -/
theorem fold_far (S : LinShape) (l : Lin) (lay : VectorLay) (A B : List Tensor)
    (hpsi : l.psiSh.length = S.kCol) (hz : l.zFd.length = S.kRow)
    (hA : tensorBelow (Tensor.eq l.zFd) 0 S.kRow S.matrixRows = some A)
    (hB : tensorBelow (Tensor.eq (l.psiSh.take S.kLo ++ l.zFd) (negE oneE)) S.kLo S.kRow
      S.matrixRows = some B)
    (hrO : S.kRow ≤ lay.bits) (hrU : S.kLo + S.kRow ≤ l.oU.lay.bits) (o : Nat) (pt : Part)
    (idx : Nat)
    (hO : l.oOmega = o → Part.main = pt → idx < 2 ^ lay.bits ∧ S.matrixRows ≤ lay.entryAt idx)
    (hU : l.oU.oracle = o → Part.main = pt →
      idx < 2 ^ l.oU.lay.bits ∧ S.matrixRows * 2 ^ S.kLo ≤ l.oU.lay.entryAt idx) :
    ρ.val ((l.oU.addAll (addLaid {} l.oOmega lay A) B).coefficient o pt idx) = 0 := by
  have hvA : (Tensor.eq l.zFd).vars = S.kRow := by rw [vars_eq, hz]
  have hvB : (Tensor.eq (l.psiSh.take S.kLo ++ l.zFd) (negE oneE)).vars = S.kLo + S.kRow := by
    rw [vars_eq, List.length_append, List.length_take, hz, hpsi]
    unfold LinShape.kCol
    omega
  rw [fold_coefficient]
  have z1 : (if l.oOmega = o ∧ Part.main = pt then
      (A.map fun t => ρ.val ((lay.onTable t).entry idx)).sum else 0) = 0 := by
    by_cases h : l.oOmega = o ∧ Part.main = pt
    · rw [if_pos h]
      obtain ⟨hi, hk⟩ := hO h.1 h.2
      have z := laid_cut_zero ρ lay (Tensor.eq l.zFd) rfl 0 S.kRow S.matrixRows A hA
        (by rw [hvA]; exact hrO) (lay.entryAt idx) (entryAt_lt lay idx hi) (by
          intro hlt
          rw [hvA] at hlt
          rw [Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt hlt]
          exact hk)
      rw [index_entryAt lay idx hi] at z
      exact z
    · rw [if_neg h]
  have z2 : (if l.oU.oracle = o ∧ Part.main = pt then
      (B.map fun t => ρ.val ((l.oU.lay.onTable t).entry idx)).sum else 0) = 0 := by
    by_cases h : l.oU.oracle = o ∧ Part.main = pt
    · rw [if_pos h]
      obtain ⟨hi, hk⟩ := hU h.1 h.2
      have z := laid_cut_zero ρ l.oU.lay (Tensor.eq (l.psiSh.take S.kLo ++ l.zFd) (negE oneE)) rfl
        S.kLo S.kRow S.matrixRows B hB (by rw [hvB]; exact hrU) (l.oU.lay.entryAt idx)
        (entryAt_lt l.oU.lay idx hi) (by
          intro hlt
          rw [hvB, Nat.pow_add] at hlt
          rw [Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul hlt)]
          exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).2 hk)
      rw [index_entryAt l.oU.lay idx hi] at z
      exact z
    · rw [if_neg h]
  rw [z1, z2, add_zero]

/-! ## The part of a constraint on some messages -/

/-- The part of a constraint names messages of its own side alone. -/
theorem part_names (row : Row) (m : Array Nat) (b : Bool) (o : Nat)
    (h : o ∈ (part row m b).oracles) : (m.contains o == b) = true := by
  simp only [Row.oracles, part, List.mem_append, Array.toList_map, List.mem_map,
    Array.toList_filter, List.mem_filter] at h
  rcases h with
    ((⟨t, ⟨_, ht⟩, rfl⟩ | ⟨t, ⟨_, ht⟩, rfl⟩) | ⟨t, ⟨_, ht⟩, rfl⟩) | ⟨t, ⟨_, ht⟩, rfl⟩ <;>
  exact ht

/-- It reads as 0 on the messages of the other side. -/
theorem part_off (row : Row) (m : Array Nat) (b : Bool) (o : Nat) (h : m.contains o ≠ b)
    (pt : Part) (i : Nat) : ρ.val ((part row m b).coefficient o pt i) = 0 :=
  coefficient_off ρ _ o (fun hm => h (by simpa using part_names row m b o hm)) pt i

/-- It reads as the constraint on the messages of its own side. -/
theorem part_on (row : Row) (m : Array Nat) (b : Bool) (o : Nat) (h : m.contains o = b)
    (pt : Part) (i : Nat) :
    ρ.val ((part row m b).coefficient o pt i) = ρ.val (row.coefficient o pt i) := by
  have hadd := part_add ρ row m o pt i
  cases b with
  | false =>
    rw [part_off ρ row m true o (by rw [h]; decide) pt i, zero_add] at hadd
    exact hadd
  | true =>
    rw [part_off ρ row m false o (by rw [h]; decide) pt i, add_zero] at hadd
    exact hadd

/-- A structured summand of a part is one of the constraint's, of the part's side. -/
theorem mem_part_terms (row : Row) (m : Array Nat) (b : Bool) (t : Term)
    (h : t ∈ (part row m b).terms) : t ∈ row.terms ∧ (m.contains t.oracle == b) = true := by
  have h' : t ∈ row.terms.filter (m.contains ·.oracle == b) := h
  exact Array.mem_filter.1 h'

/-! ## The two constraints that "SPLIT" lays -/

/-- Facts on the statement, the two groups and the mask entry kappa. -/
structure SplitFacts (T : Statement) (S : LinShape) (l : Lin) (lay : VectorLay) (GU GO : Group)
    (kappa : Nat) : Prop where
  omega : Sits T GO l.oOmega lay S.matrixRows
  u : Sits T GU l.oU.oracle l.oU.lay (S.matrixRows * 2 ^ S.kLo)
  uOut : GO.members.contains l.oU.oracle = false
  spO : GO.members.contains l.oSp = true
  spU : GU.members.contains l.oSp = true
  mask : T.has l.oSp .mask = true
  inside : kappa < 2 ^ T.tableBits l.oSp .mask
  /-- kappa masks no answer -/
  free : ∀ x, T.oracles[l.oSp]? = some x → (Part.mask, kappa) ∉ x.pad
  bitsOmega : S.kRow ≤ lay.bits
  bitsU : S.kLo + S.kRow ≤ l.oU.lay.bits

/-- The mask entry fits its place in a group that has o_sp as a member. -/
theorem kappa_fits {T : Statement} {S : LinShape} {l : Lin} {lay : VectorLay} {GU GO : Group}
    {kappa : Nat} (h : SplitFacts T S l lay GU GO kappa) (G : Group)
    (hm : G.members.contains l.oSp = true) :
    VerifiableInference.Desc.Own.placeFits T G l.oSp .mask (T.tableBits l.oSp .mask) kappa =
      true := by
  unfold VerifiableInference.Desc.Own.placeFits
  rw [hm, tableThere_of_has T l.oSp .mask h.mask]
  simp [h.inside]

/-- What both constraints read as on an entry that masks an answer: nothing. c: the coefficient on
kappa. -/
theorem split_pad {T : Statement} {S : LinShape} {l : Lin} {lay : VectorLay} {GU GO : Group}
    {kappa : Nat} (h : SplitFacts T S l lay GU GO kappa) (A B : List Tensor)
    (hpsi : l.psiSh.length = S.kCol) (hz : l.zFd.length = S.kRow)
    (hA : tensorBelow (Tensor.eq l.zFd) 0 S.kRow S.matrixRows = some A)
    (hB : tensorBelow (Tensor.eq (l.psiSh.take S.kLo ++ l.zFd) (negE oneE)) S.kLo S.kRow
      S.matrixRows = some B) (b : Bool) (c : E) (o : Nat) (x : Oracle)
    (hx : T.oracles[o]? = some x) (q : Part × Nat) (hq : q ∈ x.pad) :
    ρ.val (((part (l.oU.addAll (addLaid {} l.oOmega lay A) B) GO.members b).addUnit l.oSp .mask
      kappa c).coefficient o q.1 q.2) = 0 := by
  rw [coefficient_addUnit]
  have z2 : (if l.oSp = o ∧ Part.mask = q.1 ∧ kappa = q.2 then ρ.val c else 0) = 0 := by
    refine if_neg fun e => ?_
    obtain ⟨e1, e2, e3⟩ := e
    subst e1
    refine h.free x hx ?_
    have : q = (Part.mask, kappa) := by rw [e2, e3]
    rw [← this]
    exact hq
  rw [z2, add_zero]
  by_cases hb : GO.members.contains o = b
  · rw [part_on ρ _ _ b o hb]
    refine fold_far ρ S l lay A B hpsi hz hA hB h.bitsOmega h.bitsU o q.1 q.2 ?_ ?_
    · intro e1 e2
      subst e1
      exact h.omega.pad x hx q hq e2.symm
    · intro e1 e2
      subst e1
      exact h.u.pad x hx q hq e2.symm
  · exact part_off ρ _ _ b o hb _ _

/-- **The group of o_omega takes its constraint.** -/
theorem onOmega_fits {T : Statement} {S : LinShape} {l : Lin} {lay : VectorLay} {GU GO : Group}
    {kappa : Nat} (h : SplitFacts T S l lay GU GO kappa) (row : Row)
    (hf : fold S l lay = some row) (mu : E) :
    Fits T GO (onOmega row GO.members l.oSp kappa mu) := by
  obtain ⟨A, B, hpsi, hz, hA, hB, rfl⟩ := fold_made S l lay row hf
  have hvA : (Tensor.eq l.zFd).vars = S.kRow := by rw [vars_eq, hz]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    cases e
  · intro t ht
    have ht' : t ∈ (part (l.oU.addAll (addLaid {} l.oOmega lay A) B) GO.members true).terms := ht
    obtain ⟨h1, h2⟩ := mem_part_terms _ _ _ _ ht'
    unfold FoldedRow.addAll at h1
    rcases mem_addLaid _ _ _ _ _ h1 with h3 | ⟨v, hv, rfl⟩
    · rcases mem_addLaid _ _ _ _ _ h3 with h4 | ⟨v, hv, rfl⟩
      · simp at h4
      · obtain ⟨d1, d2⟩ := tensorBelow_mem _ rfl _ _ _ _ hA v hv
        exact laid_term_fits h.omega v d1 (by rw [d2, hvA]; exact h.bitsOmega)
    · have h5 : (GO.members.contains l.oU.oracle == true) = true := h2
      rw [h.uOut] at h5
      cases h5
  · intro y hy
    have hy' : y ∈ ((part (l.oU.addAll (addLaid {} l.oOmega lay A) B) GO.members true).units.push
      ⟨l.oSp, .mask, kappa, oneE⟩) := hy
    rcases Array.mem_push.1 hy' with h1 | rfl
    · have h2 : y ∈ (l.oU.addAll (addLaid {} l.oOmega lay A) B).units.filter
        (GO.members.contains ·.oracle == true) := h1
      have h3 := (Array.mem_filter.1 h2).1
      unfold FoldedRow.addAll at h3
      rw [units_addLaid, units_addLaid] at h3
      simp at h3
    · exact kappa_fits h GO h.spO
  · show (l.oU.addAll (addLaid {} l.oOmega lay A) B).runs.filter
      (GO.members.contains ·.oracle == true) = #[]
    unfold FoldedRow.addAll
    rw [runs_addLaid, runs_addLaid]
    rfl
  · show (l.oU.addAll (addLaid {} l.oOmega lay A) B).forms.filter
      (GO.members.contains ·.oracle == true) = #[]
    unfold FoldedRow.addAll
    rw [forms_addLaid, forms_addLaid]
    rfl
  · intro o _ x hx q hq
    exact split_pad Model.Reading.gl h A B hpsi hz hA hB true oneE o x hx q hq

/-- **The group of o_u takes its constraint.** -/
theorem onU_fits {T : Statement} {S : LinShape} {l : Lin} {lay : VectorLay} {GU GO : Group}
    {kappa : Nat} (h : SplitFacts T S l lay GU GO kappa) (row : Row)
    (hf : fold S l lay = some row) (mu : E) :
    Fits T GU (onU row GO.members l.oSp kappa mu) := by
  obtain ⟨A, B, hpsi, hz, hA, hB, rfl⟩ := fold_made S l lay row hf
  have hvB : (Tensor.eq (l.psiSh.take S.kLo ++ l.zFd) (negE oneE)).vars = S.kLo + S.kRow := by
    rw [vars_eq, List.length_append, List.length_take, hz, hpsi]
    unfold LinShape.kCol
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    cases e
  · intro t ht
    have ht' : t ∈ (part (l.oU.addAll (addLaid {} l.oOmega lay A) B) GO.members false).terms := ht
    obtain ⟨h1, h2⟩ := mem_part_terms _ _ _ _ ht'
    unfold FoldedRow.addAll at h1
    rcases mem_addLaid _ _ _ _ _ h1 with h3 | ⟨v, hv, rfl⟩
    · rcases mem_addLaid _ _ _ _ _ h3 with h4 | ⟨v, hv, rfl⟩
      · simp at h4
      · have h5 : (GO.members.contains l.oOmega == false) = true := h2
        rw [h.omega.member] at h5
        cases h5
    · obtain ⟨d1, d2⟩ := tensorBelow_mem _ rfl _ _ _ _ hB v hv
      exact laid_term_fits h.u v d1 (by rw [d2, hvB]; exact h.bitsU)
  · intro y hy
    have hy' : y ∈ ((part (l.oU.addAll (addLaid {} l.oOmega lay A) B) GO.members false).units.push
      ⟨l.oSp, .mask, kappa, negE oneE⟩) := hy
    rcases Array.mem_push.1 hy' with h1 | rfl
    · have h2 : y ∈ (l.oU.addAll (addLaid {} l.oOmega lay A) B).units.filter
        (GO.members.contains ·.oracle == false) := h1
      have h3 := (Array.mem_filter.1 h2).1
      unfold FoldedRow.addAll at h3
      rw [units_addLaid, units_addLaid] at h3
      simp at h3
    · exact kappa_fits h GU h.spU
  · show (l.oU.addAll (addLaid {} l.oOmega lay A) B).runs.filter
      (GO.members.contains ·.oracle == false) = #[]
    unfold FoldedRow.addAll
    rw [runs_addLaid, runs_addLaid]
    rfl
  · show (l.oU.addAll (addLaid {} l.oOmega lay A) B).forms.filter
      (GO.members.contains ·.oracle == false) = #[]
    unfold FoldedRow.addAll
    rw [forms_addLaid, forms_addLaid]
    rfl
  · intro o _ x hx q hq
    exact split_pad Model.Reading.gl h A B hpsi hz hA hB false (negE oneE) o x hx q hq

end Desc.K14.Honest

#print axioms Desc.K14.Honest.fold_makes
#print axioms Desc.K14.Honest.fold_made
#print axioms Desc.K14.Honest.fold_coefficient
#print axioms Desc.K14.Honest.fold_far
#print axioms Desc.K14.Honest.part_names
#print axioms Desc.K14.Honest.part_off
#print axioms Desc.K14.Honest.part_on
#print axioms Desc.K14.Honest.mem_part_terms
#print axioms Desc.K14.Honest.kappa_fits
#print axioms Desc.K14.Honest.split_pad
#print axioms Desc.K14.Honest.onOmega_fits
#print axioms Desc.K14.Honest.onU_fits
