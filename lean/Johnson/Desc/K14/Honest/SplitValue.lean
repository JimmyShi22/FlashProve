--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/SplitValue.lean: the scalar that an honest prover sends at "SPLIT", written
out: omega_col at the point z_fd, over the rows of the matrix, plus the mask's entry.

  mem_oracles_part, coefficient_part_true   the part of a constraint on the messages of a list has
                  the constraint's coefficients on these messages, and 0 elsewhere
  fold_coeffs        what (fold) is made of, and its coefficients, read
  value_partOmega the part of (fold) on G_omega, applied to words
  muVal_formula   **the honest scalar**: the sum of eq(z_fd, j) omega_col[j] over the matrix's rows,
                  plus the mask's entry

What is assumed. The two messages of (fold) have their tables (Placed); o_omega is among the listed
messages and o_u is not; the mask message is there and the entry lies within its mask table.
What is not claimed. Nothing on a verifier's yes, on soundness or on hiding.

-/
import Johnson.Desc.K14.Honest.SplitSays
import Johnson.Desc.K14.Law.MeansRec
import Johnson.Desc.K14.Law.Carry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Means (Words)
open VerifiableInference.Desc.Ground (ok)
open Desc.K14.Law

variable {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)

/-- A message that a part of a constraint names has passed the part's test. -/
theorem mem_oracles_part (row : Row) (members : Array Nat) (b : Bool) (o : Nat)
    (h : o ∈ (part row members b).oracles) : (members.contains o == b) = true := by
  simp only [Row.oracles, part, List.mem_append, Array.toList_map, List.mem_map,
    Array.toList_filter, List.mem_filter] at h
  rcases h with ((⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩
  · exact ht.2
  · exact ht.2
  · exact ht.2
  · exact ht.2

/-- The part of a constraint on the listed messages: the constraint's coefficients there, 0
elsewhere. -/
theorem coefficient_part_true (row : Row) (members : Array Nat) (o : Nat) (pt : Part) (i : Nat) :
    ρ.val ((part row members true).coefficient o pt i) =
      if members.contains o = true then ρ.val (row.coefficient o pt i) else 0 := by
  by_cases c : members.contains o = true
  · rw [if_pos c]
    have hoff : o ∉ (part row members false).oracles := fun h => by
      have h' := beq_iff_eq.1 (mem_oracles_part row members false o h)
      rw [c] at h'
      cases h'
    have e := part_add ρ row members o pt i
    rw [coefficient_off ρ _ o hoff, add_zero] at e
    exact e
  · rw [if_neg c]
    exact coefficient_off ρ _ o
      (fun h => c (beq_iff_eq.1 (mem_oracles_part row members true o h))) pt i

/-- What (fold) is made of, and its coefficients, read. -/
theorem fold_coeffs (S : LinShape) (l : Lin) (lay : VectorLay) (row : Row)
    (hf : fold S l lay = some row) :
    ∃ A B : List Tensor, l.zFd.length = S.kRow ∧
      tensorBelow (Tensor.eq l.zFd) 0 S.kRow S.matrixRows = some A ∧
      ∀ o pt i, ρ.val (row.coefficient o pt i) =
        (if l.oOmega = o ∧ Part.main = pt then
          (A.map fun t => ρ.val ((lay.onTable t).entry i)).sum else 0) +
        (if l.oU.oracle = o ∧ Part.main = pt then
          (B.map fun t => ρ.val ((l.oU.lay.onTable t).entry i)).sum else 0) := by
  unfold fold at hf
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hf
  obtain ⟨u0, hg, A, hA, B, hB, hrow⟩ := hf
  have hok : ok (foldL S l) = true := by
    by_contra hne
    simp [guard, hne] at hg
  simp only [ok, foldL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq] at hok
  refine ⟨A, B, hok.2, hA, fun o pt i => ?_⟩
  rw [← hrow]
  unfold FoldedRow.addAll
  rw [coefficient_addLaid, coefficient_addLaid, coefficient_empty, zero_add]

/-- **The part of (fold) on G_omega, applied to words**: omega_col at z_fd, over the matrix's
rows. -/
theorem value_partOmega (T : Statement) (S : LinShape) (l : Lin) (lay : VectorLay) (row : Row)
    (members : Array Nat) (m : Words K) (hf : fold S l lay = some row) (hP : Placed T S l lay)
    (hO : members.contains l.oOmega = true) (hU : members.contains l.oU.oracle = false) :
    Means.value ρ T (part row members true) m =
      ∑ j ∈ Finset.range S.matrixRows, eqK (l.zFd.map ρ.val) j * omegaOf l lay m j := by
  obtain ⟨A, B, hz, hA, hc⟩ := fold_coeffs ρ S l lay row hf
  have hR : S.matrixRows ≤ 2 ^ S.kRow := le_two_pow_ceilLog2 _
  have hvA : (Tensor.eq l.zFd).vars = S.kRow := by
    simp only [Tensor.eq, Tensor.vars, List.length_map, hz]
  have hc' : ∀ o pt i, ρ.val ((part row members true).coefficient o pt i) =
      if l.oOmega = o ∧ Part.main = pt then
        (A.map fun t => ρ.val ((lay.onTable t).entry i)).sum else 0 := by
    intro o pt i
    rw [coefficient_part_true, hc]
    by_cases c : members.contains o = true
    · have hne : ¬ (l.oU.oracle = o ∧ Part.main = pt) := fun e => by
        rw [← e.1, hU] at c
        cases c
      rw [if_pos c, if_neg hne, add_zero]
    · have hne : ¬ (l.oOmega = o ∧ Part.main = pt) := fun e => c (by rw [← e.1]; exact hO)
      rw [if_neg c, if_neg hne]
  rw [value_one ρ T _ l.oOmega lay.bits _ hc' hP.hasOmega hP.bitsOmega m,
    cut_laid_sum ρ lay _ rfl 0 S.kRow S.matrixRows A hA (by rw [hvA]; exact hP.roomOmega), hvA]
  refine Eq.trans ?_ (sum_below_len (2 ^ S.kRow) S.matrixRows hR
    fun j => eqK (l.zFd.map ρ.val) j * omegaOf l lay m j)
  refine Finset.sum_congr rfl fun j hj => ?_
  have e : j / 2 ^ 0 % 2 ^ S.kRow = j := by
    rw [Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt (Finset.mem_range.1 hj)]
  rw [e, entry_eq, ρ.one, one_mul]
  unfold omegaOf
  split_ifs <;> simp

/-- **The honest scalar, written out.** -/
theorem muVal_formula (T : Statement) (S : LinShape) (l : Lin) (lay : VectorLay) (row : Row)
    (members : Array Nat) (kappa : Nat) (m : Words K) (hf : fold S l lay = some row)
    (hP : Placed T S l lay) (hO : members.contains l.oOmega = true)
    (hU : members.contains l.oU.oracle = false) (ho : l.oSp < T.oracles.size)
    (hk : kappa < Means.tableSize T l.oSp .mask) :
    muVal ρ T row members l.oSp kappa m =
      (∑ j ∈ Finset.range S.matrixRows, eqK (l.zFd.map ρ.val) j * omegaOf l lay m j) +
        m l.oSp .mask kappa := by
  rw [muVal_eq ρ T row members l.oSp kappa m ho hk,
    value_partOmega ρ T S l lay row members m hf hP hO hU]

end Desc.K14.Honest

#print axioms Desc.K14.Honest.mem_oracles_part
#print axioms Desc.K14.Honest.coefficient_part_true
#print axioms Desc.K14.Honest.fold_coeffs
#print axioms Desc.K14.Honest.value_partOmega
#print axioms Desc.K14.Honest.muVal_formula
