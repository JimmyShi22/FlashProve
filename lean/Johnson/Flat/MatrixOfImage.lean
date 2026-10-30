-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/MatrixOfImage.lean: which matrices of field elements are Flat.matrixOf i for an index
i, at the reference shape (3,076,096 rows, 2^18 columns).

No goal of the library is stated or changed here. Six short theorems; no definition.

Words. An index (Cm.Idx, Cm/RelBase.lean) is a well-formed matrix of integer digits of that shape
(WFW, Inst/Model/Layout.lean: each digit from -128 to 127, and a bound on each pair of digits of a
two-byte weight). Flat.GE is the field of the cells: the cubic extension, with p^3 elements, of the
integers modulo p = 2^64 - 2^32 + 1 (Cb.Gl.E, Cb/Gl/GlField.lean). Flat.matrixOf i
(Johnson/Flat/ThreeFull.lean) is the matrix of field elements whose cells are the casts of the
digits of i. From Johnson/Flat/LedgerClaim.lean: Flat.Holds M i says that each cell of M is the
cast of the digit of i at that place, and that i, read as 0 outside its own shape, is 0 outside the
shape of M (always so at the reference shape); Flat.InRange M says that M holds some index;
Flat.RelL s M x is the claim of a request x on M at the table of scales s, at exact match: M holds
an index at which some trace meets the relaxed relation with the cost ledger. Flat.RelLAt pp M x
(Johnson/Top/H/TargetAtPolicy.lean) is the same claim at a table pp of scales and policy.

Main names:
  Flat.eq_matrixOf_of_holds: a matrix that holds the index i is matrixOf i.
  Flat.inRange_iff_matrixOf: M is in range if and only if M = matrixOf i for some index i. So the
    image of matrixOf is the set of matrices in range.
  Flat.RelLAt.exists_matrixOf, Flat.RelL.exists_matrixOf: a matrix at which the claim of a request
    is true is matrixOf i for an index i at which some trace meets the relation.
  Flat.matrixOf_injective: two indices with one matrix are one. So the index in the theorems above
    is the only one with that matrix.
  Flat.exists_not_inRange: some matrix is not in range. So matrixOf does not reach every matrix.
    (By the definitions a cell of a matrix in range is one of 256 field elements; no theorem here
    counts the matrices.)

What it is for. Some statements are written for an index, others for a matrix of field elements
(obj_decodes_index_full and obj_decodes_cells_full in Johnson/Flat/CodingCells.lean are such a
pair). By these theorems a statement that is proved in the form "for every index i, at the matrix
matrixOf i" is true at every matrix in range, and so at every matrix at which the claim of a
request is true. These theorems carry it to no other matrix.

Limits: the reference shape alone. Several indices may have the same weight tensors (the head of
Cm/RelBase.lean: by reading of the layout, no theorem); this file names no map from tensors to an
index. Nothing on a protocol: nothing on soundness, on completeness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.ThreeFull
import Johnson.Top.H.TargetAtPolicy

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles

open Inst.Model
open Inst.Model.Layout (kRef hRef)

/-- A matrix of the reference shape that holds an index is matrixOf of that index. -/
theorem Flat.eq_matrixOf_of_holds {M : Fin hRef → Fin (2 ^ kRef) → Flat.GE} {i : Cm.Idx}
    (h : Flat.Holds M i) : M = Flat.matrixOf i := by
  funext y c
  exact h.1 y c

/-- **The image of matrixOf is the set of matrices in range.** -/
theorem Flat.inRange_iff_matrixOf (M : Fin hRef → Fin (2 ^ kRef) → Flat.GE) :
    Flat.InRange M ↔ ∃ i : Cm.Idx, M = Flat.matrixOf i :=
  ⟨fun ⟨i, h⟩ => ⟨i, Flat.eq_matrixOf_of_holds h⟩, fun ⟨i, e⟩ => e ▸ ⟨i, Flat.holds_matrixOf i⟩⟩

/-- A matrix at which the claim of a request is true, at a table of scales and policy, is matrixOf
of an index at which some trace meets the relaxed relation with the cost ledger. -/
theorem Flat.RelLAt.exists_matrixOf {pp : ScalesAndPolicy} {M : Fin hRef → Fin (2 ^ kRef) → Flat.GE}
    {x : Instance ppref} (h : Flat.RelLAt pp M x) :
    ∃ i : Cm.Idx, M = Flat.matrixOf i ∧ ∃ T, Policy.LedgerRel.Rno Cb.Gl.p pp i x T :=
  let ⟨i, hi, hT⟩ := h
  ⟨i, Flat.eq_matrixOf_of_holds hi, hT⟩

/-- The same for the claim at a table of scales and exact match. -/
theorem Flat.RelL.exists_matrixOf {s : Cm.Scales} {M : Fin hRef → Fin (2 ^ kRef) → Flat.GE}
    {x : Instance ppref} (h : Flat.RelL s M x) :
    ∃ i : Cm.Idx, M = Flat.matrixOf i ∧
      ∃ T, Policy.LedgerRel.Rno Cb.Gl.p (Policy.ppOf s AcceptancePolicy.exact) i x T :=
  Flat.RelLAt.exists_matrixOf (pp := Policy.ppOf s AcceptancePolicy.exact) h

/-- Two indices with one matrix are one. -/
theorem Flat.matrixOf_injective : Function.Injective Flat.matrixOf := fun i i' e =>
  Flat.holds_unique le_rfl le_rfl (Flat.holds_matrixOf i) (e ▸ Flat.holds_matrixOf i')

/-- **Some matrix is not in range**, so matrixOf does not reach every matrix (inRange_iff_matrixOf):
the matrix whose cells are all 128 holds no index, since a digit lies from -128 to 127 and the
field's characteristic is larger than 256. -/
theorem Flat.exists_not_inRange :
    ∃ M : Fin hRef → Fin (2 ^ kRef) → Flat.GE, ¬ Flat.InRange M := by
  refine ⟨fun _ _ => ((128 : ℤ) : Flat.GE), ?_⟩
  rintro ⟨i, h⟩
  have hr : 0 < hRef := by decide
  have hc : 0 < 2 ^ kRef := Nat.two_pow_pos kRef
  have e : ((128 : ℤ) : Flat.GE) = ((i.mat 0 0 : ℤ) : Flat.GE) := h.1 ⟨0, hr⟩ ⟨0, hc⟩
  have d := i.wf.1 0 hr 0 hc
  have h1 : (Cb.Gl.p : ℤ) ∣ i.mat 0 0 - 128 :=
    ((CharP.intCast_eq_intCast Flat.GE Cb.Gl.p).1 e).dvd
  have hp : (256 : ℤ) < (Cb.Gl.p : ℤ) := by
    have e' : Cb.Gl.p = 18446744069414584321 := Code.pGold_eq
    rw [e']
    norm_num
  have h2 : |i.mat 0 0 - 128| < (Cb.Gl.p : ℤ) := by
    refine lt_of_le_of_lt ?_ hp
    rw [abs_le]
    constructor <;> omega
  have h3 := Int.eq_zero_of_abs_lt_dvd h1 h2
  omega

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.Flat.eq_matrixOf_of_holds
#print axioms VerifiableInference.OnPublicFiles.Flat.inRange_iff_matrixOf
#print axioms VerifiableInference.OnPublicFiles.Flat.RelLAt.exists_matrixOf
#print axioms VerifiableInference.OnPublicFiles.Flat.RelL.exists_matrixOf
#print axioms VerifiableInference.OnPublicFiles.Flat.matrixOf_injective
#print axioms VerifiableInference.OnPublicFiles.Flat.exists_not_inRange
