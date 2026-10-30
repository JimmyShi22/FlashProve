-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/TableHidesGuardAtFiles.lean: the guard of E2E/TableHidesGuard.lean at the object at public files
Z (E2E/ObjectAtFiles.lean), on all matrices and cut to the matrices in range. Statements and proofs.

What is shown.
  **`not_hidE_filesAt`**: at EVERY Z and for all provers P: the clause `hidE` of `HolographicProtocol.ReadsR`
    (`HidE`, E2E/TableHides.lean) fails at 44,040,192 at `(filesAt Z).withProvers P`. At 44,040,191 it holds
    there (`hidE_filesAt`, E2E/ReadsAtFiles.lean).
  `not_reads_filesAt`: so `HolographicProtocol.ReadsR` fails there at 44,040,192, whatever its four counts.
  `Differ.not_hidE_cut`: two indices that differ, both within a cut of the index type: the clause
    fails at the cut object. General.
  `zero_eq_matrixOf`, `oneCell_eq_matrixOf`: the guard's two matrices are the matrices of two
    indices of the integer model (`idxA`, `idxB`, E2E/ObjectGuards.lean), so both are in range.
  **`not_hidE_objAt`**, `not_reads_objAt`: so the clause, and `HolographicProtocol.ReadsR`, fail at 44,040,192 at
    the object cut to the matrices in range (`objAt Z P`) too, at every Z and for all provers.
  **`every_set_filesAt`**, **`every_set_objAt`**: at both objects, at EVERY set of 44,040,192
    positions, in the clause's own words (`SameAt`, E2E/TableHidesGuard.lean): at the OOD seed
    `seedOne` the two laws are not one at the two matrices (`ixOne`, `ixZero`: as matrices in
    range).

Limits. Those of E2E/TableHidesGuard.lean: some OOD seed (a corner, at which the OOD answers read no
cell), some two matrices; no size of the difference is stated; typed for the clause's form with all
OOD seeds alone; the clause is a premise of the library's theorem on the whole object, and that the
result itself fails there is typed by no environment. "At every Z and for all provers" is no
strength: the clause reads neither.
An index of the integer model (`Cm.Idx`) is a matrix of whole numbers that meets the library's
condition on such matrices. By the library's own comment (IntegerModel/Arrays/OfIndex.lean) not
every entry of such a matrix is kept on the way to weights and back. That the guard's two matrices
are those of two sets of weights is not shown.

BESIDE EVERY TELLING of the result on the index's committed tables, to which this file belongs
(E2E/WholeViewAtFiles.lean, E2E/TablesAtOwnObject.lean):
- placeholder provers: no message of the protocol is covered; it is not zero knowledge;
- before compilation: no hashing; each OOD seed is chosen before its table's coins are drawn, from
  nothing but what has been shown and coins of the environment's own: of a seed that hangs on
  anything hidden, another table's pads too, nothing is said;
- fresh uniform pads and encoding randomness for each table (as run: derived from the committer's
  secret seed); one OOD sample a table; one set of public files. One table's randomness is used
  under one set of public files alone. The same rows and pads under other public files would get
  another seed, and of two OOD samples on one table's pads this file says nothing.
- the budget is table by table, is kept by nobody, and has no slack: at one column more the
  interface's clause on the encoder fails (a theorem: some OOD seed, two matrices in range, at every
  set of that size; it states no size of the difference, only that the two laws differ; typed for
  the form with all OOD seeds alone); that the result itself fails there is typed by no environment;
- that the IOP's own tests on the public files pass is shown in the side library: at the library's
  two named sets of public files (AtFullSide/E2E/AtWrittenFiles.lean), and at the first set's files
  under every policy within four bounds (`theLive_zAt`, AtFullSide/Top/LiveAtPolicies.lean); no
  theorem ties any of these to a file on a disk.


-/
import E2E.TableHidesGuard
import E2E.ObjectAtFiles
import E2E.ObjectGuards

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Table
open Iop Hiop

/-- **At the object at public files Z**, at every Z and for all provers: the clause fails at
44,040,192, and with it `HolographicProtocol.ReadsR` at that number, whatever the four counts. -/
theorem not_hidE_filesAt (Z : VerifierAndGoals.PublicFiles) (P : (AtPublicFiles.AtFiles.filesAt Z).Provers) :
    ¬ HidE ((AtPublicFiles.AtFiles.filesAt Z).withProvers P) 44040192 :=
  not_hidE_full _ Subtype.val (AtPublicFiles.AtFiles.filesAt Z) P

theorem not_reads_filesAt (Z : VerifierAndGoals.PublicFiles) (P : (AtPublicFiles.AtFiles.filesAt Z).Provers)
    (qT qpar qch qon : ℕ) :
    ¬ ((AtPublicFiles.AtFiles.filesAt Z).withProvers P).ReadsR 44040192 qT qpar qch qon :=
  fun h => not_hidE_filesAt Z P (hidE_of_reads h)

/-! ## At the object cut to the matrices in range -/

/-- Two indices that differ, both within a cut of the index type: the clause fails at the cut
object. General in the configuration, the protocols, the provers and the cut. -/
theorem Differ.not_hidE_cut {C : ConfigurationWithOutOfDomainSample} (F : OnBytes.Flat.Files C) (P : F.Provers)
    (p : C.I → Prop) {b : ℕ} {i i' : C.I} (h : Differ C b i i') (hi : p i) (hi' : p i') :
    ¬ HidE (AtPublicFiles.Cut.cut (F.withProvers P) p) b := fun H => by
  obtain ⟨Q, s, hQ, hne⟩ := h
  exact hne (H Q hQ s ⟨i, hi⟩ ⟨i', hi'⟩)

/-- The matrix 0 is the matrix of the index with all entries 0. -/
theorem zero_eq_matrixOf :
    (fun _ _ => 0 : AtPublicFiles.AtFiles.FullSizeMatrix) =
      VerifiableInference.OnPublicFiles.Flat.matrixOf AtPublicFiles.AtFiles.idxA := by
  funext y c
  show (0 : OnBytes.Slice.GE) = ((Cm.ext AtPublicFiles.AtFiles.idxA.val y.val c.val : ℤ) : OnBytes.Slice.GE)
  rw [Cm.ext_in _ y.isLt c.isLt]
  exact Int.cast_zero.symm

/-- The matrix with the one cell 1 is the matrix of the index with the entry 1 in row 0, column 0.
-/
theorem oneCell_eq_matrixOf :
    (oneCell OnBytes.Slice.frS 402653181 VerifiableInference.OnPublicFiles.numsRef OnBytes.Slice.frZ :
      AtPublicFiles.AtFiles.FullSizeMatrix) = VerifiableInference.OnPublicFiles.Flat.matrixOf AtPublicFiles.AtFiles.idxB := by
  funext y c
  show (if y.val = 0 ∧ c.val = 0 then (1 : OnBytes.Slice.GE) else 0) =
    ((Cm.ext AtPublicFiles.AtFiles.idxB.val y.val c.val : ℤ) : OnBytes.Slice.GE)
  rw [Cm.ext_in _ y.isLt c.isLt]
  show _ = (((if y.val = 0 ∧ c.val = 0 then 1 else 0 : ℤ)) : OnBytes.Slice.GE)
  by_cases h : y.val = 0 ∧ c.val = 0
  · rw [if_pos h, if_pos h, Int.cast_one]
  · rw [if_neg h, if_neg h, Int.cast_zero]

/-- **At the object cut to the matrices in range**, at every Z and for all provers: the clause fails
at 44,040,192: the two matrices are in range. -/
theorem not_hidE_objAt (Z : VerifierAndGoals.PublicFiles) (P : (AtPublicFiles.AtFiles.filesAt Z).Provers) :
    ¬ HidE (AtPublicFiles.AtFiles.objAt Z P) 44040192 :=
  Differ.not_hidE_cut (AtPublicFiles.AtFiles.filesAt Z) P AtPublicFiles.AtFiles.inRange
    (differ_full _ _ Subtype.val)
    (oneCell_eq_matrixOf ▸ (AtPublicFiles.AtFiles.ixOf AtPublicFiles.AtFiles.idxB).2)
    (zero_eq_matrixOf ▸ (AtPublicFiles.AtFiles.ixOf AtPublicFiles.AtFiles.idxA).2)

/-! ## At every set of 44,040,192 positions, in the clause's own words -/

/-- **At the object at public files Z, at EVERY set Q of 44,040,192 positions**: at the OOD seed
`seedOne` the two laws of the clause are not one at the two matrices. -/
theorem every_set_filesAt (Z : VerifierAndGoals.PublicFiles) (P : (AtPublicFiles.AtFiles.filesAt Z).Provers)
    (Q : Finset OnBytes.Slice.frS.Pos) (hQ : Q.card = 44040192) :
    ¬ SameAt ((AtPublicFiles.AtFiles.filesAt Z).withProvers P) Q (seedOne OnBytes.Slice.frS 29)
      (oneCell OnBytes.Slice.frS 402653181 VerifiableInference.OnPublicFiles.numsRef OnBytes.Slice.frZ)
      (fun _ _ => 0) :=
  (differ_at_full _ _ Subtype.val Q hQ).obj (AtPublicFiles.AtFiles.filesAt Z) P

/-- What differs at the configuration, at two indices within a cut of the index type, differs at the
cut object, in the clause's own words. General in the configuration, the protocols, the provers and
the cut. -/
theorem DifferAt.cut {C : ConfigurationWithOutOfDomainSample} (F : OnBytes.Flat.Files C) (P : F.Provers) (p : C.I → Prop)
    {Q : Finset (Fin C.n)} {s : C.Seed} {i i' : C.I} (h : DifferAt C Q s i i') (hi : p i)
    (hi' : p i') : ¬ SameAt (AtPublicFiles.Cut.cut (F.withProvers P) p) Q s ⟨i, hi⟩ ⟨i', hi'⟩ := h

/-- The guard's matrix with the one cell 1, as a matrix in range. -/
def ixOne : AtPublicFiles.AtFiles.Ix :=
  ⟨oneCell OnBytes.Slice.frS 402653181 VerifiableInference.OnPublicFiles.numsRef OnBytes.Slice.frZ,
    oneCell_eq_matrixOf ▸ (AtPublicFiles.AtFiles.ixOf AtPublicFiles.AtFiles.idxB).2⟩

/-- The matrix 0, as a matrix in range. -/
def ixZero : AtPublicFiles.AtFiles.Ix :=
  ⟨fun _ _ => 0, zero_eq_matrixOf ▸ (AtPublicFiles.AtFiles.ixOf AtPublicFiles.AtFiles.idxA).2⟩

/-- It is a member of E2E/ObjectGuards.lean. -/
theorem ixOne_eq : ixOne = AtPublicFiles.AtFiles.ixOf AtPublicFiles.AtFiles.idxB := Subtype.ext oneCell_eq_matrixOf

/-- So is this one. -/
theorem ixZero_eq : ixZero = AtPublicFiles.AtFiles.ixOf AtPublicFiles.AtFiles.idxA := Subtype.ext zero_eq_matrixOf

/-- **The same at the object cut to the matrices in range**, at these two. -/
theorem every_set_objAt (Z : VerifierAndGoals.PublicFiles) (P : (AtPublicFiles.AtFiles.filesAt Z).Provers)
    (Q : Finset OnBytes.Slice.frS.Pos) (hQ : Q.card = 44040192) :
    ¬ SameAt (AtPublicFiles.AtFiles.objAt Z P) Q (seedOne OnBytes.Slice.frS 29) ixOne ixZero :=
  DifferAt.cut (AtPublicFiles.AtFiles.filesAt Z) P AtPublicFiles.AtFiles.inRange
    (differ_at_full _ _ Subtype.val Q hQ) _ _

theorem not_reads_objAt (Z : VerifierAndGoals.PublicFiles) (P : (AtPublicFiles.AtFiles.filesAt Z).Provers)
    (qT qpar qch qon : ℕ) : ¬ (AtPublicFiles.AtFiles.objAt Z P).ReadsR 44040192 qT qpar qch qon :=
  fun h => not_hidE_objAt Z P (hidE_of_reads h)

end AtPublicFiles.Table

#print axioms AtPublicFiles.Table.not_hidE_filesAt
#print axioms AtPublicFiles.Table.not_reads_filesAt
#print axioms AtPublicFiles.Table.Differ.not_hidE_cut
#print axioms AtPublicFiles.Table.zero_eq_matrixOf
#print axioms AtPublicFiles.Table.oneCell_eq_matrixOf
#print axioms AtPublicFiles.Table.DifferAt.cut
#print axioms AtPublicFiles.Table.ixOne_eq
#print axioms AtPublicFiles.Table.ixZero_eq
#print axioms AtPublicFiles.Table.every_set_filesAt
#print axioms AtPublicFiles.Table.every_set_objAt
#print axioms AtPublicFiles.Table.not_hidE_objAt
#print axioms AtPublicFiles.Table.not_reads_objAt
