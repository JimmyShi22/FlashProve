-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/JoinsSizes.lean: JOINS: from the laws over the sizes
(Johnson/Bind/ForProver/LawsSizes.lean, AtWeights.lean) to the terms that other files call: the
matrix of an index, of which the library's theorem on decoding speaks; the packing off a value of
`ProofFile.Pub`; `encW`; the test `rowsFit` at the library's two sizes. Statements and proofs.

Main names (namespace `Bind.ForProver`).
  **`cellsOfF_matrixOf`**: at the casts of an index's integers `cellsOfF`, at the full size, is the
    library's matrix of that index (`VerifiableInference.OnPublicFiles.Flat.matrixOf`,
    Johnson/Flat/ThreeFull.lean).
  **`column_decodes_full`**: so, at the full size, the table whose symbol at x is the position's
    number with `encAt`'s column written as words is decoded by the library's object to the index's
    matrix (`OnBytes.Flat.obj_decodes_index_full`, Johnson/Flat/CodingCells.lean).
  **`words_typedW`**: `words_typed` at `encW` off Z, under its two premises (`Agree` and hfit, at
    the shape and the numbers off Z); there the files F are typed at the numbers off Z. `encW_full`,
    **`words_full`**: under `ShapeAtFull Z`: `encW` at the item 0 is `encAt` at the full size's
    shape and numbers; and the same law with F typed at `numsRef`, where the description's own files
    and provers are members.
  **`entryOfPub_full`**: under `ShapeAtFull Z` the packing off Z, at the casts of the digits of
    given weights, is `Bind.Cpp.entryOf s w`: the plain entries of what stands in the commit field
    (`Bind.Cpp.cppCommit T`, at every T).
  `rowsFit_full`, `rowsFit_small`: at the two sizes' shapes and numbers the test `rowsFit` passes.
  **`premises_full`**, **`premises_small`**: under `ShapeAtFull Z`, or `ShapeAtSmall Z`: the test
    `rowsFit` passes at Z and the code has at most 2^32 positions: the two public premises of
    Johnson/Bind/ForProver/TabCols.lean; JoinsLoc.lean asks the second alone.
  **`column_decodes_at`**: `column_decodes_full` off Z: under `ShapeAtFull Z`, at `encW Z` at the
    casts of an index's integers, which is `enc Z i` (Johnson/Bind/ForProver/Enc.lean) by unfolding.

Limits. `ShapeAtFull Z` and `ShapeAtSmall Z` are premises here; of the first see
Johnson/Bind/ForProver/InScope.lean; no statement of this library concludes the second.
`Agree` and hfit are premises of `words_typedW`. `column_decodes_full` stands at the numerals of the
full size. Nothing on decoding at the small stored example's size: the library's theorem there asks
a matrix in range, and no index is typed at that size. The OOD sample that the decoder is handed is
the library's own at that matrix, not one of this folder. It is an equation on the library's
decoder: no correctness of extraction of any protocol, no binding of the commitment (the opening
form). No hash function is read. No completeness, no index privacy; nothing on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.LawsSizes
import Johnson.Bind.ForProver.AtWeights
import Johnson.Bind.ForProver.Laws

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.ForProver
open Prob Cb Cb.Ood Blocks Hiop OnBytes.Slice OnBytes.Flat Inst.Model VerifiableInference
open Iop hiding Shape
open VerifiableInference.OnPublicFiles (numsRef)
open ProofFile.Honest (TableRand)
open Bind.Twin (Shape Table)
open Bind.Column (Agree)

/-- **At the casts of an index's integers the matrix of cells is the library's matrix of that
index.** -/
theorem cellsOfF_matrixOf (i : Cm.Idx) :
    cellsOfF frS frZ 402653181 numsRef (fun y c => ((i.mat y c : ℤ) : GF)) =
      OnPublicFiles.Flat.matrixOf i := by
  funext y c
  show algebraMap GF GE ((i.mat y.val c.val : ℤ) : GF) = ((i.mat y.val c.val : ℤ) : GE)
  exact map_intCast _ _

/-- At the full size's shape and numbers the test passes. -/
theorem rowsFit_full : rowsFit Bind.Column.shFull numsRef.kLo numsRef.rows = true :=
  (rowsFit_iff Bind.Column.agree_full _ _).2 full_fits.1

/-- At the small stored example's shape and numbers the test passes. -/
theorem rowsFit_small : rowsFit Bind.Column.shSmall numsSmall.kLo numsSmall.rows = true :=
  (rowsFit_iff Bind.Column.agree_small _ _).2 small_fits.1

/-- **At the full size the table of `encAt`'s columns, written as words, decodes to the index's
matrix**, where the decoder is handed the library's own OOD sample at that matrix. No correctness of
extraction. -/
theorem column_decodes_full {X : Type} (pp : ScalesAndPolicy) (req : X → Instance ppref)
    (F : Files (DecR.configurationOfStoredTable (claimsLedgerOnAt (frS.toDecR frZ 402653181) numsRef pp req)
      (relationsAndEncodingOfClaims _ (codingCells frS frZ 402653181 numsRef pp req)))) (P : F.Provers)
    (i : Cm.Idx) (ρ : TableRand) (s : (F.withProvers P).OutOfDomainSeed) :
    (F.withProvers P).decodeIndex
        (fun x : frS.Pos => (x.val, ((encAt Bind.Column.shFull
          (entryAtF numsRef.kLo numsRef.rows frS.P.v fun y c => ((i.mat y c : ℤ) : GF)) ρ
          x.val).getD []).map ofF))
        ((F.withProvers P).recOf (OnPublicFiles.Flat.matrixOf i)
          (fun b j => ρ.pad b.val j.val, fun b q => ρ.tail b.val q.val) s) =
      some (OnPublicFiles.Flat.matrixOf i) := by
  have e : (fun x : frS.Pos => (x.val, ((encAt Bind.Column.shFull
      (entryAtF numsRef.kLo numsRef.rows frS.P.v fun y c => ((i.mat y c : ℤ) : GF)) ρ
      x.val).getD []).map ofF)) =
      (F.withProvers P).encodeIndex (OnPublicFiles.Flat.matrixOf i)
        (fun b j => ρ.pad b.val j.val, fun b q => ρ.tail b.val q.val) := by
    funext x
    rw [← cellsOfF_matrixOf i]
    exact words_typed X pp req F P Bind.Column.agree_full full_fits.1 _ ρ x
  rw [e]
  exact obj_decodes_index_full pp req F P i _ s

section
variable {S : Sz} {Zs : Sample GE S.En} {cut : ℕ} (Z : ProofFile.Pub)
  (X : Type) (pp : ScalesAndPolicy) (req : X → Instance ppref)
  (F : Files (DecR.configurationOfStoredTable (claimsLedgerOnAt (S.toDecR Zs cut) (numsOf Z) pp req)
    (relationsAndEncodingOfClaims _ (codingCells S Zs cut (numsOf Z) pp req)))) (P : F.Provers)

/-- **The position's number with `encW`'s column, written as words, is the typed encoder's symbol**,
at the item 0, under `Agree` and hfit at the shape and the numbers off Z. -/
theorem words_typedW (h : Agree (shapeOf Z) S cut)
    (hfit : (numsOf Z).rows * 2 ^ (numsOf Z).kLo ≤ cut) (w : ProofFile.Honest.Weights)
    (rc : ℕ → TableRand) (x : S.Pos) :
    (x.val, ((encW Z w rc 0 x.val).getD []).map ofF) =
      (F.withProvers P).encodeIndex (cellsOfF S Zs cut (numsOf Z) w.entry)
        (fun b j => (rc 0).pad b.val j.val, fun b q => (rc 0).tail b.val q.val) x := by
  have hr : rowsFit (shapeOf Z) (linOf Z).kLo (linOf Z).matrixRows = true :=
    (rowsFit_iff h _ _).2 hfit
  rw [encW_fit Z w rc x.val hr, h.v]
  exact words_typed X pp req F P h hfit w.entry (rc 0) x

end

/-- **Under `ShapeAtFull` the packing off Z, at the digits of given weights, is the plain entries of
what stands in the commit field.** -/
theorem entryOfPub_full (Z : ProofFile.Pub) (hZ : ShapeAtFull Z) (s : IntegerTransformer.Settings)
    (w : ModelWeights s) :
    entryOfPub Z ⟨fun y c => (((Bind.Cpp.idxOf s w).mat y c : ℤ) : Cb.Gl.F)⟩ =
      Bind.Cpp.entryOf s w := by
  have h1 : (linOf Z).kLo = numsRef.kLo := congrArg MatrixNums.kLo hZ.2
  have h2 : (linOf Z).matrixRows = numsRef.rows := congrArg MatrixNums.rows hZ.2
  have h3 : (shapeOf Z).v = 11 := congrArg Bind.Twin.Shape.v hZ.1
  unfold entryOfPub
  rw [h1, h2, h3, entryOf_eq]

/-- **Under `ShapeAtFull` the two public premises hold.** -/
theorem premises_full (Z : ProofFile.Pub) (hZ : ShapeAtFull Z) :
    rowsFit (shapeOf Z) (linOf Z).kLo (linOf Z).matrixRows = true ∧ (shapeOf Z).a ≤ 32 := by
  refine ⟨(rowsFit_iff (paid_full Z hZ).1 _ _).2 (paid_full Z hZ).2, ?_⟩
  rw [hZ.1]
  exact Nat.le_refl 32

/-- **Under `ShapeAtSmall` the two public premises hold.** -/
theorem premises_small (Z : ProofFile.Pub) (hZ : ShapeAtSmall Z) :
    rowsFit (shapeOf Z) (linOf Z).kLo (linOf Z).matrixRows = true ∧ (shapeOf Z).a ≤ 32 := by
  refine ⟨(rowsFit_iff (paid_small Z hZ).1 _ _).2 (paid_small Z hZ).2, ?_⟩
  rw [hZ.1]
  show 23 ≤ 32
  decide

/-- Under `ShapeAtFull` `encW` at the item 0 is `encAt` at the full size's shape and numbers. -/
theorem encW_full (Z : ProofFile.Pub) (hZ : ShapeAtFull Z) (w : ProofFile.Honest.Weights)
    (rc : ℕ → TableRand) (x : ℕ) :
    encW Z w rc 0 x =
      encAt Bind.Column.shFull (entryAtF numsRef.kLo numsRef.rows frS.P.v w.entry) (rc 0) x := by
  have h1 : (linOf Z).kLo = numsRef.kLo := congrArg MatrixNums.kLo hZ.2
  have h2 : (linOf Z).matrixRows = numsRef.rows := congrArg MatrixNums.rows hZ.2
  rw [encW_fit Z w rc x (premises_full Z hZ).1, hZ.1, h1, h2]
  rfl

/-- **Under `ShapeAtFull` the position's number with `encW`'s column, written as words, is the typed
encoder's symbol at the full size's own numbers**: so the description's own files and provers, which
are typed at these, are members. -/
theorem words_full (Z : ProofFile.Pub) (hZ : ShapeAtFull Z) {X : Type} (pp : ScalesAndPolicy)
    (req : X → Instance ppref)
    (F : Files (DecR.configurationOfStoredTable (claimsLedgerOnAt (frS.toDecR frZ 402653181) numsRef pp req)
      (relationsAndEncodingOfClaims _ (codingCells frS frZ 402653181 numsRef pp req)))) (P : F.Provers)
    (w : ProofFile.Honest.Weights) (rc : ℕ → TableRand) (x : frS.Pos) :
    (x.val, ((encW Z w rc 0 x.val).getD []).map ofF) =
      (F.withProvers P).encodeIndex (cellsOfF frS frZ 402653181 numsRef w.entry)
        (fun b j => (rc 0).pad b.val j.val, fun b q => (rc 0).tail b.val q.val) x := by
  rw [encW_full Z hZ w rc x.val]
  exact words_typed X pp req F P Bind.Column.agree_full full_fits.1 w.entry (rc 0) x

/-- **Under `ShapeAtFull` the table of `encW`'s columns at an index, written as words, decodes to
the index's matrix**, where the decoder is handed the library's own OOD sample at that matrix. No
correctness of extraction. -/
theorem column_decodes_at (Z : ProofFile.Pub) (hZ : ShapeAtFull Z) {X : Type} (pp : ScalesAndPolicy)
    (req : X → Instance ppref)
    (F : Files (DecR.configurationOfStoredTable (claimsLedgerOnAt (frS.toDecR frZ 402653181) numsRef pp req)
      (relationsAndEncodingOfClaims _ (codingCells frS frZ 402653181 numsRef pp req)))) (P : F.Provers)
    (i : Cm.Idx) (rc : ℕ → TableRand) (s : (F.withProvers P).OutOfDomainSeed) :
    (F.withProvers P).decodeIndex
        (fun x : frS.Pos => (x.val, ((encW Z ⟨fun y c => ((i.mat y c : ℤ) : GF)⟩ rc 0
          x.val).getD []).map ofF))
        ((F.withProvers P).recOf (OnPublicFiles.Flat.matrixOf i)
          (fun b j => (rc 0).pad b.val j.val, fun b q => (rc 0).tail b.val q.val) s) =
      some (OnPublicFiles.Flat.matrixOf i) := by
  have e : (fun x : frS.Pos => (x.val, ((encW Z ⟨fun y c => ((i.mat y c : ℤ) : GF)⟩ rc 0
      x.val).getD []).map ofF)) =
      fun x : frS.Pos => (x.val, ((encAt Bind.Column.shFull
        (entryAtF numsRef.kLo numsRef.rows frS.P.v fun y c => ((i.mat y c : ℤ) : GF)) (rc 0)
        x.val).getD []).map ofF) := by
    funext x
    rw [encW_full Z hZ _ rc x.val]
  rw [e]
  exact column_decodes_full pp req F P i (rc 0) s

end Bind.ForProver

end

#print axioms Bind.ForProver.cellsOfF_matrixOf
#print axioms Bind.ForProver.rowsFit_full
#print axioms Bind.ForProver.rowsFit_small
#print axioms Bind.ForProver.column_decodes_full
#print axioms Bind.ForProver.words_typedW
#print axioms Bind.ForProver.entryOfPub_full
#print axioms Bind.ForProver.premises_full
#print axioms Bind.ForProver.premises_small
#print axioms Bind.ForProver.encW_full
#print axioms Bind.ForProver.words_full
#print axioms Bind.ForProver.column_decodes_at
