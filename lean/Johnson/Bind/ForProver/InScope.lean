-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/InScope.lean: AT THREE PUBLIC FILES IN THE GOALS' SCOPE, AT EVERY PUBLIC PART
THAT THE PROOF FILE'S OWN MAKER RETURNS OF THEM, THE PUBLIC PREMISES OF THE LAWS NAMED BELOW HOLD:
`ShapeAtFull`, the test `rowsFit`, the bound on the code. Statements and proofs; no definition.

On what it rests. Johnson/Bind/ForProver/ShapeInScope.lean: the shape and the matrix's two numbers
off such a public part are the full size's: over the library's own theorems on the planner in scope.

Main names (namespace `Bind.ForProver`), each under the two premises "in scope" (hP) and "the maker
returned Z" (h), at every value o of the argument that stands for the format's second hash function.
"The maker" is the maker of the public part alone (`ProofFile.pubPlain`).
  **`shapeAtFull_inScope`**: `ShapeAtFull Z` (Johnson/Bind/ForProver/LawsSizes.lean).
  **`cols_inScope`**, **`tab_inScope`**: `cols_at` and `tab_at`
    (Johnson/Bind/ForProver/TabCols.lean) with no other premise on Z.
  **`locEq_inScope`**: `locEq_at` (Johnson/Bind/ForProver/JoinsLoc.lean): wherever `encW` gives a
    column at the item 0. **`locEq_stored_inScope`**: `locEq_stored` (TabCols.lean): the same at the
    column's words, at every position that the code has.
  `entryOfPub_inScope`: the packing off Z, at the casts of the digits of given weights, is
    `Bind.Cpp.entryOf s w` (`entryOfPub_full`, Johnson/Bind/ForProver/JoinsSizes.lean).
  **`column_decodes_inScope`**: the table of `encW Z`'s columns at an index, written as words, is
    decoded by the library's object to the index's matrix, where the decoder is handed the library's
    own OOD sample at that matrix, these pads and tails and any seed (`column_decodes_at`,
    Johnson/Bind/ForProver/JoinsSizes.lean). `encW Z` at the casts of an index's integers is
    `enc Z i` (Johnson/Bind/ForProver/Enc.lean), by unfolding.
  `words_inScope`: the position's number with `encW`'s column, written as words, is the symbol of
    the library's typed encoder at the full size's own numbers (`words_full`,
    Johnson/Bind/ForProver/JoinsSizes.lean): the description's own files and provers are members.

Limits. ONE DIRECTION: from a maker that returns. That `ProofFile.pubPlain` returns at any files in scope
is shown by no theorem of this file: so none of them shows a public part that meets the two premises
together (the side library proves that the maker returns at the two stored full-size sets:
`okStart_zFull_whole`, `okStart_zGap_whole`, AtFullSide/E2E/StartAtWrittenFiles.lean, by the field
`pub` of `LaidAt`, Johnson/P5J/LaidOpens.lean). Nothing at files out of scope, so nothing at the
small stored example's. The limits of the files that are named above stand. `column_decodes_inScope`
is an equation on the library's decoder: no correctness of extraction of any protocol, no binding of
the commitment (the opening form). No statement here names a prover of the frame
(`ProofFile.Honest.Prover`). `column_decodes_inScope` and `words_inScope` bind the library's honest
provers of its three protocols as a variable (Q : `F.Provers`, OnBytes/Flat/Object.lean), at every
value, because the library's object `F.withProvers Q` takes them. No completeness of any protocol, no index
privacy; nothing on any program: the names under `Bind.Cpp` are Lean definitions and theorems, not
programs.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.ShapeInScope
import Johnson.Bind.ForProver.TabCols
import Johnson.Bind.ForProver.JoinsSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.ForProver
open Prob Cb Cb.Ood Blocks Hiop OnBytes.Slice OnBytes.Flat Inst.Model VerifiableInference
open Iop hiding Shape
open VerifiableInference.OnPublicFiles (numsRef)
open OnBytes (generatorAt)
open OnBytes.Model (Reading)
open ProofFile.Honest (TableRand)
open Desc.K14.Law (LocEq genK)

section
variable {P : VerifierAndGoals.PublicFiles} (hP : VerifierAndGoals.InScope P = true) {o : ProofFile.SecondHashFunctionArgument} {Z : ProofFile.Pub}
  (h : ProofFile.pubPlain o P.pol P.lay P.KL = .ok Z)
include hP h

/-- **The shape and the matrix's numbers off Z are the full size's.** -/
theorem shapeAtFull_inScope : ShapeAtFull Z := by
  refine ⟨shapeOf_inScope hP h, ?_⟩
  show (⟨(linOf Z).matrixRows, (linOf Z).kLo⟩ : MatrixNums) = numsRef
  rw [matrixRows_inScope hP h, kLo_inScope hP h]
  rfl

/-- **At every position there is a column of the declared width.** -/
theorem cols_inScope (w : ProofFile.Honest.Weights) (rc : ℕ → TableRand) (l : List (ℕ × ℕ)) (p : ℕ)
    (hp : p < 2 ^ (declaredAt Z l).sh.a) :
    ∃ u, storedW Z w rc (declaredAt Z l).item p = some u ∧
      u.length = (declaredAt Z l).sh.W :=
  cols_at Z (rowsFit_inScope hP h) w rc l p hp

/-- **Each word of the column, read, is the programs' generator row applied to that row before
encoding.** -/
theorem tab_inScope (w : ProofFile.Honest.Weights) (rc : ℕ → TableRand) (x : ℕ)
    (hx : x < 2 ^ (linOf Z).fold.index.code.logN) (r : ℕ)
    (hr : r < (linOf Z).fold.index.rows) :
    Reading.gl.val (OnBytes.ofF (((storedW Z w rc 0 x).getD []).toArray.getD r 0)) =
      genK Reading.gl (linOf Z).fold x (fun j => Reading.gl.val
        (ProofFile.Honest.K14.rowsOf (linOf Z) w ⟨(rc 0).pad, (rc 0).tail⟩ r j)) :=
  tab_at Z (rowsFit_inScope hP h) w rc (a_inScope hP h) x hx r hr

/-- **(loc_x)'s equation at `encW`'s column**, at files in scope. -/
theorem locEq_inScope (w : ProofFile.Honest.Weights) (rc : ℕ → TableRand) (x : ℕ)
    (col : List Cb.Gl.F) (hc : encW Z w rc 0 x = some col) (psi : List OnBytes.E) :
    LocEq Reading.gl (linOf Z).fold (generatorAt (linOf Z).fold.index.code x)
      (fun r => Reading.gl.val (Desc.K14.Law.eqE (psi.drop (linOf Z).kLo) r)) (2 ^ (shapeOf Z).v)
      (fun r => Reading.gl.val (OnBytes.ofF (ofF (col.getD r 0))))
      (fun k => Reading.gl.val (Desc.K14.Honest.uAtE (linOf Z) psi
        (ProofFile.Honest.K14.rowsOf (linOf Z) w ⟨(rc 0).pad, (rc 0).tail⟩) k)) :=
  locEq_at Z w rc x col hc (a_inScope hP h) psi

/-- **(loc_x)'s equation at the words of `encW`'s column**, at files in scope, at every position
that the code has. -/
theorem locEq_stored_inScope (w : ProofFile.Honest.Weights) (rc : ℕ → TableRand) (x : ℕ)
    (hx : x < 2 ^ (linOf Z).fold.index.code.logN) (psi : List OnBytes.E) :
    LocEq Reading.gl (linOf Z).fold (generatorAt (linOf Z).fold.index.code x)
      (fun r => Reading.gl.val (Desc.K14.Law.eqE (psi.drop (linOf Z).kLo) r)) (2 ^ (shapeOf Z).v)
      (fun r => Reading.gl.val (OnBytes.ofF (((storedW Z w rc 0 x).getD []).toArray.getD r 0)))
      (fun k => Reading.gl.val (Desc.K14.Honest.uAtE (linOf Z) psi
        (ProofFile.Honest.K14.rowsOf (linOf Z) w ⟨(rc 0).pad, (rc 0).tail⟩) k)) :=
  locEq_stored Z (rowsFit_inScope hP h) w rc (a_inScope hP h) x hx psi

/-- The packing off Z, at the digits of given weights, is the plain entries of what stands in the
commit field (`Bind.Cpp.cppCommit T`, at every T). -/
theorem entryOfPub_inScope (s : IntegerTransformer.Settings) (w : ModelWeights s) :
    entryOfPub Z ⟨fun y c => (((Bind.Cpp.idxOf s w).mat y c : ℤ) : Cb.Gl.F)⟩ =
      Bind.Cpp.entryOf s w :=
  entryOfPub_full Z (shapeAtFull_inScope hP h) s w

/-- **The table of `encW Z`'s columns at an index, written as words, decodes to the index's
matrix**, where the decoder is handed the library's own OOD sample at that matrix. No correctness of
extraction. -/
theorem column_decodes_inScope {X : Type} (pp : ScalesAndPolicy) (req : X → Instance ppref)
    (F : Files (DecR.configurationOfStoredTable (claimsLedgerOnAt (frS.toDecR frZ 402653181) numsRef pp req)
      (relationsAndEncodingOfClaims _ (codingCells frS frZ 402653181 numsRef pp req)))) (Q : F.Provers)
    (i : Cm.Idx) (rc : ℕ → TableRand) (s : (F.withProvers Q).OutOfDomainSeed) :
    (F.withProvers Q).decodeIndex
        (fun x : frS.Pos => (x.val, ((encW Z ⟨fun y c => ((i.mat y c : ℤ) : GF)⟩ rc 0
          x.val).getD []).map ofF))
        ((F.withProvers Q).recOf (OnPublicFiles.Flat.matrixOf i)
          (fun b j => (rc 0).pad b.val j.val, fun b q => (rc 0).tail b.val q.val) s) =
      some (OnPublicFiles.Flat.matrixOf i) :=
  column_decodes_at Z (shapeAtFull_inScope hP h) pp req F Q i rc s

/-- The position's number with `encW`'s column, written as words, is the typed encoder's symbol at
the full size. -/
theorem words_inScope {X : Type} (pp : ScalesAndPolicy) (req : X → Instance ppref)
    (F : Files (DecR.configurationOfStoredTable (claimsLedgerOnAt (frS.toDecR frZ 402653181) numsRef pp req)
      (relationsAndEncodingOfClaims _ (codingCells frS frZ 402653181 numsRef pp req)))) (Q : F.Provers)
    (w : ProofFile.Honest.Weights) (rc : ℕ → TableRand) (x : frS.Pos) :
    (x.val, ((encW Z w rc 0 x.val).getD []).map ofF) =
      (F.withProvers Q).encodeIndex (cellsOfF frS frZ 402653181 numsRef w.entry)
        (fun b j => (rc 0).pad b.val j.val, fun b q => (rc 0).tail b.val q.val) x :=
  words_full Z (shapeAtFull_inScope hP h) pp req F Q w rc x

end

end Bind.ForProver

end

#print axioms Bind.ForProver.shapeAtFull_inScope
#print axioms Bind.ForProver.cols_inScope
#print axioms Bind.ForProver.tab_inScope
#print axioms Bind.ForProver.locEq_inScope
#print axioms Bind.ForProver.locEq_stored_inScope
#print axioms Bind.ForProver.entryOfPub_inScope
#print axioms Bind.ForProver.column_decodes_inScope
#print axioms Bind.ForProver.words_inScope
