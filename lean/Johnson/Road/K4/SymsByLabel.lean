-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/SymsByLabel.lean: THE TEST AT ONE MATRIX (`symTieB`,
Johnson/Road/K4/SymsOfLayout.lean) ASKED AT THE OWNER AND THE NAME THAT THE PUBLIC PARAMETERS' LABEL
NAMES, SO THAT IT READS NEITHER THE BUILT LINKS' LISTS OF ARRAYS NOR THE MATRIX's TREE. `symTieB`
has three conjuncts: the lookup's authors' `symArrB`, which finds (owner, name) in the built link's
list at the matrix's tree; the names' tie, which says that this pair is the label's; and `tenantB`.
Where the names' tie is had from elsewhere (`names_tie`, a theorem in the goals'
scope), the first conjunct can be asked at the label's pair outright and the second falls. Two
definitions with code and three theorems. Glue; no draw, no count.

  `arrAtB D l i b n R K`: `symArrB`'s text behind its first look-up, at the pair (b, n).
  `symArr_at`: where the built link's list has (b, n) at t, `symArrB D l i t R K = arrAtB …`.
  `symLabB A num arr N k X s μ`: `arrAtB` and `tenantB` at the label's pair.
  `symTie_eq_lab`: under the names' tie at μ, `symTieB … μ = symLabB … μ`: AN EQUATION: a reject
    carries over too.
  `symsOne_of_lab`: `SymsOne` from the names' tie and `symLabB` at every matrix.

Limits. K04_law IS NOT PROVED BY THIS. THE NAMES' TIE IS A PREMISE HERE: this file does not import
its proof, whose closure is heavy. `symLabB` still reads of the public parameters X the labels (aId)
and, through s, the matrices' sizes.
-/
import Johnson.Road.K4.SymsOfLayout

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes
open OnBytes.Model (HTailF2)
open OnBytes.Params (ReqLayout)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls symArrB msgIn blocksB)
open Meaning (seatBy fLay labAt ownerK ownerA nameOf)
open Cb.Pv.Tail (Size)

/-- `symArrB`'s text behind its first look-up: at the array of link b with the name n. -/
def arrAtB (D : Sent) (l : List (OracleShape × ℕ)) (i b : ℕ) (n : String) (R K : ℕ) : Bool :=
  match OnBytes.reqArray D.layout b n with
  | some a =>
    match msgIn D i b a.message with
    | some k =>
      match l[k]? with
      | some o => blocksB a.blocks R K o.1.mainRows (Johnson.Pack.pMain D.codes o.1).ell
      | none => false
    | none => false
  | none => false

/-- Where the built link's list has (b, n) at t. -/
theorem symArr_at {D : Sent} {l : List (OracleShape × ℕ)} {i t b : ℕ} {n : String} (R K : ℕ)
    (h : (D.arrayOf.getD i #[])[t]? = some (b, n)) :
    symArrB D l i t R K = arrAtB D l i b n R K := by
  unfold symArrB arrAtB
  rw [h]
  rfl

section
variable {Cells : Type} (A : PinPlan Cells) (num arr : ℕ → ℕ → ℕ) (N : Numbers) (k : ℕ)

/-- **The test at one matrix, at the label's owner and name.** -/
def symLabB (X : Model.Verify.Public) (s : ℕ → Size) (μ : ℕ) : Bool :=
  arrAtB A.D (sigListCalls A.D A.rad A.link) A.link (ownerK (labAt X k μ))
      (nameOf (ownerA (labAt X k μ))) (Alg.symRows ((s k).m μ)) ((s k).k μ) &&
    tenantB A num arr N k (ownerK (labAt X k μ)) (nameOf (ownerA (labAt X k μ)))

/-- **Under the names' tie the two tests are one.** -/
theorem symTie_eq_lab (tl : HTailF2) (X : Model.Verify.Public) (s : ℕ → Size) (μ : ℕ)
    (h : (A.D.arrayOf.getD A.link #[])[tl.gtTree.getD μ 0]? =
      some (ownerK (labAt X k μ), nameOf (ownerA (labAt X k μ)))) :
    symTieB A num arr N k tl X s μ = symLabB A num arr N k X s μ := by
  unfold symTieB symLabB
  rw [symArr_at _ _ h, decide_eq_true h, Bool.and_true]

/-- **The two readings of the committed symbols are one**, from the names' tie and one test a
matrix that reads no built link. -/
theorem symsOne_of_lab (tl : HTailF2) {X : Model.Verify.Public} {s : ℕ → Size}
    {layout : ReqLayout} (hlay : A.D.layout = layout)
    (hN : ∀ μ < (s k).NM, (A.D.arrayOf.getD A.link #[])[tl.gtTree.getD μ 0]? =
      some (ownerK (labAt X k μ), nameOf (ownerA (labAt X k μ))))
    (hB : ∀ μ < (s k).NM, symLabB A num arr N k X s μ = true) :
    SymsOne A tl arr N k (s k) (seatBy (fLay layout num) X s k) :=
  symsOne_of_layout A num arr N k tl hlay fun μ hμ =>
    (symTie_eq_lab A num arr N k tl X s μ (hN μ hμ)).trans (hB μ hμ)

end

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.symArr_at
#print axioms OnBytes.Road.K4.symTie_eq_lab
#print axioms OnBytes.Road.K4.symsOne_of_lab
