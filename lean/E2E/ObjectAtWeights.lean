-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ObjectAtWeights.lean: from weights to matrices in range, and the object of
E2E/ObjectAtFiles.lean at the weights themselves as index type.

Why. The matrices in range (`Ix`, E2E/ObjectAtFiles.lean) are more than the weights: a matrix has
entries at which no byte of a weight lies (the library's reading of its layout; no theorem). So "two
different matrices in range" (E2E/ObjectGuards.lean) does not say "two different weights". And the
library's definition of an argument system speaks of `ModelWeights settings` (VerifiableInference/
ModelWeights.lean): arrays that pass the test on sizes and ranges at public settings. There the
range is in the type, and no predicate is left.

Definitions, at valid settings.
  `wIx valid w`: the matrix of the weights w, as a matrix in range: the library's `indexOfWeights`
    (IntegerModel/Arrays/OfIndex.lean), then `Flat.matrixOf` (Johnson/Flat/ThreeFull.lean).
  `wBack valid i`: the weights that a matrix in range holds: the library's `weightsOfIndex` at the
    index that the matrix holds.
  `objW valid F P`: `cutObj F P` re-indexed along these two (E2E/CutIndex.lean): an object whose
    index type is `ModelWeights settings`.
What is shown.
  `tensors_two`, `weights_two`: at valid settings there are two different weights (all tensors 0;
    the entry 1 in row 0, column 0 of the embedding).
  `wIx_injective`: different weights have different matrices. `ix_two_of_weights`: so two different
    matrices in range come from weights.
  `wBack_wIx`: from the matrix of w the weights w come back.
  `v_objW`: the verifier's side of `objW valid F P` is that of `F.withProvers P`.
  `whole_objW`: the conditional theorem of E2E/WholeView.lean at `objW valid F P`.

Limits.
- The settings are a free letter under "valid". Nothing here ties them to three public files: the
  tables of scales that the relation at Z reads come from Z's files.
- That a committer commits to the matrix `wIx valid w` is not said: no committer occurs here.
- The decoder of `objW` returns the weights of whatever matrix in range the library's decoder
  returns: two matrices with the same tensors give the same weights. Nothing on soundness is said.
- Two weights are few. That the two named ones are of any use is not said.
- All limits of E2E/WholeView.lean's head stand.

`objW` may be read as part of a goal: it fixes an object. It is not among this library's goals.


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
import E2E.ObjectGuards
import IntegerModel.Arrays.SameTensors

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Cut
open OnBytes.Flat (Files)
open Inst.Model (ppref Index)
open Inst.Model.ScalesSanity (iZero iW iW_wf)
open VerifiableInference (ModelWeights settingsAreValid weightsOfIndex indexOfWeights)
open VerifiableInference.OnPublicFiles (Flat.matrixOf Flat.holds_matrixOf)
open scoped ENNReal

/-! ## 1. Two different weights -/

/-- The tensors with the entry 1 in row 0, column 0 of the embedding, and 0 elsewhere. -/
def jOne : Index ppref :=
  ⟨iW (fun _ => 0) fun j x => if j = 0 ∧ x = 0 then 1 else 0,
    iW_wf (fun _ => by norm_num) (fun _ _ => rfl) fun j x => by
      by_cases h : j = 0 ∧ x = 0
      · obtain ⟨rfl, rfl⟩ := h
        rw [if_pos (by decide)]
        norm_num
      · rw [if_neg h]
        split_ifs <;> norm_num⟩

theorem tensors_two : iZero ≠ jOne := fun h => by
  have e : iZero.val.Emb 0 0 = jOne.val.Emb 0 0 := by rw [h]
  have e' : (0 : ℤ) = 1 := e
  norm_num at e'

section Valid
variable {settings : IntegerTransformer.Settings} (valid : settingsAreValid settings = true)
include valid

/-- **At valid settings there are two different weights.** -/
theorem weights_two : ∃ w w' : ModelWeights settings, w ≠ w' :=
  ⟨weightsOfIndex valid (Cm.Idx.ofIndex iZero), weightsOfIndex valid (Cm.Idx.ofIndex jOne),
    fun h => tensors_two (by
      have e := (VerifiableInference.weightsOfIndex_eq_iff valid _ _).1 h
      rwa [Cm.index_ofIndex, Cm.index_ofIndex] at e)⟩

/-! ## 2. From weights to matrices in range, and back -/

/-- The matrix of given weights, as a matrix in range. -/
def wIx (w : ModelWeights settings) : Ix := ixOf (indexOfWeights valid w)

/-- **Different weights have different matrices.** -/
theorem wIx_injective : Function.Injective (wIx valid) := fun w w' h => by
  have e := ixOf_injective h
  rw [← VerifiableInference.weightsOfIndex_indexOfWeights valid w, e,
    VerifiableInference.weightsOfIndex_indexOfWeights valid w']

/-- **Two different matrices in range that come from weights.** -/
theorem ix_two_of_weights : ∃ w w' : ModelWeights settings, wIx valid w ≠ wIx valid w' := by
  obtain ⟨w, w', h⟩ := weights_two valid
  exact ⟨w, w', fun e => h (wIx_injective valid e)⟩

/-- The weights that a matrix in range holds. -/
def wBack (i : Ix) : Option (ModelWeights settings) :=
  some (weightsOfIndex valid (Classical.choose i.2))

/-- From the matrix of w the weights w come back. -/
theorem wBack_wIx (w : ModelWeights settings) : wBack valid (wIx valid w) = some w := by
  have h := Classical.choose_spec (wIx valid w).2
  have e : Classical.choose (wIx valid w).2 = indexOfWeights valid w :=
    VerifiableInference.OnPublicFiles.Flat.holds_unique le_rfl le_rfl h
      (Flat.holds_matrixOf (indexOfWeights valid w))
  unfold wBack
  rw [e, VerifiableInference.weightsOfIndex_indexOfWeights valid w]

/-! ## 3. The object at the weights -/

variable {X : Type} {pp : Inst.Model.ScalesAndPolicy} {req : X → Inst.Model.Instance Inst.Model.ppref}

/-- **The object of three protocols F and provers P with the weights as index type.** -/
def objW (F : Files (ConfAt pp req)) (P : F.Provers) : HolographicProtocol (ModelWeights settings) X :=
  reIndex (cutObj F P) (wIx valid) (wBack valid)

/-- Its verifier's side is that of `F.withProvers P`. -/
theorem v_objW (F : Files (ConfAt pp req)) (P : F.Provers) : (objW valid F P).v = (F.withProvers P).v :=
  rfl

/-- **The conditional theorem of E2E/WholeView.lean at the weights**: for any provers that fit, the
library's `HVZKWholeR` of `objW valid F P`: the index ranges over the weights at the settings. IT
ASKS NO ACCEPTANCE OF P. -/
theorem whole_objW (F : Files (ConfAt pp req)) (P : F.Provers) (Ryes : Ix → X → Prop)
    {b qT qpar qch qon : ℕ} {zT zL zO : ℝ≥0∞} (reads : (cutObj F P).ReadsR b qT qpar qch qon)
    (fit : ProversFit F P Ryes zT zL zO) :
    ∃ Sm : SimsR (objW valid F P), ∀ B : BoundsR, B.Fits b qT qpar qch qon →
      ∀ w₀ : ModelWeights settings,
        HVZKWholeR (objW valid F P) (fun w => Ryes (wIx valid w)) B
          (simWholeR (objW valid F P) Sm w₀) (B.err zT zL zO) :=
  rec_hvzk_whole_hiding _ _ (objW valid F P) (fun w => Ryes (wIx valid w)) b qT qpar qch qon zT zL
    zO
    (wired_reIndex (cutObj F P) (wIx valid) (wBack valid)
      (fun w r s => (wired_cutObj F P fit.ext).dec_enc (wIx valid w) r s) (wBack_wIx valid)
      (ext_reIndex (wIx valid) (wBack valid) fit.ext))
    (reads_reIndex (wIx valid) (wBack valid) reads)
    (hiding_reIndex (wIx valid) (wBack valid) (fun _ _ hy => hy) fit.hidden)

end Valid

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.tensors_two
#print axioms AtPublicFiles.AtFiles.weights_two
#print axioms AtPublicFiles.AtFiles.wIx_injective
#print axioms AtPublicFiles.AtFiles.ix_two_of_weights
#print axioms AtPublicFiles.AtFiles.wBack_wIx
#print axioms AtPublicFiles.AtFiles.v_objW
#print axioms AtPublicFiles.AtFiles.whole_objW
