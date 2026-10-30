-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/TailClaims/CoefKeeps.lean: what the step that lays the virtual rows' weights
(coefBody, Johnson/Desc/First/TailClaims/Coefficients.lean) leaves as it was. General laws; nothing
is evaluated.

Why. The smallness test's guards on sizes, counts and marks (shapeT,
Johnson/Desc/First/TailClaims/TestsCut.lean) are asked at the state behind that step. Of all that
they read the step turns one thing: the rows' weights coef on their array's rows. Here: all else
stays.

  `Same F G`: G has F's number of planned claims, batching element and number of arrays; each array
    has its name, kind, numbers of rows and columns and number of virtual rows; each virtual row has
    its weights L on the row's entries and the first column L0 that these hold.
  `KeepsL f`: a change of one virtual row that leaves L and L0.
  `same_onRow`, `same_foldl`: one such change, and a row of them, give Same.
  **`same_coefBody`**: Same F (coefBody tl g F).

It goes stage by stage over the library's own cut of the step (Fo.coefAll and its five stages,
OnBytes/Tie/Pv/Lookup/Ends/FoCoef.lean).

Limits. Nothing on coef itself or its size, nor on a field that Same does not name (the step does
turn a row's marks and parts of a product form: CoefWrites.lean). Same is another relation than the
library's OnBytes.PscRun.Same. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.TailClaims.CoefficientsAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law.Tests
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc.First.TailClaims
open Fo (rowAt tree_onRow getD_modify forIn_inv coefAll coefTables coefPieces coefPowers coefBZ
  coefMats coefPieces_eq coefMats_eq)

/-- **What the guards read, but for the rows' weights, is the same**: the ten fields below. Of the
ledger's and a row's other fields it says nothing. -/
structure Same (F G : Fork) : Prop where
  plan : G.planClaimsF = F.planClaimsF
  theta : G.theta = F.theta
  count : G.trees.size = F.trees.size
  name : ∀ t, (G.trees.getD t {}).name = (F.trees.getD t {}).name
  kind : ∀ t, (G.trees.getD t {}).kind = (F.trees.getD t {}).kind
  R : ∀ t, (G.trees.getD t {}).R = (F.trees.getD t {}).R
  K : ∀ t, (G.trees.getD t {}).K = (F.trees.getD t {}).K
  rows : ∀ t, (G.trees.getD t {}).rows.size = (F.trees.getD t {}).rows.size
  L : ∀ t e, (rowAt G t e).L = (rowAt F t e).L
  L0 : ∀ t e, (rowAt G t e).L0 = (rowAt F t e).L0

theorem Same.refl (F : Fork) : Same F F :=
  ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl⟩

theorem Same.trans {F G H : Fork} (a : Same F G) (b : Same G H) : Same F H :=
  ⟨b.plan.trans a.plan, b.theta.trans a.theta, b.count.trans a.count,
    fun t => (b.name t).trans (a.name t), fun t => (b.kind t).trans (a.kind t),
    fun t => (b.R t).trans (a.R t), fun t => (b.K t).trans (a.K t),
    fun t => (b.rows t).trans (a.rows t), fun t e => (b.L t e).trans (a.L t e),
    fun t e => (b.L0 t e).trans (a.L0 t e)⟩

/-- A change of one virtual row that leaves its weights on the row's entries, and their first
column. -/
def KeepsL (f : HRow → HRow) : Prop := ∀ row, (f row).L = row.L ∧ (f row).L0 = row.L0

theorem same_onRow (F : Fork) (t r : Nat) {f : HRow → HRow} (hf : KeepsL f) :
    Same F (onRow F t r f) := by
  refine ⟨rfl, rfl, by simp [onRow], fun t' => ?_, fun t' => ?_, fun t' => ?_, fun t' => ?_,
    fun t' => ?_, fun t' e => ?_, fun t' e => ?_⟩
  · rw [tree_onRow]; split <;> rfl
  · rw [tree_onRow]; split <;> rfl
  · rw [tree_onRow]; split <;> rfl
  · rw [tree_onRow]; split <;> rfl
  · rw [tree_onRow]
    split
    · simp
    · rfl
  · unfold rowAt
    rw [tree_onRow]
    split
    · show (((F.trees.getD t' {}).rows.modify r f).getD e {}).L = _
      rw [getD_modify]
      split
      · exact (hf _).1
      · rfl
    · rfl
  · unfold rowAt
    rw [tree_onRow]
    split
    · show (((F.trees.getD t' {}).rows.modify r f).getD e {}).L0 = _
      rw [getD_modify]
      split
      · exact (hf _).2
      · rfl
    · rfl

theorem same_foldl {α : Type} (tr ro : α → Nat) (f : Fork → α → HRow → HRow)
    (hf : ∀ F a, KeepsL (f F a)) : ∀ (l : List α) (F : Fork),
      Same F (l.foldl (fun F a => onRow F (tr a) (ro a) (f F a)) F)
  | [], F => Same.refl F
  | a :: l, F => (same_onRow F _ _ (hf F a)).trans (same_foldl tr ro f hf l _)

theorem same_tables (tl : HTailF2) (F : Fork) : Same F (coefTables tl F) := by
  unfold coefTables
  refine forIn_inv (Same F) _ (fun n s hs => ?_) _ _ (Same.refl F)
  dsimp only
  split
  · split
    · exact ⟨_, rfl, hs.trans (same_onRow _ _ _ fun _ => ⟨rfl, rfl⟩)⟩
    · exact ⟨_, rfl, hs⟩
  · exact ⟨_, rfl, hs⟩

theorem same_pieces (tl : HTailF2) (g : Forest.Heard) (F : Fork) : Same F (coefPieces tl g F) := by
  rw [coefPieces_eq]
  exact same_foldl (fun a : Nat × Piece => a.2.tree) (fun a => a.2.row) (Fo.pieceF tl g)
    (fun _ _ _ => ⟨rfl, rfl⟩) _ _

theorem same_powers (tl : HTailF2) (theta : E) (F : Fork) : Same F (coefPowers tl theta F) := by
  have h1 := same_onRow F tl.ix.ZZ tl.zzRowReads
    (f := fun row => formPowers { row with coef := tl.vt } theta tl.tau) (fun _ => ⟨rfl, rfl⟩)
  exact h1.trans (same_onRow _ tl.ix.ZZ tl.zzRowTies
    (f := fun row => formPowers { row with coef := tl.vp } theta tl.tau) (fun _ => ⟨rfl, rfl⟩))

theorem same_bz (tl : HTailF2) (g : Forest.Heard) (F : Fork) : Same F (coefBZ tl g F) := by
  have h0 := same_onRow F tl.ix.BZ 0
    (f := fun row => formPoint { row with coef := eqTab ((g.zb 0).extract 0 5) }
      ((g.zb 0).extract 0 5) 0) (fun _ => ⟨rfl, rfl⟩)
  have h1 := h0.trans (same_onRow _ tl.ix.BZ 1
    (f := fun row => formPoint { row with coef := eqTab ((g.zb 1).extract 0 5) }
      ((g.zb 1).extract 0 5) 0) (fun _ => ⟨rfl, rfl⟩))
  exact h1.trans (same_onRow _ tl.ix.BZ 2
    (f := fun row => formOnes { row with coef := Array.replicate 32 oneE }) (fun _ => ⟨rfl, rfl⟩))

theorem same_mats (tl : HTailF2) (theta : E) (F : Fork) : Same F (coefMats tl theta F) := by
  rw [coefMats_eq]
  exact same_foldl (fun mu => tl.gtTree.getD mu 0) (fun _ => 0)
    (fun _ mu row => formPowers { row with coef := tl.rowX.getD mu #[] } (powE theta tl.stepF)
      (tl.shp.getD mu {}).mS) (fun _ _ _ => ⟨rfl, rfl⟩) _ _

/-- **The step that lays the weights leaves these ten fields.** -/
theorem same_coefBody (tl : HTailF2) (g : Forest.Heard) (F : Fork) : Same F (coefBody tl g F) :=
  ((((same_tables tl F).trans (same_pieces tl g _)).trans (same_powers tl _ _)).trans
    (same_bz tl g _)).trans (same_mats tl _ _)

end VerifiableInference.Desc.First.TailClaims.Law.Tests

#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.same_onRow
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.same_foldl
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.same_coefBody
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.Same
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.Same.refl
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.Same.trans
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.KeepsL
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.same_tables
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.same_pieces
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.same_powers
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.same_bz
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.same_mats
