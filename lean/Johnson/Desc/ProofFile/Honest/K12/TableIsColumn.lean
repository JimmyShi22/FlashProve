-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/TableIsColumn.lean: a sent table's column, as a view shows it, is
the sending's column: for the tables that a sending's part lays (`sentTables`,
Honest/K14/Sendings.lean): where a public check on the tree's width says yes, the table number μ is
there, and at every position its column (`Table.col`, Honest/Frame.lean) is `columnOf` … μ. And that
check under the library's head.

Why a check is wanted. A table holds field elements: the sender reads each word of `columnOf` into
the field, as many as the tree's declared width; `Table.col` writes them out again. So the two are
one list where every word is a written form (it is: a law) and the column is just as long as the
declared width: that is up to the plan.

  `widthFits`    THE PUBLIC CHECK, with code: the tree is there, and its declared width is three
                 words for each main row and each mask row of the messages that lie in it
  `length_symbolsOf`, `canonW_symbolsOf`, `length_flat`, `length_columnOf`, `canonW_columnOf`
                 lengths; written forms
  `col_sent`     the statement
  `widthFits_plan`   the check reads of a plan its codes and shape
  `width_real`   the check at the typed sizes: one evaluation by Lean's kernel
  `width_head`   the check under the head, at every number n of "LIN point"

By what. `symbolsOf_field` (TreeIsColumn.lean); `columnOf_mine` (TreeIsColumnAt.lean);
`written_at_head`, `qAt_written` (FitAtHead.lean), as `colFits_head` (TreeIsColumnAtHead.lean) calls
them.

Limits. The sender's side alone: no member of a test, no run. "send o_u"'s tree number 0 and
"send o_omega"'s tree number 1 alone under the head. A message whose main rows are over the base
field has one word a row: there the check says no (TableIsColumnSmall.lean has such a control). The
full size alone under the head. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.TreeIsColumnAtHead
import Johnson.Desc.ProofFile.Honest.K12.TableCol

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes.Slice (ofF toF toF_ofF ofE)
open VerifiableInference.Desc.K1 (qAt realSized)
open Johnson.G (codesFull2)
open ProofFile.Honest.K14 (SendJob SendPub jobU jobOmega columnOf symbolsOf sentTables)

/-! ## 1 The check -/

/-- **A public check with code**: the sending's tree number μ is there, and its declared width is
three words for each main row and each mask row of the messages that lie in it. It reads the codes
and the messages' shapes alone. -/
def widthFits (J : SendJob) (μ : ℕ) : Bool :=
  let lay := (VerifiableInference.Desc.Own.treesMade J.Q.codes J.Q.sent).getD {}
  decide (μ < lay.shapes.size) &&
    ((lay.shapes.getD μ {}).mainWidth + (lay.shapes.getD μ {}).maskWidth ==
      3 * ((mineOf J μ).map fun k => (shapeAt J k).mainRows).sum +
        3 * ((mineOf J μ).map fun k => (shapeAt J k).maskRows).sum)

/-! ## 2 Lengths and written forms -/

theorem length_symbolsOf (c : OnBytes.Code) (x n : ℕ) (row tail : ℕ → ℕ → OnBytes.E) :
    (symbolsOf c x n row tail).length = 3 * n := by
  unfold symbolsOf
  rw [List.length_flatMap]
  simp only [List.length_cons, List.length_nil, List.map_const', List.length_range,
    List.sum_replicate, smul_eq_mul]
  omega

theorem canonW_symbolsOf (c : OnBytes.Code) (x n : ℕ) (row tail : ℕ → ℕ → OnBytes.E) :
    CanonW (symbolsOf c x n row tail) := fun w hw => by
  rw [symbolsOf_field] at hw
  obtain ⟨r, -, hr⟩ := List.mem_flatMap.1 hw
  simp only [Fmt.M1.Own.words, ofE, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩

/-- The length of a flat list of symbols over a list of messages. -/
theorem length_flat (l : List ℕ) (f : ℕ → List UInt64) (g : ℕ → ℕ)
    (h : ∀ k, (f k).length = 3 * g k) : (l.flatMap f).length = 3 * (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, ih, h, List.map_cons, List.sum_cons, Nat.mul_add]

theorem length_columnOf (J : SendJob) (L : ℕ → ProofFile.Honest.K14.Laid) (μ x : ℕ) :
    (columnOf J.Q.codes J.Q.sent L μ x).length =
      3 * ((mineOf J μ).map fun k => (shapeAt J k).mainRows).sum +
        3 * ((mineOf J μ).map fun k => (shapeAt J k).maskRows).sum := by
  rw [columnOf_mine, List.length_append,
    length_flat _ _ (fun k => (shapeAt J k).mainRows) fun k => length_symbolsOf _ _ _ _ _,
    length_flat _ _ (fun k => (shapeAt J k).maskRows) fun k => length_symbolsOf _ _ _ _ _]

theorem canonW_columnOf (J : SendJob) (L : ℕ → ProofFile.Honest.K14.Laid) (μ x : ℕ) :
    CanonW (columnOf J.Q.codes J.Q.sent L μ x) := fun w hw => by
  rw [columnOf_mine] at hw
  rcases List.mem_append.1 hw with h | h
  · obtain ⟨k, -, hk⟩ := List.mem_flatMap.1 h
    exact canonW_symbolsOf _ _ _ _ _ w hk
  · obtain ⟨k, -, hk⟩ := List.mem_flatMap.1 h
    exact canonW_symbolsOf _ _ _ _ _ w hk

/-! ## 3 The statement -/

/-- **A SENT TABLE's COLUMN, AS A VIEW SHOWS IT, IS THE SENDING's COLUMN**, where the check on the
width says yes: the table number μ of `sentTables` is there, and at every position its column is
`columnOf` … μ. -/
theorem col_sent (J : SendJob) (L : ℕ → ProofFile.Honest.K14.Laid) (μ : ℕ)
    (hw : widthFits J μ = true) :
    ∃ T, (sentTables J.Q.codes J.Q.sent L)[μ]? = some T ∧
      ∀ x, T.col x = columnOf J.Q.codes J.Q.sent L μ x := by
  unfold widthFits at hw
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
  obtain ⟨h1, h2⟩ := hw
  have hl : μ < ((VerifiableInference.Desc.Own.treesMade J.Q.codes J.Q.sent).getD
      {}).shapes.toList.length := by
    rw [Array.length_toList]
    exact h1
  have hg : ((VerifiableInference.Desc.Own.treesMade J.Q.codes J.Q.sent).getD {}).shapes.toList[μ] =
      ((VerifiableInference.Desc.Own.treesMade J.Q.codes J.Q.sent).getD {}).shapes.getD μ {} := by
    rw [Array.getElem_toList, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1]
    rfl
  refine ⟨_, by
    unfold sentTables
    rw [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hl]
    rfl, fun x => ?_⟩
  have hlen := length_columnOf J L μ x
  rw [← h2, ← hg] at hlen
  refine List.ext_getElem (by
    simp only [Table.col, List.length_ofFn, Nat.zero_add]
    exact hlen.symm) fun i i1 i2 => ?_
  simp only [Table.col, List.getElem_ofFn, Nat.zero_add]
  rw [List.getD_eq_getElem _ _ i2]
  obtain ⟨y, hy⟩ := canonW_columnOf J L μ x _ (List.getElem_mem i2)
  rw [hy, toF_ofF]

/-! ## 4 The check at the typed sizes and under the head -/

theorem widthFits_plan (A : SendPub) (μ : ℕ) :
    widthFits (jobU A) μ = widthFits (jobU (planOf A.P.codes A.P.S)) μ ∧
      widthFits (jobOmega A) μ = widthFits (jobOmega (planOf A.P.codes A.P.S)) μ := ⟨rfl, rfl⟩

theorem width_real : (realSized.all fun q =>
    widthFits (jobU (planOf q.2 q.1.shape)) 0 && widthFits (jobOmega (planOf q.2 q.1.shape)) 1) =
      true := by
  decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **The check at the shared chain's own plan, under the head.** -/
theorem width_head (h : P5J.AtMg o Z D r Zp Np cF) (n : ℕ) :
    widthFits (jobU ⟨qAt Zp Np, n⟩) 0 = true ∧ widthFits (jobOmega ⟨qAt Zp Np, n⟩) 1 = true := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  have k := width_real
  rw [hx] at k
  have k' : (widthFits (jobU (planOf codesFull2 x.shape)) 0 &&
      widthFits (jobOmega (planOf codesFull2 x.shape)) 1) = true := k
  simp only [Bool.and_eq_true] at k'
  refine ⟨?_, ?_⟩
  · rw [(widthFits_plan _ 0).1, qAt_written Wr Np]
    exact k'.1
  · rw [(widthFits_plan _ 1).2, qAt_written Wr Np]
    exact k'.2

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.widthFits
#print axioms ProofFile.Honest.K12.Light.length_symbolsOf
#print axioms ProofFile.Honest.K12.Light.canonW_symbolsOf
#print axioms ProofFile.Honest.K12.Light.length_flat
#print axioms ProofFile.Honest.K12.Light.length_columnOf
#print axioms ProofFile.Honest.K12.Light.canonW_columnOf
#print axioms ProofFile.Honest.K12.Light.col_sent
#print axioms ProofFile.Honest.K12.Light.widthFits_plan
#print axioms ProofFile.Honest.K12.Light.width_real
#print axioms ProofFile.Honest.K12.Light.width_head
