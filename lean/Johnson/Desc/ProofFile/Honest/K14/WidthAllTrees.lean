-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/WidthAllTrees.lean: kind K14: ONE MORE SILENT DEFAULT OF THE TWO
SENDINGS' TEXTS IS NOT TAKEN AT THE FULL SIZE: "a word beyond a column's length: 0" (the head of
Honest/K14/Sendings.lean). A sent table reads as many words of a column as the tree's declared
width. The library's public check widthFits (Honest/K12/TableIsColumn.lean) says that this width is
just the column's length (length_columnOf there); under the library's hypothesis at the full size it
is shown there at two trees alone. Here it is shown AT EVERY TREE OF BOTH SENDINGS.

  widthAll        the check at every tree that the sending's layout has
  widthAll_plan   it reads of a plan its codes and shape
  trees_real, width_all_real   at the typed sizes, by Lean's kernel: "send o_u" has one tree and
                  "send o_omega" two; the check says yes at all three
  width_all_head  **under the hypothesis, at every number n of "LIN point": the check says yes at
                  every tree of both sendings**
  trees_at_head   under the hypothesis "send o_u" has one tree and "send o_omega" two: so the check
                  runs over three trees, not over none
  width_at_head   the check tree by tree

Limits. The sender's side alone: no member of a test, no run. The full size alone. Where the trees
cannot be laid the layout is empty and widthAll says yes for nothing: trees_at_head bars that under
the hypothesis. The two closed lines run over a list of typed sizes and bite where that list has a
member: under the hypothesis it has (written_at_head). That a table's word is then the column's own
word, and not the default, is col_sent (Honest/K12/TableIsColumn.lean); it is not called here.
Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.TableIsColumn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc.K1 (qAt realSized)
open Johnson.G (codesFull2)
open ProofFile.Honest.K12.Light (widthFits planOf written_at_head qAt_written)

/-- How many trees a sending's layout has; 0 where the trees cannot be laid. -/
def treesOf (J : SendJob) : Nat :=
  ((VerifiableInference.Desc.Own.treesMade J.Q.codes J.Q.sent).getD {}).shapes.size

/-- **The check at every tree that the sending's layout has.** -/
def widthAll (J : SendJob) : Bool := (List.range (treesOf J)).all (widthFits J)

theorem widthAll_plan (A : SendPub) :
    widthAll (jobU A) = widthAll (jobU (planOf A.P.codes A.P.S)) ∧
      widthAll (jobOmega A) = widthAll (jobOmega (planOf A.P.codes A.P.S)) := ⟨rfl, rfl⟩

theorem trees_real : (realSized.all fun q =>
    treesOf (jobU (planOf q.2 q.1.shape)) == 1 && treesOf (jobOmega (planOf q.2 q.1.shape)) == 2) =
      true := by
  decide +kernel

theorem width_all_real : (realSized.all fun q =>
    widthAll (jobU (planOf q.2 q.1.shape)) && widthAll (jobOmega (planOf q.2 q.1.shape))) =
      true := by
  decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **Under the hypothesis the check says yes at every tree of both sendings.** -/
theorem width_all_head (h : P5J.AtMg o Z D r Zp Np cF) (n : ℕ) :
    widthAll (jobU ⟨qAt Zp Np, n⟩) = true ∧ widthAll (jobOmega ⟨qAt Zp Np, n⟩) = true := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  have k := width_all_real
  rw [hx] at k
  have k' : (widthAll (jobU (planOf codesFull2 x.shape)) &&
      widthAll (jobOmega (planOf codesFull2 x.shape))) = true := k
  simp only [Bool.and_eq_true] at k'
  refine ⟨?_, ?_⟩
  · rw [(widthAll_plan _).1, qAt_written Wr Np]
    exact k'.1
  · rw [(widthAll_plan _).2, qAt_written Wr Np]
    exact k'.2

theorem treesOf_plan (A : SendPub) :
    treesOf (jobU A) = treesOf (jobU (planOf A.P.codes A.P.S)) ∧
      treesOf (jobOmega A) = treesOf (jobOmega (planOf A.P.codes A.P.S)) := ⟨rfl, rfl⟩

/-- **Under the hypothesis "send o_u" has one tree and "send o_omega" two**: so the check above runs
over three trees, not over none. -/
theorem trees_at_head (h : P5J.AtMg o Z D r Zp Np cF) (n : ℕ) :
    treesOf (jobU ⟨qAt Zp Np, n⟩) = 1 ∧ treesOf (jobOmega ⟨qAt Zp Np, n⟩) = 2 := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  have k := trees_real
  rw [hx] at k
  have k' : (treesOf (jobU (planOf codesFull2 x.shape)) == 1 &&
      treesOf (jobOmega (planOf codesFull2 x.shape)) == 2) = true := k
  simp only [Bool.and_eq_true, beq_iff_eq] at k'
  refine ⟨?_, ?_⟩
  · rw [(treesOf_plan _).1, qAt_written Wr Np]
    exact k'.1
  · rw [(treesOf_plan _).2, qAt_written Wr Np]
    exact k'.2

/-- The same tree by tree. -/
theorem width_at_head (h : P5J.AtMg o Z D r Zp Np cF) (n : ℕ) :
    (∀ μ, μ < treesOf (jobU ⟨qAt Zp Np, n⟩) → widthFits (jobU ⟨qAt Zp Np, n⟩) μ = true) ∧
      ∀ μ, μ < treesOf (jobOmega ⟨qAt Zp Np, n⟩) →
        widthFits (jobOmega ⟨qAt Zp Np, n⟩) μ = true :=
  ⟨fun μ hμ => List.all_eq_true.1 (width_all_head h n).1 μ (List.mem_range.2 hμ),
    fun μ hμ => List.all_eq_true.1 (width_all_head h n).2 μ (List.mem_range.2 hμ)⟩

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.widthAll_plan
#print axioms ProofFile.Honest.K14.trees_real
#print axioms ProofFile.Honest.K14.width_all_real
#print axioms ProofFile.Honest.K14.width_all_head
#print axioms ProofFile.Honest.K14.trees_at_head
#print axioms ProofFile.Honest.K14.width_at_head
