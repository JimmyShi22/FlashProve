-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/StageNums.lean: a common bound for the errors of all rounds of a stage or chain, and bounds
for the probabilities of the two parts `Bad`, `Win` of its withheld set (`Hon.withheld`). (Words of
this library: lean/GLOSSARY.md.)

A stage's errors are counts, one for each round. The compiler (Compile/) takes them as "every error,
as a probability, is at most c" (`Iop.Err.Below`).
 * `Stage.Below κ`: every error of the stage, as a probability, is at most κ; `Chain.Below`.
 * `Chain.PrLe`, `Chain.PrLe.stage`: if `pBad` and `pWin` of each stage are at most the members of
   two lists, those of the chain are at most the sums of the lists.
Notation: `Bad : Set (Rho B.shape)`: the public bad set: no argument but the block's own ρ;
`Win : Ii → Set (Rho B.shape)`: the rest of the withheld set, which may depend on the state (`Hon`,
Blocks/BlockHon.lean); `S.e : ι → ℕ`: the round that binds the variable i has e i + 1 masked scalars
(`SC`, Blocks/SumCheckBlock.lean).
These errors are numbers that a stage lists (the data field `Stage.ε`, Blocks/Stage.lean; for the
masked sumcheck the list `SC.scErr`, Blocks/SumCheckBlock.lean): that a stage is sound at the
numbers that it lists is no statement of this file; that tie is the field `clean` of `Stage.Props`
(Blocks/Stage.lean), proved for the masked sumcheck by `SC.Prover.props_stage`
(Blocks/SumCheckStage.lean), under its hypotheses.

Round-by-round soundness is the notion of R. Canetti, Y. Chen, J. Holmgren, A. Lombardi, G.
Rothblum, R. Rothblum, ePrint 2018/1004, Definition 5.3.
-/
import Blocks.StageSide

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks

open Iop Prob
open scoped ENNReal

/-! ## One bound for all errors -/

section Below

variable {P E : Type} {a b c : Sorts}

/-- Every error of the stage, as a probability, is at most κ. -/
def Stage.Below (S : Stage P E a b) (κ : ℝ≥0∞) : Prop := Err.Below S.ε κ

theorem Stage.Below.seq {S₁ : Stage P E a b} {S₂ : Stage P E b c} {κ : ℝ≥0∞}
    (h₁ : S₁.Below κ) (h₂ : S₂.Below κ) : (S₁.seq S₂).Below κ :=
  Err.Below.app h₁ h₂

theorem Stage.below_id (a : Sorts) (κ : ℝ≥0∞) : (Stage.id (P := P) (E := E) a).Below κ := trivial

theorem Stage.Below.mono {S : Stage P E a b} {κ κ' : ℝ≥0∞} (h : S.Below κ) (hκ : κ ≤ κ') :
    S.Below κ' :=
  Err.Below.mono_bound hκ h

/-- Every error of every stage of the chain, as a probability, is at most κ. -/
def Chain.Below (κ : ℝ≥0∞) : {a b : Sorts} → Chain P E a b → Prop
  | _, _, .nil _ => True
  | _, _, .cons S t => S.Below κ ∧ t.Below κ

theorem Chain.Below.stage {κ : ℝ≥0∞} :
    ∀ {a b : Sorts} {t : Chain P E a b}, t.Below κ → t.stage.Below κ
  | _, _, .nil a, _ => Stage.below_id a κ
  | _, _, .cons _ _, h => h.1.seq (Chain.Below.stage h.2)

end Below

/-! ## Blocks/StageLib.lean; the masked sumcheck -/

section Lib

variable {P E : Type} [Field E] [Fintype E] [Fintype P] [DecidableEq P] {a b : Sorts} (κ : ℝ≥0∞)

theorem Stage.below_nameScalars
    {K : Type} [Fintype K] [DecidableEq K] (idx : K → P) (val : a.I → K → E) :
    (Stage.nameScalars (E := E) a idx val).Below κ :=
  ⟨by simp, trivial⟩

theorem Stage.below_pure (f : a.X → Option b.X) (g : a.Y → b.Y) (nx : a.I → b.I) :
    (Stage.pure (P := P) (E := E) f g nx).Below κ := trivial

variable {κ}

theorem Stage.below_sample {I' C : Type} [Fintype C] [Nonempty C] (ok : C → Bool)
    (nx : a.I → C → I') (e : ℕ) (pBad : ℝ≥0∞) (h : (e : ℝ≥0∞) ≤ κ * Fintype.card C) :
    (Stage.sample (P := P) (E := E) a I' C ok nx e pBad).Below κ := ⟨h, trivial⟩

/-- g |E|^(g - 1) of the |E|^g points are a fraction of at most g / |E|: if g / |E| ≤ κ (h), this
count is at most κ times the number of points. (Such a count: `Stage.ptFam`, Blocks/StageRows.lean.)
-/
theorem point_le (g : ℕ) (h : (g : ℝ≥0∞) / Fintype.card E ≤ κ) :
    ((g * Fintype.card E ^ (g - 1) : ℕ) : ℝ≥0∞) ≤ κ * Fintype.card (Fin g → E) := by
  have hq0 : (Fintype.card E : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hqt : (Fintype.card E : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · simp
  · rw [Fintype.card_fun, Fintype.card_fin]
    have h1 : Fintype.card E ^ g = Fintype.card E ^ (g - 1) * Fintype.card E := by
      rw [← pow_succ, Nat.sub_add_cancel hg]
    rw [h1]
    push_cast
    calc (g : ℝ≥0∞) * (Fintype.card E : ℝ≥0∞) ^ (g - 1)
        = ((g : ℝ≥0∞) / Fintype.card E) * ((Fintype.card E : ℝ≥0∞) ^ (g - 1) * Fintype.card E) := by
          rw [mul_comm ((Fintype.card E : ℝ≥0∞) ^ (g - 1)),
            ← mul_assoc, ENNReal.div_mul_cancel hq0 hqt]
      _ ≤ κ * ((Fintype.card E : ℝ≥0∞) ^ (g - 1) * Fintype.card E) := by gcongr

/-- The errors of the masked sumcheck (`SC.scErr`): e i + 1 of the |E| challenges of the round that
binds i; `Below κ` if e i + 1 ≤ κ |E| for every i. -/
theorem SC.below_scErr {Y Ξ ι : Type} [DecidableEq E] [DecidableEq ι] (S : SC E Y P Ξ ι)
    (h : ∀ i, ((S.e i + 1 : ℕ) : ℝ≥0∞) ≤ κ * Fintype.card E) :
    ∀ l : List ι, Err.Below (S.scErr l) κ
  | [] => trivial
  | i :: l => ⟨h i, SC.below_scErr S h l⟩

theorem SC.Prover.below_stage {Y Ξ ι A : Type} [DecidableEq E] [DecidableEq ι] {S : SC E Y P Ξ ι}
    (H : S.Prover A) (h : ∀ i, ((S.e i + 1 : ℕ) : ℝ≥0∞) ≤ κ * Fintype.card E) (l : List ι) :
    (H.stage l).Below κ :=
  SC.below_scErr S h l

end Lib

/-! ## The two probabilities -/

section Pr

variable {P E : Type}

/-- The bounds pBad and pWin of each stage of the chain are at most the members of the two lists, in
the order of the stages. -/
def Chain.PrLe : {a b : Sorts} → Chain P E a b → List ℝ≥0∞ → List ℝ≥0∞ → Prop
  | _, _, .nil _, _, _ => True
  | _, _, .cons S t, x :: A, y :: B => S.pBad ≤ x ∧ S.pWin ≤ y ∧ t.PrLe A B
  | _, _, .cons _ _, _, _ => False

/-- Under `Chain.PrLe`: `pBad`, `pWin` of the chain are at most the sums of the lists. -/
theorem Chain.PrLe.stage :
    ∀ {a b : Sorts} {t : Chain P E a b} {A B : List ℝ≥0∞},
      t.PrLe A B → t.stage.pBad ≤ A.sum ∧ t.stage.pWin ≤ B.sum
  | _, _, .nil _, _, _, _ => ⟨zero_le _, zero_le _⟩
  | _, _, .cons _ _, _ :: _, _ :: _, h => by
      obtain ⟨h1, h2⟩ := Chain.PrLe.stage h.2.2
      rw [List.sum_cons, List.sum_cons]
      exact ⟨add_le_add h.1 h1, add_le_add h.2.1 h2⟩

end Pr

end Blocks
