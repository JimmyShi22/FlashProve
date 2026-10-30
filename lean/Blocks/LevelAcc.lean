-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/LevelAcc.lean: lemmas on the levels (Blocks/LevelDef.lean) for an honest run: `ptAt`, the
entries of a combination of rows, the running claim at the end, and the verifier unfolded (`ok_nil`,
`ok_cons`). (Words of this library: lean/GLOSSARY.md.)

Notation: s0, s2: `ℕ → E`; the s0_j, s2_j of `LevSpec.clEnd` (Blocks/LevelDef.lean); `nat v`: a
vector as a function on ℕ, 0 beyond its end (Blocks/Basic.lean).
-/
import Alg.SumCheck
import Blocks.EqN
import Blocks.LevelDef
import Code.Facts
import Iop.InteractiveOracleProof
import Mathlib.Data.FinEnum

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks
namespace LevelAcc
open Iop Prob Finset

/-! ## 1. The point of one round -/

section Alg1

variable {F : Type} [Field F] (a : LevSpec F) {E : Type} [Field E] [Fintype E]
  [DecidableEq E] [Algebra F E]

theorem ptAt_congr {ζ ζ' : ℕ → E} (j : ℕ) (h : ∀ t, t < j → ζ t = ζ' t) (y : E) (z : ℕ) :
    a.ptAt ζ j y z = a.ptAt ζ' j y z := by
  funext t
  unfold LevSpec.ptAt
  by_cases ht : t < j
  · rw [if_pos ht, if_pos ht, h t ht]
  · rw [if_neg ht, if_neg ht]

theorem ptAt_eq_update (ζ : ℕ → E) (j : ℕ) (y y' : E) (z : ℕ) :
    a.ptAt ζ j y z = Function.update (a.ptAt ζ j y' z) j y := by
  funext t
  by_cases ht : t = j
  · subst ht
    rw [Function.update_self]
    unfold LevSpec.ptAt
    rw [if_neg (lt_irrefl t), if_pos rfl]
  · rw [Function.update_of_ne ht]
    unfold LevSpec.ptAt
    by_cases h1 : t < j
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1, if_neg ht, if_neg ht]

end Alg1

/-! ## 2. Combinations of rows, sums -/

section Alg2

variable {F : Type} [Field F] (a : LevSpec F) {E : Type} [Field E] [Fintype E]
  [DecidableEq E] [Algebra F E]

/-- the entries of a combination of the rows -/
theorem nat_comb (A : a.Arr E) (e : Fin a.rows → E) (j : ℕ) :
    nat (fun j' => ∑ i, e i * A i j') j = ∑ i, e i * nat (A i) j := by
  unfold nat
  by_cases h : j < a.code.msg
  · simp only [dif_pos h]
  · simp only [dif_neg h, mul_zero, sum_const_zero]

theorem fm_comb (A : a.Arr E) (e : Fin a.rows → E) :
    a.code.fm (fun j => ∑ i, e i * A i j) (fun _ => (0 : E)) =
      fun t => ∑ i, e i * a.code.fm (A i) (fun _ => (0 : E)) t := by
  funext t
  unfold Code.Enc.fm
  by_cases h : t.val < a.code.msg
  · simp only [dif_pos h]
  · simp only [dif_neg h, dite_eq_ite, ite_self, mul_zero, sum_const_zero]

theorem sum_ofFlat (b : LevSpec F) (g h : ℕ → E) :
    ∑ i, ∑ j, b.ofFlat g i j * b.ofFlat h i j = ∑ t ∈ range (b.rows * b.code.msg), g t * h t := by
  rw [Alg.sum_range_mul_add,
    ← Fin.sum_univ_eq_sum_range
      (fun i => ∑ j ∈ range b.code.msg, g (i * b.code.msg + j) * h (i * b.code.msg + j))]
  refine sum_congr rfl fun i _ => ?_
  rw [← Fin.sum_univ_eq_sum_range
      (fun j => g (i.val * b.code.msg + j) * h (i.val * b.code.msg + j))]
  rfl

end Alg2

/-! ## 3. The running claim at the end; the verifier unfolded -/

section Run

variable {F : Type} [Field F] (a : LevSpec F) {E : Type} [Field E] [Fintype E]
  [DecidableEq E] [Algebra F E]

/-- The running claim at the end depends on the scalars s0, s2 only at the mu rounds. -/
theorem clEnd_congr (v : E) (ζ : ℕ → E) {s0 s2 s0' s2' : ℕ → E}
    (h0 : ∀ j, j < a.mu → s0 j = s0' j) (h2 : ∀ j, j < a.mu → s2 j = s2' j) :
    a.clEnd v ζ s0 s2 = a.clEnd v ζ s0' s2' := by
  unfold LevSpec.clEnd
  congr 1
  exact sum_congr rfl fun j hj => by rw [h0 j (mem_range.mp hj), h2 j (mem_range.mp hj)]

/-- the verifier of the last level accepts if its equations H hold on the two parts σ, tl of the
transcript (`h1`, `h2`) -/
theorem ok_nil (c : a.Claim E) (w : a.Word E) (τ : Tr (levelsShape E a []))
    (σ : Tr (List.replicate a.mu (LinSh.rSC E))) (tl : Tr [a.rTheta E, a.rLast E])
    (h1 : Tr.fst (s := List.replicate a.mu (LinSh.rSC E)) (t := [a.rTheta E, a.rLast E]) τ = σ)
    (h2 : Tr.snd (s := List.replicate a.mu (LinSh.rSC E)) (t := [a.rTheta E, a.rLast E]) τ = tl)
    (H : a.endVal c (ofList ((trList (LinSh.rSC E) a.mu σ).map fun x => x.2)) (nat tl.2.2.1.2.1) =
        a.clEnd c.v (ofList ((trList (LinSh.rSC E) a.mu σ).map fun x => x.2))
          (ofList ((trList (LinSh.rSC E) a.mu σ).map fun x => x.1.2.1))
          (ofList ((trList (LinSh.rSC E) a.mu σ).map fun x => x.1.2.2)) ∧
      ∀ i,
        a.encRow tl.2.2.1.2.1 (tl.2.2.2.1 i) =
          a.foldW w (ofList ((trList (LinSh.rSC E) a.mu σ).map fun x => x.2)) (tl.2.2.2.1 i) ∧
        a.encRow tl.2.2.1.2.2 (tl.2.2.2.1 i) = a.combW w tl.2.1 (tl.2.2.2.1 i)) :
    levelsOk a [] c w τ = true := by
  subst h1 h2
  unfold levelsOk
  simp only [decide_eq_true_eq]
  exact H

/-- the verifier of a level that is not the last, unfolded on the two parts of a transcript -/
theorem ok_cons (b : LevSpec F) (rest : List (LevSpec F)) (c : a.Claim E) (w : a.Word E)
    (τ : Tr (levelsShape E a (b :: rest))) (σ : Tr (List.replicate a.mu (LinSh.rSC E)))
    (tl : Tr (a.rTheta E :: a.rNext E b :: levelsShape E b rest))
    (h1 : Tr.fst (s := List.replicate a.mu (LinSh.rSC E))
        (t := a.rTheta E :: a.rNext E b :: levelsShape E b rest) τ = σ)
    (h2 : Tr.snd (s := List.replicate a.mu (LinSh.rSC E))
        (t := a.rTheta E :: a.rNext E b :: levelsShape E b rest) τ = tl) :
    levelsOk a (b :: rest) c w τ =
      levelsOk b rest
        (a.nextClaim b c w (ofList ((trList (LinSh.rSC E) a.mu σ).map fun x => x.2))
          (ofList ((trList (LinSh.rSC E) a.mu σ).map fun x => x.1.2.1))
          (ofList ((trList (LinSh.rSC E) a.mu σ).map fun x => x.1.2.2)) tl.2.1 tl.2.2.2.1)
        (tl.2.2.1.1 ()) tl.2.2.2.2 := by
  subst h1 h2
  rfl

end Run

end LevelAcc

end Blocks
