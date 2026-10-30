-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/At/RootsSum.lean: HOW MANY ROOTS EACH CHAIN's DECLARED ROUNDS SEND AT THE
WRITTEN DESCRIPTION `WP` (Johnson/AtFull/ProofPlan/WP.lean): 83, 11 AND 4; AND SO THE NUMBER OF THE
THIRD CHAIN's FIRST OWN TREE: 84. Four general statements and four closed facts.

Why. `BookPlan.sentOraclesMatchEntries` (Johnson/Desc/BookPlan.lean) and `FileDescription.lastChainFirstTreeNumber`
(Johnson/Desc/Block.lean), which `FileDescription.labelsOk` reads, carry a sum along a chain's declared
rounds. The first chain has 48293. Lean's kernel evaluates lazily: a number that grows along a list
stays a term as deep as the list is long (Johnson/G/Eager.lean). Here the sum is evaluated by that
file's `sumE`, which makes the kernel evaluate it at every step.

`foldl_roots`, `roots_of_sumE`: the carried sum is the sum of the list of the rounds' numbers of
roots; it is had from an evaluation of `sumE`. `firstTree₃_of`: `FileDescription.lastChainFirstTreeNumber` with the first
chain's sum given; stated of any description, because at a closed one the kernel sets out to
evaluate the sum. `allTold_of_sums`: `BookPlan.sentOraclesMatchEntries` with its three sums given. `wp_roots₁`,
`wp_roots₂`, `wp_roots₃`, `wp_firstTree₃`: the closed facts; the three sums each by an evaluation in
Lean's kernel, which ends at Lean's default thread stack. One limit is raised for them: maxRecDepth
to 1000000.

Limits. Facts on one closed written description. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.ProofPlan.WP
import Johnson.G.Eager

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VerifiableInference.Desc
open P2Law.ProofPlan (WP)

namespace Johnson.AtFull.ProofPlan

/-- The sum that is carried along the rounds is the sum of the list of the rounds' numbers of
roots. -/
theorem foldl_roots (l : List Fmt.DeclaredRound) (a : Nat) :
    l.foldl (fun n r => n + r.entry.roots) a = a + (l.map (·.entry.roots)).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
    omega

/-- The carried sum, from an evaluation of the eager sum. -/
theorem roots_of_sumE {l : List Fmt.DeclaredRound} {n : Nat}
    (h : Johnson.G.sumE 0 (l.map (·.entry.roots)) = n) :
    l.foldl (fun n r => n + r.entry.roots) 0 = n := by
  subst h
  rw [foldl_roots, Johnson.G.sumE_eq]

/-- The number of the third chain's first own tree, with the first chain's sum given. Stated of any
description: at a closed one the kernel would set out to evaluate the sum. -/
theorem firstTree₃_of {Xi : Type} {F : FileDescription Xi} {n : Nat}
    (h : F.roundsDeclaredByBlocks.1.foldl (fun n r => n + r.entry.roots) 0 = n) : F.lastChainFirstTreeNumber = n + 1 := by
  unfold FileDescription.lastChainFirstTreeNumber
  rw [h]

/-- `BookPlan.sentOraclesMatchEntries` with its three sums given. -/
theorem allTold_of_sums {D : BookPlan.DeclaredRoundsByChain} {T : BookPlan.SentOraclesByChain} {n₁ n₂ n₃ : Nat}
    (h₁ : D.1.foldl (fun n r => n + r.entry.roots) 0 = n₁)
    (h₂ : D.2.1.foldl (fun n r => n + r.entry.roots) 0 = n₂)
    (h₃ : D.2.2.foldl (fun n r => n + r.entry.roots) 0 = n₃) :
    BookPlan.sentOraclesMatchEntries D T =
      (T.length == 3 && [n₁, n₂, n₃].zipIdx.all fun c => ((T[c.2]?).getD []).length == c.1) := by
  subst h₁ h₂ h₃
  rfl

set_option maxRecDepth 1000000 in
theorem wp_roots₁ : WP.roundsDeclaredByBlocks.1.foldl (fun n r => n + r.entry.roots) 0 = 83 :=
  roots_of_sumE (by decide +kernel)

set_option maxRecDepth 1000000 in
theorem wp_roots₂ : WP.roundsDeclaredByBlocks.2.1.foldl (fun n r => n + r.entry.roots) 0 = 11 :=
  roots_of_sumE (by decide +kernel)

set_option maxRecDepth 1000000 in
theorem wp_roots₃ : WP.roundsDeclaredByBlocks.2.2.foldl (fun n r => n + r.entry.roots) 0 = 4 :=
  roots_of_sumE (by decide +kernel)

theorem wp_firstTree₃ : WP.lastChainFirstTreeNumber = 84 := firstTree₃_of wp_roots₁

end Johnson.AtFull.ProofPlan

#print axioms Johnson.AtFull.ProofPlan.foldl_roots
#print axioms Johnson.AtFull.ProofPlan.roots_of_sumE
#print axioms Johnson.AtFull.ProofPlan.firstTree₃_of
#print axioms Johnson.AtFull.ProofPlan.allTold_of_sums
#print axioms Johnson.AtFull.ProofPlan.wp_roots₁
#print axioms Johnson.AtFull.ProofPlan.wp_roots₂
#print axioms Johnson.AtFull.ProofPlan.wp_roots₃
#print axioms Johnson.AtFull.ProofPlan.wp_firstTree₃
