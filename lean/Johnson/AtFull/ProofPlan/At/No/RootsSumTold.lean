-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/At/No/RootsSumTold.lean: FOR A NEGATIVE LINE: HOW MANY ROOTS EACH CHAIN's
DECLARED ROUNDS SEND AT `wpTold` (Johnson/AtFull/ProofPlan/At/Bent2.lean: the written description
with one thing turned): 83, 11 AND 4, AS AT `WP`: what is turned there is what the blocks tell, not
what the rounds send. Three closed facts, each by an evaluation in Lean's kernel of the eager sum
(Johnson/AtFull/ProofPlan/At/RootsSum.lean). One limit is raised for them: maxRecDepth to 1000000.

Limits. Facts on a made-up value. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.ProofPlan.At.RootsSum
import Johnson.AtFull.ProofPlan.At.Bent2

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VerifiableInference.Desc
open P2Law.ProofPlan (wpTold)

namespace Johnson.AtFull.ProofPlan

set_option maxRecDepth 1000000 in
theorem wpTold_roots₁ : wpTold.roundsDeclaredByBlocks.1.foldl (fun n r => n + r.entry.roots) 0 = 83 :=
  roots_of_sumE (by decide +kernel)

set_option maxRecDepth 1000000 in
theorem wpTold_roots₂ : wpTold.roundsDeclaredByBlocks.2.1.foldl (fun n r => n + r.entry.roots) 0 = 11 :=
  roots_of_sumE (by decide +kernel)

set_option maxRecDepth 1000000 in
theorem wpTold_roots₃ : wpTold.roundsDeclaredByBlocks.2.2.foldl (fun n r => n + r.entry.roots) 0 = 4 :=
  roots_of_sumE (by decide +kernel)

end Johnson.AtFull.ProofPlan

#print axioms Johnson.AtFull.ProofPlan.wpTold_roots₁
#print axioms Johnson.AtFull.ProofPlan.wpTold_roots₂
#print axioms Johnson.AtFull.ProofPlan.wpTold_roots₃
