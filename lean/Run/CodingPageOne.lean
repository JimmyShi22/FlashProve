-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CodingPageOne.lean: the encoding of the queries of Run/CodingPage.lean has one block for a leaf
and one for a node.

Four theorems, each by definition.

Why: the step to a single oracle (CompileK) speaks of every encoding m with m.blocks OracleName.leaf = 1
and m.blocks OracleName.node = 1.
Run/CodingImpl.lean has the two equations at its generic encoding (`implA_leaf`, `implA_node`). Here
they stand by name at the encoding of the queries of Run/CodingPage.lean (`theImpl`), and at its
instance made from a chain's description.

Main names: `theImpl_leaf1`, `theImpl_node1` (for all data C, at any tag); `PQ.pageQ_leaf1`,
`PQ.pageQ_node1`.

Limits: this file does not say that any other hypothesis of that step is met at these data.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PageQ

set_option autoImplicit false

namespace Run
open Rom Compile Compile.Batch Iop

theorem theImpl_leaf1 {I X : Type} {L : BatchProtocol I X} {K : ℕ} {tg : Tag} (C : PageC L K tg) :
    (theImpl C).blocks Batch.OracleName.leaf = 1 := rfl

theorem theImpl_node1 {I X : Type} {L : BatchProtocol I X} {K : ℕ} {tg : Tag} (C : PageC L K tg) :
    (theImpl C).blocks Batch.OracleName.node = 1 := rfl

theorem PQ.pageQ_leaf1 (S : _root_.Fmt.Spec) (C : PQ.CK) (dec : PQ.View → Bool)
    (K : ℕ) (h : PQ.OKQ S = true) :
    (theImpl (PQ.pageQ S C dec K h)).blocks Batch.OracleName.leaf = 1 := rfl

theorem PQ.pageQ_node1 (S : _root_.Fmt.Spec) (C : PQ.CK) (dec : PQ.View → Bool)
    (K : ℕ) (h : PQ.OKQ S = true) :
    (theImpl (PQ.pageQ S C dec K h)).blocks Batch.OracleName.node = 1 := rfl

end Run
