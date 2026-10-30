-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/HonestKeyRO.lean: `ZKCP.HasExtractionError` (ZKCP/Optional.lean) passes to every
extractor with the same index part; and the bound `deltaB (D.WO o)` in its parameters.




Statements and short proofs.

`HasExtractionError A E δ` (ZKCP/Optional.lean): for every i, Pr[ what E extracts as the index from
the honest committer's verification key and trace is not i (no index counts too) ] ≤ δ.

Why: this is the
optional requirement of the work that this protocol builds on (lean/CREDITS.md, "Further work";
ZKCP/Optional.lean:
HasExtractionError). The requirement reads the index part alone.






Main names:
  `ZKCP.extraction_of_Ei`: `HasExtractionError A E δ` passes to every E' with the same index part.









  `Spec.deltaB_WO_le`: `deltaB (D.WO o)` is 2 (2 · 2^d)² / 2^λ with d = ⌈log₂ L.wordLength⌉ (by definition,
    and `depth_WO`); the statement: for any inhabited type Nn of nonces and L.wordLength ≤ 2^a,
    `deltaB (D.WO o)` ≤ 2^(2 a + 3) / 2^λ.

Limits: the chance is over the oracle and the committer's coins: an average over honest keys. This
file does not say that the honest key is good (a failed search leaves a key under which V rejects;
the index is extracted all the same). It says nothing on a committer that is not the honest one.
What the head of CompileK/GrindHonest.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import CompileK.GrindHonest
import CompileK.WideLang
import CompileK.KnowWidePass
import CompileK.Recompute
import CompileK.KnowLocal

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP

/-- The extraction error reads the extractor's index part alone. -/
theorem extraction_of_Ei {lam : ℕ} {I X W IVK ISK Pf : Type}
    (A : Arg lam I X W IVK ISK Pf) (E E' : Extractor lam I X W IVK Pf) {δ : ℝ≥0∞}
    (h : ∀ v tr, E'.Ei v tr = E.Ei v tr) (H : HasExtractionError A E δ) :
    HasExtractionError A E' δ := by
  intro i
  refine le_trans (le_of_eq ?_) (H i)
  congr 1
  funext _
  ext o
  show E'.Ei o.1.1 o.2 ≠ some i ↔ E.Ei o.1.1 o.2 ≠ some i
  rw [h]

end ZKCP

namespace Compile.Batch
open Iop Rom ZKCP Top.Batch Top.ProgDraw

namespace Spec

/-- The bound in its parameters. -/
def deltaB_WO_le : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (I X : Type) (L : BatchProtocol I X) (lam : ℕ) (D : DataK L lam)
      (o : Option (Work Nn L)) (a : ℕ),
    L.wordLength ≤ 2 ^ a → deltaB (D.WO o) ≤ (2 : ℝ≥0∞) ^ (2 * a + 3) / 2 ^ lam

end Spec

/-- The depth of the tree over an encoded index, with work or without. -/
theorem depth_WO {Nn : Type} [Inhabited Nn] {I X : Type} {L : BatchProtocol I X} {lam : ℕ}
    (D : DataK L lam) (o : Option (Work Nn L)) :
    (D.WO o).depth = Nat.clog 2 L.wordLength := by
  cases o <;> rfl

theorem deltaB_WO_le : Spec.deltaB_WO_le := by
  intro Nn _ I X L lam D o a ha
  unfold deltaB
  rw [depth_WO]
  have hd : Nat.clog 2 L.wordLength ≤ a := (Nat.clog_le_iff_le_pow (by norm_num)).2 ha
  refine ENNReal.div_le_div_right ?_ _
  have e : (2 : ℝ≥0∞) ^ (2 * a + 3) = 2 * ((2 * 2 ^ a : ℕ) : ℝ≥0∞) ^ 2 := by
    push_cast
    ring
  rw [e]
  gcongr
  norm_num

end Compile.Batch
