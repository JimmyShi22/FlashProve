-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/RecRowsK14.lean: the law on the answers of the key of the out-of-domain (OOD)
sample (`ownAnswers_oodSh`, Johnson/Bind/ForProver/RecRows.lean), with each row read as the honest
side of the linear claim's shared rounds (the shared chain) reads it (`ProofFile.Honest.K14.rowsOf`,
Johnson/Desc/ProofFile/Honest/K14/Parts.lean).

Main names (namespace `Bind.ForProver`).
  `gl_rowsOf`   below the message's length, at a row that the table has, where the test `rowsFit`
    passes: `rowsOf`'s entry, read in the extension field, is `msgK`: over `rowsOf_eq`
    (Johnson/Bind/ForProver/K14Rows.lean) and `gl_eOfF` (Johnson/Bind/ForProver/LocHonest.lean).
  **`ownAnswers_rowsOf`**   for each seed of the key `ood Z k` with its number i, and each row r:
    the sum of eq(z, j) times the row's entry j over the plain entries, plus the factor times 1, X,
    X^2 on the three pads of answer i, is what the key holds at r · answers + i, as read. The row is
    `rowsOf` at the public part's shape, k's index and k's coins of item 0.
  `ownAnswers_rowsOf_sh`   the same of `oodSh sh Z k`, where sh is Z's shape.

Limits. One committed table; which of the protocol's tables it is, the first or a copy, is not said
here. The item 0 is a session's numbering, not the link's (Johnson/Bind/ForProver/Enc.lean, Limits,
"Which item"). Asked: `rowsFit`, a test on the public part alone. No public part is shown here at
which `rowsFit` passes: `rowsFit_of_ok` (Johnson/Bind/ForProver/K14Rows.lean) gives it from the
verifier's own test on the shape; `rowsFit_inScope` and `shapeOf_inScope`
(Johnson/Bind/ForProver/ShapeInScope.lean) from files in scope at which the maker of the public part
(`ProofFile.pubPlain`) returns.
The two sums read a row below the message's length: nothing on a row's tail.
Nothing here says that the state's key in a run is `ood` at these readers. Nothing here says that
the seeds are those of the table's name. The form at the index type
`Cm.Idx`: Johnson/Bind/ForProver/RecRowsAtIndex.lean. An equation in a field: no completeness, no
soundness, no correctness of extraction, no binding of the commitment (the opening form,
`BindsWith`, VerifiableInference/MoreStatements.lean), no index privacy; nothing on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.RecRows
import Johnson.Bind.ForProver.LocHonest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open OnBytes (E SampleSeed TableKey zeroE thetaE)
open OnBytes.Model (Reading)
open Desc.K14.Law (eqK)
open ProofFile.Honest (TableRand Weights Isk)

/-- **A row's entry as the shared rounds' honest side reads it, read in the field, is `msgK`.** -/
theorem gl_rowsOf (Z : ProofFile.Pub) (w : Weights) (ρ : TableRand)
    (hfit : rowsFit (shapeOf Z) (linOf Z).kLo (linOf Z).matrixRows = true) (r j : ℕ)
    (hr : r < 2 ^ (linOf Z).fold.index.v) (hj : j < (linOf Z).fold.index.code.ell) :
    Reading.gl.val (ProofFile.Honest.K14.rowsOf (linOf Z) w ⟨ρ.pad, ρ.tail⟩ r j) =
      msgK (shapeOf Z) (entryOfPub Z w) ρ r j := by
  rw [rowsOf_eq (linOf Z) w ρ hfit r j hr]
  unfold rowLaidE
  rw [if_pos hj, gl_eOfF]
  rfl

/-- **Every answer of the key, seed by seed and row by row, at the shared rounds' own rows.** -/
theorem ownAnswers_rowsOf (Z : ProofFile.Pub) (k : Isk Weights (ℕ → TableRand) (Seed (shapeOf Z) × ℕ))
    (hfit : rowsFit (shapeOf Z) (linOf Z).kLo (linOf Z).matrixRows = true) :
    ∀ x ∈ (ood Z k).seeds.zipIdx, ∀ r < (linOf Z).fold.index.rows,
      (∑ j ∈ Finset.range (linOf Z).fold.index.plain, eqK (x.1.z.map Reading.gl.val) j *
          Reading.gl.val (ProofFile.Honest.K14.rowsOf (linOf Z) k.index
            ⟨(k.coins 0).pad, (k.coins 0).tail⟩ r j)) +
        ∑ t ∈ Finset.range 3, Reading.gl.val x.1.beta * Reading.gl.val (thetaE t) *
          Reading.gl.val (ProofFile.Honest.K14.rowsOf (linOf Z) k.index
            ⟨(k.coins 0).pad, (k.coins 0).tail⟩ r ((linOf Z).fold.index.padPlace x.2 t)) =
      Reading.gl.val ((ood Z k).record.getD (r * (linOf Z).fold.index.answers + x.2) zeroE) := by
  intro x hx r hr
  obtain ⟨h3, -⟩ := rowsFit_spec (S := linOf Z) hfit
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 hx)
  have hi : x.2 < (linOf Z).fold.index.answers :=
    lt_of_lt_of_eq hlt (fits_spell (shapeOf Z) k.seed.1).1
  refine Eq.trans ?_ (ownAnswers_oodSh (shapeOf Z) Z k h3 x hx r hr)
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun j hj => ?_)
    (Finset.sum_congr rfl fun t ht => ?_)
  · rw [gl_rowsOf Z k.index (k.coins 0) hfit r j hr
      (lt_of_lt_of_le (Finset.mem_range.1 hj) (Nat.sub_le _ _))]
  · have ht' := Finset.mem_range.1 ht
    have hp : (linOf Z).fold.index.padPlace x.2 t < (linOf Z).fold.index.code.ell := by
      unfold OnBytes.Params.IndexShape.padPlace OnBytes.Params.IndexShape.plain
        OnBytes.Params.IndexShape.pads
      omega
    rw [gl_rowsOf Z k.index (k.coins 0) hfit r _ hr hp]
    rfl

/-- The same of `oodSh sh Z k`, where sh is the public part's shape. -/
theorem ownAnswers_rowsOf_sh (sh : Bind.Twin.Shape) (Z : ProofFile.Pub) (h : sh = shapeOf Z)
    (k : Isk Weights (ℕ → TableRand) (Seed sh × ℕ))
    (hfit : rowsFit sh (linOf Z).kLo (linOf Z).matrixRows = true) :
    ∀ x ∈ (oodSh sh Z k).seeds.zipIdx, ∀ r < (linOf Z).fold.index.rows,
      (∑ j ∈ Finset.range (linOf Z).fold.index.plain, eqK (x.1.z.map Reading.gl.val) j *
          Reading.gl.val (ProofFile.Honest.K14.rowsOf (linOf Z) k.index
            ⟨(k.coins 0).pad, (k.coins 0).tail⟩ r j)) +
        ∑ t ∈ Finset.range 3, Reading.gl.val x.1.beta * Reading.gl.val (thetaE t) *
          Reading.gl.val (ProofFile.Honest.K14.rowsOf (linOf Z) k.index
            ⟨(k.coins 0).pad, (k.coins 0).tail⟩ r ((linOf Z).fold.index.padPlace x.2 t)) =
      Reading.gl.val
        ((oodSh sh Z k).record.getD (r * (linOf Z).fold.index.answers + x.2) zeroE) := by
  subst h
  exact ownAnswers_rowsOf Z k hfit

end Bind.ForProver

#print axioms Bind.ForProver.gl_rowsOf
#print axioms Bind.ForProver.ownAnswers_rowsOf
#print axioms Bind.ForProver.ownAnswers_rowsOf_sh
