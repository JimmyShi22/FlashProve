-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/RecRowsAtIndex.lean: what the linear claim's shared rounds (the shared chain)
read of the committed table's key (Johnson/Bind/ForProver/RecRows.lean,
Johnson/Bind/ForProver/RecRowsK14.lean), at the key `oodIdxSh`
(Johnson/Bind/ForProver/OodAtIndex.lean): the index a well-formed matrix of digits (`Cm.Idx`), read
through the library's reader of an index's digits (`OnBytes.HonestTrace.entryOf`,
Johnson/HonestTrace/IndexReaders.lean). Instances, by unfolding.

Main names (namespace `Bind.ForProver`).
  `factorsOwn_oodIdxSh`   no factor is 0, in the description's own spelling.
  `recEq_oodIdxSh`   "(rec_gamma)"'s equation (`Desc.K14.Law.RecEq`) at the key's answers and the
    rows' fold under any coefficients, where a message has room for its pads (3 s ≤ l); at the shape
    `indexOf sh`. In these two nothing ties sh to Z.
  **`ownAnswers_rowsOf_idx`**   every answer of the key, seed by seed and row by row, at the shared
    rounds' own rows (`ProofFile.Honest.K14.rowsOf`), where sh is Z's shape and `rowsFit` passes.

Limits. Those of the three files that are called. One committed table; which of the protocol's
tables it is, the first or a copy, is not said here. The item 0 is a session's numbering, not the
link's (Johnson/Bind/ForProver/Enc.lean, Limits, "Which item"). It means something at the full
size's shape alone: `Cm.Idx` is typed at the reference sizes. No public part is shown here at which
`rowsFit` passes: `rowsFit_of_ok` (Johnson/Bind/ForProver/K14Rows.lean) gives it from the verifier's
own test on the shape; `rowsFit_inScope` and `shapeOf_inScope`
(Johnson/Bind/ForProver/ShapeInScope.lean) from files in scope at which the maker of the public part
(`ProofFile.pubPlain`) returns; no theorem here gives it from files out of scope at
which it returns. (The library calls a fold's coefficients `weights`; they are not the model's.) No
correctness of extraction, no binding of the commitment (the opening form, `BindsWith`,
VerifiableInference/MoreStatements.lean), no soundness, no completeness, no index privacy; nothing
on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.RecRowsK14
import Johnson.Bind.ForProver.OodAtIndex

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open OnBytes (E SampleSeed TableKey zeroE thetaE)
open OnBytes.Model (Reading)
open Desc.K14.Law (eqK RecEq)
open ProofFile.Honest (TableRand Weights Isk)

section
variable (sh : Bind.Twin.Shape) (Z : ProofFile.Pub) (k : Isk Cm.Idx (ℕ → TableRand) (Seed sh × ℕ))

/-- No factor is 0, in the description's own spelling. -/
theorem factorsOwn_oodIdxSh :
    ((oodIdxSh sh Z k).seeds.all (!VerifiableInference.Desc.Own.allZero ·.beta)) = true :=
  factorsOwn_oodSh sh Z (iskOfIdx k)

/-- (rec_gamma)'s equation, under any coefficients, where a message has room for its pads (3 s ≤
l). -/
theorem recEq_oodIdxSh (h3 : 3 * sh.s ≤ sh.l) (i : ℕ) (y : SampleSeed)
    (hy : (oodIdxSh sh Z k).seeds[i]? = some y) (w : ℕ → Cb.Gl.E) :
    RecEq (indexOf sh) (y.z.map Reading.gl.val) (Reading.gl.val y.beta)
      (fun t => Reading.gl.val (thetaE t)) i w
      (fun j => Reading.gl.val ((oodIdxSh sh Z k).record.getD j zeroE))
      (fun j => ∑ r ∈ Finset.range (2 ^ sh.v), w r *
        msgK sh (entryOfPub Z ⟨OnBytes.HonestTrace.entryOf k.index⟩) (k.coins 0) r j) :=
  recEq_oodSh sh Z (iskOfIdx k) h3 i y hy w

/-- **Every answer of the key, at the shared rounds' own rows.** -/
theorem ownAnswers_rowsOf_idx (h : sh = shapeOf Z)
    (hfit : rowsFit sh (linOf Z).kLo (linOf Z).matrixRows = true) :
    ∀ x ∈ (oodIdxSh sh Z k).seeds.zipIdx, ∀ r < (linOf Z).fold.index.rows,
      (∑ j ∈ Finset.range (linOf Z).fold.index.plain, eqK (x.1.z.map Reading.gl.val) j *
          Reading.gl.val (ProofFile.Honest.K14.rowsOf (linOf Z) ⟨OnBytes.HonestTrace.entryOf k.index⟩
            ⟨(k.coins 0).pad, (k.coins 0).tail⟩ r j)) +
        ∑ t ∈ Finset.range 3, Reading.gl.val x.1.beta * Reading.gl.val (thetaE t) *
          Reading.gl.val (ProofFile.Honest.K14.rowsOf (linOf Z) ⟨OnBytes.HonestTrace.entryOf k.index⟩
            ⟨(k.coins 0).pad, (k.coins 0).tail⟩ r ((linOf Z).fold.index.padPlace x.2 t)) =
      Reading.gl.val
        ((oodIdxSh sh Z k).record.getD (r * (linOf Z).fold.index.answers + x.2) zeroE) :=
  ownAnswers_rowsOf_sh sh Z h (iskOfIdx k) hfit

end

end Bind.ForProver

#print axioms Bind.ForProver.factorsOwn_oodIdxSh
#print axioms Bind.ForProver.recEq_oodIdxSh
#print axioms Bind.ForProver.ownAnswers_rowsOf_idx
