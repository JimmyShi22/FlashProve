-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/Declared.lean: THE ENCODED INDEX'S COLUMN HAS THE SHAPE THAT THE OWN
PARAMETERS OF THE LINEAR CLAIM'S SHARED ROUNDS (THE SHARED CHAIN) DECLARE FOR THE COMMITTED TABLE:
depth, width, item: at every value of the structure `ProofFile.Pub`; a column is given only where
`rowsFit` passes. Statements and proofs.

Why. By the library's text the round "LOC" of the shared chain reads a committed table: it declares
`Desc.K14.readsAtLoc P.S.fold P.item` (Johnson/Desc/K14/Blocks.lean), at the parameters P that
`Desc.K14.p14Of` makes of the planner's chains; "No other oracle is read in these rounds"
(`readsAtLoc`'s docstring, Johnson/Desc/K14/Text.lean). Of the description's other rounds nothing is
said here. In the frame for an honest prover a run ends in an error where a committed table's column
has another number of words than the round declares (`fillCols`,
Johnson/Desc/ProofFile/Honest/Frame.lean). `encW` (Johnson/Bind/ForProver/Enc.lean) reads its shape
off the public part on the same road.

Main names (namespace `Bind.ForProver`).
  `declaredAt`: what that round declares, at the parameters off Z.
  `declared_shape`: at every Z and every list for the parameters' last field: what the round
    declares has the depth a, the width 2^v and the salt's length sigma of `shapeOf Z`, and the item
    0: by unfolding.
  **`encW_width`**: whatever column `encW` gives at the item 0 has the declared width.
  `encW_some`: where the test `rowsFit` passes, `encW` gives a column at the item 0 at every
    position below 2^a, a the declared depth.

Limits. That every round of the block "LOC" among the shared rounds' eight blocks declares
`declaredAt` is `blocks_rounds` (Johnson/Desc/K14/Honest/ChainSteps.lean), in `readsAtLoc`'s
letters, at any parameters at which the eight blocks are made; that the shared chain of the
description that `ProofFile.onlineDescription` returns holds these blocks, at these parameters with the list
`beforePointOf N`, each under one wrapper (`retype`), is `Desc.K14.Law.k14_sits`
(Johnson/Desc/K14/Law/K14Sits.lean), under the premise that these blocks are made; no theorem of
this file says it. Nothing on what the column holds (Johnson/Bind/ForProver/LawsSizes.lean). Where
`rowsFit` fails `encW` gives nothing, and `encW_width` says nothing. This file writes no honest
prover. No completeness, no index privacy; nothing on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.Enc
import Johnson.Bind.Column
import Johnson.Desc.K14.Blocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open ProofFile.Honest (TableRand Weights)

/-- What the round "LOC" declares for the committed table, at the parameters off the public part. -/
def declaredAt (Z : ProofFile.Pub) (l : List (ℕ × ℕ)) : Fmt.Stored :=
  Desc.K14.readsAtLoc (Desc.K14.p14Of Z.p.chains l).S.fold (Desc.K14.p14Of Z.p.chains l).item

/-- Depth, width, salt's length and item are those of the shape off the public part. -/
theorem declared_shape (Z : ProofFile.Pub) (l : List (ℕ × ℕ)) :
    (declaredAt Z l).sh.a = (shapeOf Z).a ∧ (declaredAt Z l).sh.W = 2 ^ (shapeOf Z).v ∧
      (declaredAt Z l).salt = (shapeOf Z).sigma ∧ (declaredAt Z l).item = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Whatever column `encW` gives at the item 0 has the declared width.** -/
theorem encW_width (Z : ProofFile.Pub) (l : List (ℕ × ℕ)) (w : Weights) (rc : ℕ → TableRand) (x : ℕ)
    (col : List Cb.Gl.F) (h : encW Z w rc 0 x = some col) :
    col.length = (declaredAt Z l).sh.W := by
  rw [(declared_shape Z l).2.1]
  unfold encW at h
  split at h
  · unfold encAt at h
    split at h
    · rw [← Option.some.inj h, List.length_map, Bind.Column.length_columnOf]
    · cases h
  · cases h

/-- Where the test passes, there is a column at every position below 2^a. -/
theorem encW_some (Z : ProofFile.Pub) (l : List (ℕ × ℕ)) (w : Weights) (rc : ℕ → TableRand) (x : ℕ)
    (hr : rowsFit (shapeOf Z) (linOf Z).kLo (linOf Z).matrixRows = true)
    (hx : x < 2 ^ (declaredAt Z l).sh.a) : (encW Z w rc 0 x).isSome = true := by
  rw [(declared_shape Z l).1] at hx
  unfold encW encAt
  rw [if_pos ⟨rfl, hr⟩, if_pos hx, Option.isSome_some]

end Bind.ForProver

#print axioms Bind.ForProver.declared_shape
#print axioms Bind.ForProver.encW_width
#print axioms Bind.ForProver.encW_some
#print axioms Bind.ForProver.declaredAt
