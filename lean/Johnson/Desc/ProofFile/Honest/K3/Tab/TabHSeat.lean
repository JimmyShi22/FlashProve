-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Tab/TabHSeat.lean:
the reader of the head's keys and bits that makes the tables once. Definitions with code.

Terms. Honest/K3/GLOSSARY.md; Honest/K3/Tab/TabH.lean.

What is defined.
  `ownHF`: the text of `ownH` (Honest/K3/WitOwner.lean) without the lift: the cell in the base
    field. The tie: `ownH_lift` (Honest/K3/Tab/TabHLaw.lean).
  `headTab`: the reader: of the public part, the head's public data, the cells and the weights: the
    text of the field `head` of `ownSourcesBound` (Honest/K3/WitBound.lean) with the key exchanged:
    the four arrays are bound in front of the structure; a call's key is `kvHBy` in the base field
    off the rows, at `colTabH`, lifted once.

How it is meant. The head's public data comes in as an argument: whoever calls `headTab` makes it
once. Each array is bound by a let in front of the structure that one application returns.

Imported. Honest/K3/Tab/TabH.lean, Honest/K3/Tab/RingG.lean (`atOwnF`).

Users. Honest/K3/Tab/TabHLaw.lean and Honest/K3/Tab/TabAll2.lean import this file.

Limits. Nothing says how long anything takes. The equations are in Honest/K3/Tab/TabHLaw.lean.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Tab.TabH
import Johnson.Desc.ProofFile.Honest.K3.Tab.RingG

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.TabH
open OnBytes.Model OnBytes.Ends.H

/-- `ownH` without the lift. -/
def ownHF (X : OnBytes.Model.Verify.Public) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F)
    (entry : ℕ → ℕ → Cb.Gl.F) (link : ℕ) : NameH → Cb.Gl.F
  | .cell a r c => TabG.atOwnF X cell link a r c
  | .w r c => entry r c

/-- **The reader of the head's keys and bits that makes the tables once.** -/
def headTab (X : OnBytes.Model.Verify.Public) (P : PubH) (C : Cells) (W : Weights) : LookIn :=
  let cE := ownH X C.cell W.entry (linkH X)
  let cF := ownHF X C.cell W.entry (linkH X)
  let t1 := nrTab P cF
  let t2 := whTab P cF
  let t3 := lwTab P cF t1 t2
  let t4 := colTabH P
  let I := innerTabH P cF t1 t2 t3
  ⟨fun theta n =>
      OnBytes.Ends.jointKey P.L.fs
        (fun q i => algebraMap Cb.Gl.F Cb.Gl.E (kvHBy P cF I (Memo.read2 t4 (colH P.L)) q i))
        theta n,
   fun u j => bitsH P.h P.L.fs cE (u * 32 + j)⟩

end ProofFile.Honest.K3.TabH
