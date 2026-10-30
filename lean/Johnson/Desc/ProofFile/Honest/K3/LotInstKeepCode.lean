-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/LotInstKeepCode.lean: the lookups' lot's honest side at rows that
pass their tables on (`theLotKeep`, `theLotInstKeep`, Honest/K3/LotInstKeep.lean) with the table's
rows filled: in closed form, of each site's shape (`Fast.rowCode`, Honest/K3/RowCode.lean); and the
seated row at a site, as these lots lay it. Definitions with code; no theorem.

Terms. Honest/K3/GLOSSARY.md. In this file: a row's own state is a value of `RowOwn`
(Honest/K3/KeptTypes.lean).

Why. `theLotInstFast` (Honest/K3/LotInstFast.lean) reads the table's rows off the verifier's face
(`Fast.rowOfFace`), which evaluates every call's table as a multilinear extension for each row anew
(Honest/K3/RowCode.lean, under "Why"; one measurement: Honest/K3/RowKeepFill.lean, under "Limits").

What is defined.
  `codeRows`: the letter row of `theLotKeep`: at each site `Fast.rowCode` at the site's shape. It
    does not read the public part.
  `theLotKeepCode cells weights req get set`, `theLotInstKeepCode cells weights get set`: the two
    lots at these rows. The letters that are left are those of `theLotFast` and `theLotInstFast`,
    and get and set: how the row's own state is read in what the chain's parts pass on, and how it
    is laid there.
  `seatKeepAt row cells weights req get set Z s`: the seated row at a site, as `theLotKeep` lays it:
    general in the rows. That the halves of `theLotKeep` are these, site by site:
    `theLotKeep_halves` (Honest/K3/Law/Keep/LotInstKeepLaw.lean [not in this library]; by `rfl`).

Imported. Honest/K3/LotInstKeep.lean, Honest/K3/RowCode.lean. Beneath the first lie the frame's
files, Honest/SumKeep.lean among them.

Users. Honest/K3/Law/Keep/LotInstKeepLaw.lean [not in this library]; Honest/K3/LotInstKeepAtZ7.lean
[not in this library] (numbers); Honest/K3/LotInstKeepBound.lean; Honest/K3/Law/Keep/LotsSame.lean
[not in this library]. Meant for a filling of the honest prover whose state has a field of the type
`RowOwn`: get reads that field and set lays it.

Limits. In the place of `theLotFast` or `theLotInstFast`, never beside them: all bear the one lot's
name. Nothing here says that these lots send what `theLotInstFast` sends, nor that `Fast.rowCode` is
the verifier's table (Honest/K3/FastLaw/RowCodeLaw.lean [not in this library]). Nothing asks that
get and set fit each other, nor that a row begins at `rowOwn₀` in a run. How long a move takes is
not said and has not been measured here. Nothing is evaluated in this file.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.LotInstKeep
import Johnson.Desc.ProofFile.Honest.K3.RowCode

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E)

variable {X : Type} {W₀ Rc Xi Tr : Type}

/-- The table's rows at each site: in closed form, of the site's shape. -/
def codeRows : Pub → Site → E → Nat → E := fun _ s => Fast.rowCode s.shape

/-- **The lot's honest side at rows that pass their tables on, the table's rows in closed form**, at
a letter for the reader of the instance. In the place of `theLotFast`, never beside it. -/
def theLotKeepCode (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (get : X → RowOwn)
    (set : X → RowOwn → X) : HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  theLotKeep codeRows cells weights req get set

/-- **The same at the proof file's own instance.** In the place of `theLotInstFast`, never beside
it. -/
def theLotInstKeepCode (cells : Tr → Cells) (weights : W₀ → Weights) (get : X → RowOwn)
    (set : X → RowOwn → X) : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X :=
  theLotInstKeep codeRows cells weights get set

/-- The seated row at a site, as `theLotKeep` lays it. -/
def seatKeepAt (row : Pub → Site → E → Nat → E) (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (get : X → RowOwn)
    (set : X → RowOwn → X) (Z : Pub) (s : Site) :
    Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  proverSideOfLookupInChainKeepingTablesAtOneOwner (fastKeeps theReads (row Z s) s.at_) (fastWit cells weights req Z s) get set s.at_

end ProofFile.Honest.K3
