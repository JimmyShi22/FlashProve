-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/TreeProps.lean: FOUR CLOSED PROPOSITIONS ON THE TREES OF THE KEY FILE's
WRITTEN SENDINGS, EACH WITH A NAME. Definitions alone.
  `treesA`, `treesB`, `treesC`: the three chains' trees at the written sendings (`treesOf`,
    TreesKOfRounds.lean; `masksB`, FitsB.lean).
  `FirstA`, `FoldedB`, `OmegaB`, `OwnAB`: which trees the first opening reads at the place of the
    ranges' test, of the test on the folded row's group (U), of the test on Omega's group (O) and of
    the own test (W): the left sides are the routines' own expressions (RangesReturns.lean,
    LaterReturns.lean), the right sides the lists that stand in Johnson/HB/LLHARD/KB8/Written.lean.
Limits. No theorem is here: a definition of a proposition says nothing on whether it holds.

-/
import Johnson.AtFull.KeyBack.RangesReturns
import Johnson.AtFull.KeyBack.LaterReturns
import Johnson.AtFull.KeyBack.FitsB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G (ChainSends keySends0 keySends1 keySends2)
open Johnson.G.OfPlan
open VerifiableInference.Desc.Key
open Lk6.AtPlan (keyFull)

/-- The first chain's trees at the written sendings. -/
abbrev treesA : List (Sent × Nat) := treesOf keySends0 1 []

/-- The shared chain's. -/
abbrev treesB : List (Sent × Nat) := treesOf keySends1 0 masksB

/-- The second chain's. -/
abbrev treesC : List (Sent × Nat) := treesOf keySends2 0 []

/-- What the first opening of the ranges' test reads. -/
def FirstA : Prop := rangesFirst treesA = [(⟨22, 77, false, 1⟩, .own 1)]

/-- What the first opening of the test on the folded row's group reads. -/
def FoldedB : Prop :=
  foldedFirst keyFull.once.shape treesB =
    [(⟨24, 324, false, 0⟩, .own 0), (⟨13, 3, false, 2⟩, .own 2)]

/-- What the first opening of the test on Omega's group reads. -/
def OmegaB : Prop :=
  ((sharedOpens keyFull.once.shape treesB)[2 + (switchOpens 0 .folded treesB).length]?).map
      (fun x => (x.1.dropLast, 0)) =
    some ([(⟨22, 36, false, 1⟩, .own 1), (⟨13, 3, false, 2⟩, .own 2)], 0)

/-- What the first opening of the own test reads. -/
def OwnAB : Prop :=
  ownFirst keyFull.once.shape treesA treesB =
    [(⟨13, 3, false, 0⟩, .taken 0 0), (⟨22, 12, false, 5⟩, .taken 0 5),
      (⟨22, 36, false, 1⟩, .taken 1 1)]

end Johnson.AtFull.KeyBack
