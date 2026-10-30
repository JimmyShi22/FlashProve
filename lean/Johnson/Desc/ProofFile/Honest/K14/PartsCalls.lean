-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/PartsCalls.lean: kind K14: THE KIND's FOUR OWN ROWS ARE CALLS OF
THE FRAME's OWN TWO SMALL PARTS (Honest/ForKinds.lean), AT THE SHARED CHAIN's TYPE PARAMETERS TOO:
lifted, a quiet part is quietPart and the part at "SPLIT" is scalarsPart at one scalar. So whatever
is shown of these two parts beside quietSim and scalarsSim, general in the caller, holds of the
kind's rows by one rewrite. And of the structure Good (Honest/Side.lean) the field fits at the four
rows, in the field's own form, at a side whose sub-protocol stands at the kind's place, declares one
round and states one list of oracle messages; the kind's On and bud, which ask nothing.

  lift_quiet      the lifted quiet part is the frame's quietPart
  lift_split      the lifted part at "SPLIT" is the frame's scalarsPart, at the run's name, one
                  scalar, and the value splitValue off the rows that the reader of the index makes
  quietRow, splitRow   the four rows, each part with the frame's simulator beside it
  k14On, k14Bud, k14_bud   they ask nothing; so k14Bud holds everywhere
  fits_quiet, fits_split   **the field fits**, under the three premises on the side's sub-protocol
                  (hp, hr, ho): the row has one move for the sub-protocol's one round; the
                  simulator names its part's address

THIS FILE STATES NOTHING OVER A DISTRIBUTION; other files of the kind do (for example
Honest/K14/ExactSend.lean, Honest/K14/MaskLaw.lean). The fields exact and fresh at these four rows
are had by calling the laws on the frame's two parts: exact_quiet, exact_split, fresh_quiet and
fresh_split, Honest/K14/GoodCalls.lean, each under premises on the side's sub-protocol, the two on
fresh also under a test on the book; that file calls the laws in their lifted form, and no file
of the kind uses lift_quiet, lift_split or k14_bud. The two sendings are written as calls of the
shared sending's part in Honest/K14/SendingsVia.lean (definitions alone); of the sendings' fields
nothing is said here.

What is not claimed. The structure Good at any row (as one term, with its fields plays and acc held
from a false premise: good_rows, Honest/K14/GoodSeated.lean). Nothing on what is or is not hidden;
no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.PartsPlay
import Johnson.Desc.ProofFile.Honest.Side

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Place)

variable {S Cl V W X Pb W₀ Rc Ky : Type}

/-- The lifted quiet part is the frame's quietPart. -/
theorem lift_quiet (A : Data) (weights : W₀ → Weights) :
    (liftK14 A weights quietPart : Part Empty (Common W₀ Rc Ky) X) = quietPart := rfl

/-- The lifted part at "SPLIT" is the frame's scalarsPart at one scalar. -/
theorem lift_split (A : Data) (weights : W₀ → Weights) :
    (liftK14 A weights (splitPart A) : Part Empty (Common W₀ Rc Ky) X) =
      scalarsPart splitRun 1 fun c fr =>
        [splitValue A { rows := entriesOf A.S (weights c.w₀) } fr.heard] := rfl

/-- A quiet row, at the piece i of the shared chain. -/
def quietRow (A : Data) (weights : W₀ → Weights) (i : Nat) :
    List (Part Empty (Common W₀ Rc Ky) X × Sim Pb) :=
  [(liftK14 A weights quietPart, quietSim { place := place i, part := 0 })]

/-- The row at "SPLIT". -/
def splitRow (A : Data) (weights : W₀ → Weights) :
    List (Part Empty (Common W₀ Rc Ky) X × Sim Pb) :=
  [(liftK14 A weights (splitPart A), splitSim)]

/-- The kind's On: it asks nothing. -/
def k14On (u : Member V W X Pb) (_ : CsAll u.part.carries) (_ : Mid W X) (_ : Before) : Prop := True

/-- The kind's bud: it asks nothing. -/
def k14Bud (_ : Nat) (_ : List Fmt.Drawn) (_ : List (List (List Nat))) : Prop := True

/-- It holds at every number, all challenges and all lists of positions. -/
theorem k14_bud (n : Nat) (ds : List Fmt.Drawn) (asks : List (List (List Nat))) :
    k14Bud n ds asks := trivial

/-- **The field fits at a quiet row**, beside a sub-protocol at the kind's place that declares one
round and states one list of oracle messages. -/
theorem fits_quiet (A : Data) (weights : W₀ → Weights) (i : Nat)
    (σ : Side S Cl Empty (Common W₀ Rc Ky) X Pb) (hrow : σ.row = quietRow A weights i)
    (hp : σ.block.place = place i) (hr : σ.block.rounds.length = 1)
    (ho : σ.block.oracles.length = 1) : σ.fits = true := by
  unfold Side.fits Side.half
  rw [hrow, hp, hr, ho]
  simp [quietRow, quietSim, Placed.rounds, liftK14, Part.lift, quietPart]

/-- **The field fits at the row of "SPLIT"**, the like. -/
theorem fits_split (A : Data) (weights : W₀ → Weights)
    (σ : Side S Cl Empty (Common W₀ Rc Ky) X Pb) (hrow : σ.row = splitRow A weights)
    (hp : σ.block.place = place 8) (hr : σ.block.rounds.length = 1)
    (ho : σ.block.oracles.length = 1) : σ.fits = true := by
  unfold Side.fits Side.half
  rw [hrow, hp, hr, ho]
  simp [splitRow, splitSim, scalarsSim, Placed.rounds, liftK14, Part.lift, splitPart, scalarsPart]

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.lift_quiet
#print axioms ProofFile.Honest.K14.lift_split
#print axioms ProofFile.Honest.K14.k14_bud
#print axioms ProofFile.Honest.K14.fits_quiet
#print axioms ProofFile.Honest.K14.fits_split
