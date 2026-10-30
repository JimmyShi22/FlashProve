-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestFrame.lean: tests of OnBytes/Model/Frame.lean and OnBytes/Model/Rounds.lean, which
run when this file is compiled.

The first four sections check the helpers of both files on a few values. The last section runs a
small block that uses each of the ten functions through which a check reads the chain (trRead to
trTrits, Rounds.lean), once as a dry run and once on a hand-written view. Then it runs that block on
three faulty views, and blocks with one fault each. These blocks must fail in the dry run already,
except those with a wrong number of rows, which fail on a view. OnBytes/Iop/Ground.lean explains
block, dry run, view, chain and plan; the head of Rounds.lean says what the channel is.

What this file does not claim. The expected values were worked out by hand, except the known first
output of SplitMix64. The tests compare nothing with the C++ verifier. Where a block must fail, the
guard sees only that the run fails, not under which name. OnBytes/Model/TestRoundsMore.lean checks
the names of the failures in the dry run, and no name of a failure on a view. No program imports
this file.
-/
import OnBytes.Model.Rounds

namespace OnBytes.Model.TestFrame

/-! ## Numbers -/

#guard fOfInt 0 == 0 && fOfInt 5 == 5 && fOfInt (-1) == 0xFFFFFFFF00000000
#guard fOfInt (-18446744069414584321) == 0 && fOfInt 18446744069414584322 == 1
#guard fOfNat 18446744069414584321 == 0 && ofNat 7 == E.mk3 7 0 0 && ofInt (-2) == negE (ofNat 2)
#guard scaleNat (E.mk3 1 2 3) 5 == E.mk3 5 10 15
#guard powers (ofNat 3) 4 == #[ofNat 1, ofNat 3, ofNat 9, ofNat 27] && powers (ofNat 3) 0 == #[]
#guard [0, 1, 2, 3, 4, 5, 8, 9].map clog2 == [0, 0, 1, 2, 2, 3, 3, 4]
-- the first output of SplitMix64 from the seed 0
#guard mix64 0 == 0xE220A8397B1DCDAF
#guard roundUp 0 8 == 0 && roundUp 1 8 == 8 && roundUp 8 8 == 8 && roundUp 9 8 == 16

/-! ## The equality polynomial -/

/-- A point with three coordinates. -/
def point : Array E := #[ofNat 2, ofNat 3, E.mk3 5 1 0]

#guard eqTab #[] == #[oneE]
#guard eqTab #[ofNat 2] == #[ofInt (-1), ofNat 2]
-- coordinate 0 belongs to the top bit of the index
#guard (eqTab #[ofNat 1, ofNat 0]) == #[zeroE, zeroE, oneE, zeroE]
#guard (eqTab point).size == 8
#guard (List.range 8).all fun c => eqOne point c == (eqTab point).getD c zeroE
#guard (eqTab point).foldl addE zeroE == oneE
#guard eqIndexOK point 7 && !eqIndexOK point 8 && eqOne point 8 == zeroE

/-! ## Orders, calls, numbers of a run -/

#guard orderDefault 4 == [3, 2, 1, 0] && orderDefault 0 == []
#guard orderRange 12 == [2, 1, 0, 5, 4, 3, 8, 7, 6, 11, 10, 9]
#guard orderRange 9 == [2, 1, 0, 5, 4, 3, 8, 7, 6]

/-- A call with an explicit table. -/
def call : Call :=
  { name := "X", n := 12, iota := 2, k := 5, kappa := 5, fn := 1, t0 := 3,
    tau := some #[9, 8, 7], heavy := [[(1, 4), (2, 6)], []] }

#guard call.tauAt 1 == 8 && call.tauAt 3 == 0 && ({ call with tau := none } : Call).tauAt 3 == 3
#guard ({ mats := #[{ k := 3 }, { k := 4 }] } : Tail).foldColumns == 7
#guard ({} : Settings).lidb == 22 && ({} : Settings).tau == 160 && bar == 128

/-! ## The rounds of a sumcheck -/

#guard roundValues .eq2 == 2 && roundValues .sum2 == 2 && roundValues .sum3 == 3
#guard roundValues .nodes 5 == 5 && roundValues .eq 1 == 1
#guard sumcheckSlots .sum3 4 2 1 == 16 && sumcheckSlots .nodes 2 0 0 7 == 15
#guard sumcheckSlotsDegrees [3, 1, 2] 2 1 == 10 && layerSlots 6 == 17
#guard RoundForm.eq.degreeOK 64 && !RoundForm.eq.degreeOK 65 && !RoundForm.nodes.degreeOK 0
#guard RoundForm.sum3.degreeOK 0 && RoundForm.eq2.equality && !RoundForm.nodes.equality

/-! ## The ten functions on the chain -/

/-- The plan's entries of a small chain. -/
def entries : List Fmt.Entry :=
  [{ name := "PSC epsilon", msg := 48, drawE := 1 }, { name := "PSC round", msg := 48, drawE := 1 },
   { name := "BAT-sigma", drawE := 1, rows := 3 }, { name := "RNG", trits := 6 },
   { name := "PSC values", msg := 24 }, { name := "PSC Y", drawE := 1, drawNZ := 1 },
   { name := "JOIN", drawE := 2 }, { name := "BAT-sigma", drawE := 1, rows := 2 }]

/-- Where a block on these entries starts. -/
def start : Start := { entries := entries, st := {} }

/-- What the small block returns: all that it has received and drawn. -/
structure Received where
  /-- what trRead has taken -/
  read : Array E
  /-- what trSum has taken -/
  sum : E
  /-- the draw of the round pscEpsilon -/
  eps : E
  /-- the draw of a round of a sumcheck -/
  round : E
  /-- the factors that trBatch has returned -/
  batch : Array E
  /-- the drawn matrix -/
  trits : Array Int
  /-- the draw that is never 0 -/
  y : E
  /-- the drawn point -/
  join : Array E
  /-- the draw of trBatchOpen -/
  sigma : E
  deriving DecidableEq

/-- A block that uses each of the ten functions. -/
def block : Blk Received := do
  let a ← trRead 1
  let sum ← trSum
  let eps ← trAnswer .pscEpsilon
  -- one message that two calls fill
  let b ← trRead 1
  let c ← trRead 1
  let round ← roundDraw
  let batch ← trBatch 3
  let trits ← trTrits 2 3
  let d ← trRead 1
  trEmpty .pscValues
  let y ← trAnswerNotZero .pscY
  let join ← trPoint .forestPoint 2
  let sigma ← trBatchOpen
  trBatchRows 2
  pure ⟨a ++ b ++ c ++ d, sum, eps, round, batch, trits, y, join, sigma⟩

/-- Name, kind and items of each round of a dry run. -/
def shapeOf {α : Type} (b : Blk α) : Option (List (String × Nat × List Fmt.Item)) :=
  (b.rounds start).map fun l => l.map fun r => (r.1.entry.name, r.1.kind.num, r.1.items)

#guard shapeOf block == some
  [("PSC epsilon", 2, [.e, .e]), ("PSC round", 1, [.e, .e]), ("BAT-sigma", 1, []), ("RNG", 5, []),
   ("PSC values", 7, [.e]), ("PSC Y", 1, []), ("JOIN", 1, []), ("BAT-sigma", 1, [])]

/-- What a round draws, from its elements and matrix entries. -/
def drawn (elems : List E) (trits : List Int := []) : Fmt.Drawn :=
  { elems := elems.map E.triple, poss := [], trits := trits, digest := none }

/-- A hand-written view of the small chain. -/
def view : List Fmt.RoundView :=
  [⟨[.e (ofNat 1).triple, .e (ofNat 2).triple], drawn [ofNat 3]⟩,
   ⟨[.e (ofNat 4).triple, .e (ofNat 5).triple], drawn [ofNat 6]⟩,
   ⟨[], drawn [ofNat 7]⟩, ⟨[], drawn [] [1, 0, -1, 0, 0, 1]⟩,
   ⟨[.e (ofNat 8).triple], drawn []⟩, ⟨[], drawn [ofNat 9]⟩,
   ⟨[], drawn [ofNat 10, ofNat 11]⟩, ⟨[], drawn [ofNat 12]⟩]

#guard ((block.walk start []) view).map (·.1) == some
  ⟨#[ofNat 1, ofNat 4, ofNat 5, ofNat 8], ofNat 2, ofNat 3, ofNat 6,
   #[ofNat 1, ofNat 7, ofNat 49], #[1, 0, -1, 0, 0, 1], ofNat 9, #[ofNat 10, ofNat 11], ofNat 12⟩
#guard ((block.walk start []) view).map (·.2.length) == some 0
-- an item too few, an item too many, a round too few
#guard ((block.walk start []) (⟨[.e (ofNat 1).triple], drawn [ofNat 3]⟩ :: view.drop 1)).isNone
#guard ((block.walk start [])
  (⟨[.e (ofNat 1).triple, .e (ofNat 2).triple, .e (ofNat 2).triple], drawn [ofNat 3]⟩ ::
    view.drop 1)).isNone
#guard ((block.walk start []) view.dropLast).isNone

/-- True if the block fails in the dry run on the given entries. -/
def fails {α : Type} (b : Blk α) (entries : List Fmt.Entry) : Bool :=
  (b.rounds { entries := entries, st := {} }).isNone

/-- True if the block fails on the given entries and view. -/
def failsOn {α : Type} (b : Blk α) (entries : List Fmt.Entry) (view : List Fmt.RoundView) : Bool :=
  ((b.walk { entries := entries, st := {} } []) view).isNone

/-- The plan of a chain with the one round that combines three rows. -/
def threeRows : List Fmt.Entry := [{ name := "BAT-sigma", drawE := 1, rows := 3 }]

-- these two pass
#guard !fails (trBatch 3) [{ name := "BAT-sigma", drawE := 1, rows := 3 }]
#guard !fails (trAnswer .line) [{ name := "LINE", drawE := 1 }]
-- no row
#guard fails (trBatch 0) [{ name := "BAT-sigma", drawE := 1, rows := 0 }]
-- a number of rows that differs from the plan's: the channel compares the two on a view
#guard !failsOn (trBatch 3) threeRows [⟨[], drawn [oneE]⟩]
#guard failsOn (trBatch 4) threeRows [⟨[], drawn [oneE]⟩]
#guard failsOn (do let _ ← trBatchOpen; trBatchRows 2) threeRows [⟨[], drawn [oneE]⟩]
-- the number of rows is never stated
#guard fails trBatchOpen [{ name := "BAT-sigma", drawE := 1, rows := 3 }]
#guard fails (do let _ ← trBatchOpen; trAnswer .line)
  [{ name := "BAT-sigma", drawE := 1, rows := 3 }, { name := "LINE", drawE := 1 }]
-- trAnswer and trPoint do not take the round that combines rows
#guard fails (trAnswer .batSigma) [{ name := "BAT-sigma", drawE := 1, rows := 0 }]
#guard fails (trPoint .batSigma 1) [{ name := "BAT-sigma", drawE := 1, rows := 0 }]
-- a name, a number of elements, a rule on 0 that differs from the plan's
#guard fails (trAnswer .line) [{ name := "ZERO", drawE := 1 }]
#guard fails (trAnswer .line) [{ name := "LINE", drawE := 2 }]
#guard fails (trPoint .zero 3) [{ name := "ZERO", drawE := 2 }]
#guard fails (trAnswer .pscY) [{ name := "PSC Y", drawE := 1, drawNZ := 1 }]
#guard fails (trAnswerNotZero .pscY) [{ name := "PSC Y", drawE := 1 }]
-- a number of matrix entries that differs from the plan's
#guard fails (trTrits 2 3) [{ name := "RNG", trits := 5 }]
-- a round of elements is not closed as an empty one
#guard fails (trEmpty .line) [{ name := "LINE" }]
-- a message is left open; an entry is left over
#guard fails (trRead 1) []
#guard fails (trAnswer .line) [{ name := "LINE", drawE := 1 }, { name := "LINE", drawE := 1 }]

end OnBytes.Model.TestFrame
