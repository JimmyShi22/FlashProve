-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/TestWf.lean: tests of OnBytes/Iop/Wf.lean on small made-up values.

Every test is checked when the file compiles. The program does not import this file.

The block WF makes one test of its own on values: the weights that a lookup hands on add up to the
sum of the equality vector over the places that the runs cover. Both numbers follow from the same
public runs, so no file can make that test fail. Here the two are made to disagree on purpose: the
claim's weights lie on both places of a part, and the part's runs cover one place alone.
-/
import OnBytes.Iop.Wf

namespace OnBytes.Wf.Test

open OnBytes.Params (WfRun WfPart WfLookup)

/-- A matrix of four rows and two columns. -/
def m : Matrix := ⟨1, 4⟩

/-- Single entries as keys, with the offset 3. The parts are given with each test. -/
def l : WfLookup where
  d := 2
  mu := 2
  live := 3
  digitWeight := [1]
  offset := 3
  paddingKey := 0
  parts := []
  firstBound := []

/-- The column coordinate of the claim's point. -/
def zCol : E := E.mk3 5 6 7
/-- The place coordinate of the claim's point. -/
def zPlace : E := E.mk3 11 12 13

/-- A claim on a part of two places without padding: the weights are the whole equality vector. -/
def claim : Lkp.Keys where
  point := [zCol, zPlace]
  weights := Form.ofTensor (Tensor.eq [zCol, zPlace])
  masks := [(⟨0, 4⟩, ofF 2), (⟨0, 5⟩, ofF 9)]
  target := E.mk3 100 200 300

/-- Both places are covered: they read the rows 1 and 2. -/
def whole : WfPart := ⟨1, [⟨0, 1, 2, 0⟩]⟩
/-- Place 0 alone is covered. -/
def half : WfPart := ⟨1, [⟨0, 1, 1, 0⟩]⟩

/-- A chain without rounds, to run a block that receives nothing. -/
def start : Start := { entries := [], st := {} }

/-- The block's value on a view without rounds; nothing if it refuses. -/
def onView (p : WfPart) : Option (List TensorRow) :=
  ((pendingOf m l [p] [claim] []).walk start [] []).map (·.1)

/-- The weight that a row gives to row j of the matrix. -/
def weightAt (r : TensorRow) (j : Nat) : E := r.g.foldl (fun s t => addE s (t.entry j)) zeroE

-- all weights of the equality vector add up to 1, and so does its sum over both places
#guard sumOfForm claim.weights == oneE
#guard coveredSum whole (eqPlaces m claim.point) == oneE
#guard coveredSum half (eqPlaces m claim.point) == subE oneE zPlace

-- the two descriptions agree: the block goes through, on a view and in the dry run
#guard (onView whole).isSome
#guard ((pendingOf m l [whole] [claim] []).dryRun start).isSome
-- THE TWO DISAGREE: refused on a view; the dry run does not compute the test
#guard (onView half).isNone
#guard ((pendingOf m l [half] [claim] []).dryRun start).isSome
-- a point of another length, and another number of claims than parts, are refused in both
#guard ((pendingOf m l [⟨2, [⟨0, 0, 4, 0⟩]⟩] [claim] []).dryRun start).isNone
#guard ((pendingOf m l [whole, whole] [claim] []).dryRun start).isNone
#guard ((pendingOf m l [] [claim] []).dryRun start).isNone

-- the pending row: the column point, the masks, the target less offset times the covered sum
#guard (onView whole).map (fun r => r.map (·.psi)) == some [[zCol]]
#guard (onView whole).map (fun r => r.map (·.masks)) == some [claim.masks]
#guard (onView whole).map (fun r => r.map (·.target)) == some [subE claim.target (ofF 3)]
-- its weights: the rows 1 and 2 have the equality vector's two entries, the rows 0 and 3 nothing
#guard (onView whole).map (fun r => r.map fun x => (List.range 4).map (weightAt x)) ==
  some [[zeroE, subE oneE zPlace, zPlace, zeroE]]
-- the dry run's row has the same public shape
#guard ((dryRow m claim).psi.length, (dryRow m claim).g.map (·.vars), (dryRow m claim).masks) ==
  (1, [2], claim.masks)

/-- Values to lay on rows. -/
def values : Array E := #[ofF 1, ofF 2, ofF 3, ofF 4, ofF 5]

/-- The weights on eight rows, written out. -/
def written (g : List Tensor) : List E :=
  (List.range 8).map fun j => g.foldl (fun s t => addE s (t.entry j)) zeroE

-- an aligned stretch is one block; the values are read from `first` on, under the factor
#guard (weightsOnRows 3 4 values 1 4 (ofF 10)).length == 1
#guard written (weightsOnRows 3 4 values 1 4 (ofF 10)) ==
  [zeroE, zeroE, zeroE, zeroE, ofF 20, ofF 30, ofF 40, ofF 50]
-- a stretch from row 1 to row 5 is cut into the blocks 1, 2-3, 4-5
#guard (weightsOnRows 3 1 values 0 5 oneE).length == 3
#guard written (weightsOnRows 3 1 values 0 5 oneE) ==
  [zeroE, ofF 1, ofF 2, ofF 3, ofF 4, ofF 5, zeroE, zeroE]
-- no row: no weight
#guard (weightsOnRows 3 2 values 0 0 oneE).isEmpty

-- what the lookup is told: a place is 2^kCol key numbers; the padding is what the runs leave
#guard (lookupOf 1 m { l with parts := [⟨2, [⟨1, 0, 1, 0⟩]⟩, whole] }).parts == [3, 2]
#guard (lookupOf 1 m { l with parts := [⟨2, [⟨1, 0, 1, 0⟩]⟩, whole] }).padding ==
  [⟨0, 0, 0, 2, 0⟩, ⟨0, 4, 0, 4, 0⟩]

end OnBytes.Wf.Test
