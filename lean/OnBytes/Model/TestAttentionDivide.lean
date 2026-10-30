-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestAttentionDivide.lean: tests of OnBytes/Model/AttentionDivide.lean: the sums over
tiles, the three tests at the head of divide, and the term of a pair in keyTerm.

The tests run when this file is compiled. The program does not import this file.

Each of the three sections below begins with its own account: what is tried, and where the expected
values come from.

Not tested: the weights of the six sumchecks. OnBytes/Model/TestAttentionHonest.lean compares what
follows from them on one honest proof. keyTerm is tried for pair 0 of one layer only. No guard has
the inner point of ix as the only one that is too short. That the three tests at the head of divide
cannot fail at a shape that the function shape returns is not proved.
-/
import OnBytes.Model.AttentionDivide
import OnBytes.Model.TestAttentionOwn

namespace OnBytes.Attention

/-! ## The sums over tiles

The sums over tiles (tileSums, overTileRows, scaled). The shape has four tiles along a side, so two
slot rows with three tile slots that hold a tile. The six tiles below the diagonal are numbered
thus, as (slot row, tile slot) -> (tile row, tile column):
  (0, 0) -> (3, 0)   (0, 1) -> (3, 1)   (0, 2) -> (3, 2)
  (1, 0) -> (1, 0)   (1, 1) -> (2, 0)   (1, 2) -> (2, 1)
The expected values were computed by hand from this list.
-/

/-- A shape of which only the numbers of tiles are set: four along a side. -/
def fourTiles : Shape := { nT := 4, hP := 2 }

/-- Small numbers as elements of the extension field. -/
def smallE (l : List UInt64) : Array E := (l.map ofF).toArray

/-- The sum over all tiles of the tile's weight times eI at its tile row, and the weights of the
tile columns. -/
def tileWeights (eP es eI : Array E) : E × Array E :=
  let w := tileSums fourTiles eP es
  (overTileRows fourTiles w.1 eI, w.2)

-- With all weights 1, tile row I counts its I tiles, and tile column J counts its 3 - J tiles.
#guard tileWeights (smallE [1, 1]) (smallE [1, 1, 1, 1]) (smallE [1, 10, 100, 1000]) ==
  (ofF 3210, smallE [3, 2, 1, 0])

-- The products of the two weights are 10, 14, 22 in row 3, then 15 in row 1, then 21, 33 in row 2.
#guard tileWeights (smallE [2, 3]) (smallE [5, 7, 11, 13]) (smallE [1, 10, 100, 1000]) ==
  (ofF 51550, smallE [46, 47, 22, 0])

#guard scaled (smallE [1, 2, 3]) (ofF 5) == smallE [5, 10, 15]

/-! ## The tests at the head of divide

The three tests at the head of divide are not meant to fail at a shape that the function shape
returns (this is not proved): that each of the segments wl, ix and wh is held by a call, that each
has as many pieces as there are pairs, and that each inner point has the length that its cut needs.
Here the own part of the check (OnBytes/Model/TestAttentionOwn.lean) is run dry at the small
configuration of OnBytes/Model/TestAttentionPlan.lean, once as it is, and then with a segment
removed from every call's list, with one piece taken away, or with one key point cut short. The
guards compare the name under which the dry run is refused: internal-af-calls for the first two
tests, and the general name refused for a point that is too short, since that test has no name of
its own. Without the first test the run would fail too, but under the general name. The inner point
of ix is never the only one that is too short: at that configuration ix shares its call with wl,
whose inner point is longer.
-/

/-- True if the dry run of the own part goes through at the small configuration, under the entries
of its plan, after f has changed the shape and z the calls' key points. False for a failure at any
test and under any name. -/
def ownPasses (f : Shape → Shape) (z : Array (Array E) → Array (Array E)) : Option Bool := do
  let P ← smallPlan.toOption
  let planned ← (Params.finish {} .request (Params.planAttentionOwn P.own)).toOption
  let block : Blk Nat :=
    (TestOwn.own (f P.S) (z (TestOwn.zeroPoints P.S))).run' (({} : Model.Fork).slots 502)
  pure (Blk.dryRun block { entries := planned.rounds.map (·.entry), st := {} }).isSome

/-- The shape without the piece of segment s for the pair (0, 0). -/
def without (s : Seg) (S : Shape) : Shape :=
  { S with calls := S.calls.map fun c =>
      { c with pcs := c.pcs.filter fun p => !(p.seg == s && p.lam == 0 && p.a == 0) } }

/-- The key points with that of call number q cut to its first n coordinates. -/
def cutPoint (q n : Nat) (zk : Array (Array E)) : Array (Array E) :=
  zk.modify q fun z => z.extract 0 n

#guard ownPasses id id == some true
-- The calls are KR, KFD, R16, WH. R16 holds wl, whose inner point has 15 coordinates. WH holds wh,
-- whose inner point has 14. A key point of just that length passes.
#guard ownPasses id (cutPoint 2 15) == some true
#guard ownPasses id (cutPoint 3 14) == some true

/-- The name under which the same dry run is refused; no name if the block goes through. -/
def ownRefusal (f : Shape → Shape) (z : Array (Array E) → Array (Array E)) :
    Option (Option String) := do
  let P ← smallPlan.toOption
  let planned ← (Params.finish {} .request (Params.planAttentionOwn P.own)).toOption
  let block : Blk Nat :=
    (TestOwn.own (f P.S) (z (TestOwn.zeroPoints P.S))).run' (({} : Model.Fork).slots 502)
  match block.runNamed { entries := planned.rounds.map (·.entry), st := {} } true [] [] with
  | .ok _ => pure none
  | .error e => pure (some e.name)

/-- The shape in which no call holds the segment s. -/
def unheld (s : Seg) (S : Shape) : Shape :=
  { S with calls := S.calls.map fun c => { c with segs := c.segs.filter (· != s) } }

#guard ownRefusal id id == some none
-- no call holds the segment
#guard ownRefusal (unheld .wl) id == some (some "internal-af-calls")
#guard ownRefusal (unheld .ix) id == some (some "internal-af-calls")
#guard ownRefusal (unheld .wh) id == some (some "internal-af-calls")
-- a segment lacks one piece
#guard ownRefusal (without .wl) id == some (some "internal-af-calls")
#guard ownRefusal (without .ix) id == some (some "internal-af-calls")
#guard ownRefusal (without .wh) id == some (some "internal-af-calls")
-- a key point is one coordinate too short
#guard ownRefusal id (cutPoint 2 14) == some (some "refused")
#guard ownRefusal id (cutPoint 3 13) == some (some "refused")

/-! ## The term of a pair at an odd number of bits

The term of a pair in the summand of the sumcheck for the key at the index (keyTerm) is a product
over the lt bits of the index. The small configuration has an even lt, where a change of sign in
every factor would not show. Here the term is computed at lt = 3 and lt = 1, on small numbers, and
compared with the value worked out by hand from the C++ source (verifier/src/vf_attention_check.h,
the part numbered 7 in the comments of run, on the row maximum): w times the key value times the
product over k of v_k (2 y_k - 1) + (1 - y_k), with y_k coordinate lt - 1 - k of the point. It is
tried for pair 0 of one layer only.
-/

/-- keyTerm for pair 0 of a shape with one layer and one pair, of which only lt is set otherwise,
with w = 2. What was shown is 3 for the key value, under slot 0, and then v for the bits of the
index. pj is the point's part for the key's token. -/
def termAt (lt : Nat) (v pj : List UInt64) : Option E := do
  let S : Shape := { cf := { lt := lt }, HA := 1, Lam := 1 }
  let F ← (({} : Model.Fork).slots (1 + lt)).hideRun 0 (smallE (3 :: v)) zeroE
  let block : Blk E := (keyTerm S 0 (smallE pj) (ofF 2) 0).run' F
  (Blk.dryRun block { entries := [], st := {} }).map (·.2)

-- Bit 0 goes with the last coordinate. The factors are 5 (2 19 - 1) + (1 - 19) = 167,
-- 7 (2 17 - 1) + (1 - 17) = 215 and 11 (2 13 - 1) + (1 - 13) = 263, and 2 3 167 215 263 = 56658090.
#guard termAt 3 [5, 7, 11] [13, 17, 19] == some (ofF 56658090)
-- 2 3 (5 (2 13 - 1) + (1 - 13)) = 6 113 = 678
#guard termAt 1 [5] [13] == some (ofF 678)

end OnBytes.Attention
