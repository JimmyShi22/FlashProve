-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/ForestTwins.lean: TWO ROUTINES OF THE LOOKUP's FOREST WITHOUT THE LINES AT WHICH
LEAN's
KERNEL STOPS, EACH ONCE, for closed facts by the kernel. Definitions alone. EACH IS THE ROUTINE's
OWN
TEXT (OnBytes/Model/Forest.lean), COPIED BY PROGRAM, LESS THE LINES NAMED:
  `Forest.shapeNoAsk`: Forest.shape less its first line "for c in calls do callAsk c".
  `Forest.callAskNoTab`: Forest.callAsk less its two tests on a call's written table (its size;
  every
    word below the prime).
Limits. NO PROGRAM CALLS THESE: they stand in statements alone; what ties them to the routines is
Johnson/Unfolds/ShapeEq.lean. Nothing on soundness.
-/
import OnBytes.Model.Forest

set_option autoImplicit false

namespace OnBytes.Model.Forest

/-- Forest.shape's text less its first line. -/
def shapeNoAsk (calls : Array Call) (lid : Nat) : Except String Shape := do
  let NC := calls.size
  if NC < 1 || NC > 16 then throw "forest-calls"
  let cK := clog2 NC
  let dT := calls.foldl (fun m c => min m c.n) lid
  let kT := calls.foldl (fun m c => max m c.k) 0
  if dT < 10 then throw "forest-depth"
  let iota := calls.map fun c => c.n - dT
  let NT := iota.foldl (fun s i => s + 2 ^ i) 0
  if NT > 256 then throw "forest-trees"
  let rK := clog2 NT
  -- A count of 32 bits has room for all keys, and the sum of all counts stays below the prime.
  if dT + rK ≥ 32 then throw "forest-keys"
  if 2 ^ (kT + cK + 32) ≥ pW.toNat then throw "no-wrap-pin-forest"
  let mut first := Array.replicate NC 0
  let mut callOf := Array.replicate NT 0
  let mut free := 0
  let order := byFallingKey NC fun c => iota.getD c 0
  for c in order do
    let trees := 2 ^ iota.getD c 0
    if free % trees != 0 then throw "internal-forest-place"
    first := first.setIfInBounds c free
    for b in List.range trees do
      callOf := callOf.setIfInBounds (free + b) c
    free := free + trees
  if free != NT then throw "internal-forest-place"
  pure { calls, dT, kT, NT, rK, NC, cK, iota, first, callOf }

/-- Forest.callAsk's text less its two tests on the written table. -/
def callAskNoTab (c : Call) : Except String Unit := do
  if c.k < 5 || c.k > 16 || c.fn > 2 || c.t0 ≥ 2 ^ c.k || c.n > 62 then
    throw "shape-pt-words"
  if c.n < 10 then throw "hid-call-floor"
  if c.kappa != 5 || !c.heavy.isEmpty then throw "hid-planes"

end OnBytes.Model.Forest
