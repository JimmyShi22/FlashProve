-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/ShapeOwn.lean: the lookup's numbers and its public tests on them, in the
description's own text.

What it is for: a lookup over several calls has a shape: how many trees of keys, how deep, which
tree belongs to which call. The shape is made of public numbers alone, and it exists only if these
numbers pass a list of tests. Until this file the description took both from the verifier
program's functions, by name. Here each test stands as a clause with its reason beside it.

Main names:
  `bitsFor`, `fallingOrder`: two small functions on numbers.
  `callOk c`: the tests on one call.
  `places NC NT iota`: which trees belong to which call.
  `shapeOwn calls lid`: the shape, or none.
  `pubOk h pub`: the tests on the numbers of padding keys.
  `planesOk h lm`, `planeColsOwn h lm`: the test on the packing of the planes of the counts, and the
    number of columns of the matrix that holds them.
  `phiBOwn g lm e`: the weights under which the planes are read at one of the two points heard.
  `pubRunOwn`, `pubLoopOwn`: a run of padding places counted tree by tree.

Limits: the record types `Call` and `Shape` and the prime `pW` are the verifier program's
(OnBytes/Model/Frame.lean, Forest.lean; OnBytes/Field/Word.lean), and so are the record `Heard`
and the table of equality weights `eqTab` (OnBytes/Model/Look.lean, Frame.lean), which computes
values and refuses nothing: no function of it that can refuse is called. What is proved of these
functions against the program's stands in ShapeOwnAgrees.lean; of `shapeOwn` and `pubOk` nothing is
proved yet: they have been run against `Forest.shape` and `Forest.pubAsk`.
The names of the refusals are not kept: a refusal is none or false. Nothing is said of soundness or
of hiding.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Model.Look

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes
open OnBytes.Model (Call)
open OnBytes.Model.Forest (Shape Heard)

/-- The number of bits that number n things: the least b with n ≤ 2^b. -/
def bitsFor (n : Nat) : Nat := if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

/-- The numbers 0 to count - 1 in descending order of key; numbers with equal keys keep their
order. -/
def fallingOrder (count : Nat) (key : Nat → Nat) : List Nat :=
  let all := List.range count
  let top := all.foldl (fun m i => max m (key i)) 0
  (List.range (top + 1)).reverse.flatMap fun k => all.filter fun i => key i == k

/-- **The tests on one call.** -/
def callOk (c : Call) : Bool :=
  -- the table has from 2^5 to 2^16 rows
  decide (5 ≤ c.k) && decide (c.k ≤ 16) &&
  -- the host's flag is 0, 1 or 2
  decide (c.fn ≤ 2) &&
  -- the row to which padding keys point lies inside the table
  decide (c.t0 < 2 ^ c.k) &&
  -- from 2^10 to 2^62 keys
  decide (10 ≤ c.n) && decide (c.n ≤ 62) &&
  -- a written table has a value for each row, and each value is below the prime: not every
  -- routine reduces a value that it is given
  (c.tau.all fun t => t.size == 2 ^ c.k && t.all fun x => decide (x < pW)) &&
  -- a count has 32 bits, and no row has a count of its own
  c.kappa == 5 && c.heavy.isEmpty

/-- **Which trees belong to which call.** The calls with the most trees come first, so that each
call's trees begin at a multiple of their number. Returns the first tree of each call and the call
of each tree; none unless the trees fill 0 to NT - 1 just so. Where NT is the sum of the numbers
2^iota[c], as in `shapeOwn`, no input is known to trip either test: the numbers are powers of two
in falling order. -/
def places (NC NT : Nat) (iota : Array Nat) : Option (Array Nat × Array Nat) :=
  let step := fun (st : Option (Array Nat × Array Nat × Nat)) (c : Nat) =>
    st.bind fun x =>
      let trees := 2 ^ iota.getD c 0
      if x.2.2 % trees != 0 then none
      else some (x.1.setIfInBounds c x.2.2,
        (List.range trees).foldl (fun a b => a.setIfInBounds (x.2.2 + b) c) x.2.1,
        x.2.2 + trees)
  ((fallingOrder NC fun c => iota.getD c 0).foldl step
      (some (Array.replicate NC 0, Array.replicate NT 0, 0))).bind fun x =>
    if x.2.2 != NT then none else some (x.1, x.2.1)

/-- **The numbers of a group of calls**, or none. lid: the cap on a tree's depth. The field pub is
left empty. -/
def shapeOwn (calls : Array Call) (lid : Nat) : Option Shape :=
  -- the calls' own tests come first: behind them no call has more than 2^62 keys, so that the
  -- powers of two below are small numbers
  if !calls.all callOk then none else
  let NC := calls.size
  let cK := bitsFor NC
  -- a tree is as deep as the smallest call, and no deeper than the cap
  let dT := calls.foldl (fun m c => min m c.n) lid
  let kT := calls.foldl (fun m c => max m c.k) 0
  let iota := calls.map fun c => c.n - dT
  let NT := iota.foldl (fun s i => s + 2 ^ i) 0
  let rK := bitsFor NT
  if -- from 1 to 16 calls
      decide (1 ≤ NC) && decide (NC ≤ 16) &&
      -- a tree has at least 2^10 keys: the last key level's order of variables needs nine bits
      -- above the tree's number
      decide (10 ≤ dT) &&
      -- at most 256 trees
      decide (NT ≤ 256) &&
      -- a count of 32 bits has room for all keys
      decide (dT + rK < 32) &&
      -- the sum of all counts stays below the prime
      decide (2 ^ (kT + cK + 32) < pW.toNat) then
    (places NC NT iota).map fun x =>
      { calls, dT, kT, NT, rK, NC, cK, iota, first := x.1, callOf := x.2 }
  else none

/-- **The tests on the numbers of padding keys.** -/
def pubOk (h : Shape) (pub : Array Nat) : Bool :=
  -- one number for each tree; the shape's number of calls is its list's
  pub.size == h.NT && h.calls.size == h.NC &&
  -- a tree of 2^dT places holds at most 2^dT padding keys
  (pub.all fun x => decide (x ≤ 2 ^ h.dT)) &&
  -- each call keeps a place for a key that is no padding: else the lookup says nothing of it
  (List.range h.NC).all fun c =>
    let i := h.iota.getD c 0
    let base := h.first.getD c 0
    decide ((List.range (2 ^ i)).foldl (fun s b => s + pub.getD (base + b) 0) 0 < 2 ^ (h.dT + i))

/-- **The test on the packing of the planes of the counts**: the matrix that holds them has 2^lm
rows, lm from 5 to kT + 5. -/
def planesOk (h : Shape) (lm : Nat) : Bool := decide (5 ≤ lm) && decide (lm ≤ h.kT + 5)

/-- The number of columns of the matrix of 2^lm rows that holds the planes of the counts; none
where the packing's test says no. -/
def planeColsOwn (h : Shape) (lm : Nat) : Option Nat :=
  if planesOk h lm then some (h.NC * 2 ^ (h.kT + 5 - lm)) else none

/-- The weights on the 2^lm rows of the planes' matrix under which the planes are read at the point
zb e: the equality weights of (the last lm - 5 coordinates of a table row's index | those of the
plane's number); none where the packing's test says no. -/
def phiBOwn (g : Heard) (lm e : Nat) : Option (Array E) :=
  let h := g.shape
  let zp := g.zb e
  if planesOk h lm then
    some (Model.eqTab (zp.extract (h.kT + 5 - lm) h.kT ++ zp.extract (h.kT + h.cK) zp.size))
  else none

/-- The loop of `pubRunOwn`. base: the number of the call's first tree. Each step takes the places
up to the end of one tree. The argument behind base bounds the number of steps. -/
def pubLoopOwn (dT base : Nat) : Nat → Array Nat → Nat → Nat → Array Nat
  | 0, pub, _, _ => pub
  | steps + 1, pub, first, count =>
    if count = 0 then pub
    else
      let b := first / 2 ^ dT
      let take := min count ((b + 1) * 2 ^ dT - first)
      pubLoopOwn dT base steps (pub.modify (base + b) (· + take)) (first + take) (count - take)

/-- **A run of padding places, counted tree by tree**: adds the places first to first + count - 1
of call c to pub. Place i lies in tree i / 2^dT of its call. None unless pub has a number for each
tree, c is a call, and the run lies inside the call's places. -/
def pubRunOwn (h : Shape) (pub : Array Nat) (c first count : Nat) : Option (Array Nat) :=
  if pub.size != h.NT || decide (c ≥ h.iota.size) then none else
  let i := h.iota.getD c 0
  let places := 2 ^ (h.dT + i)
  if decide (first > places) || decide (count > places - first) then none
  else some (pubLoopOwn h.dT (h.first.getD c 0) (2 ^ i + 1) pub first count)

end VerifiableInference.Desc.First.Look
