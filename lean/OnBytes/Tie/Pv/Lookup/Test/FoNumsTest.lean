-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Test/FoNumsTest.lean: tests of OnBytes/Tie/Pv/Lookup/Port/FoNums.lean. A
#guard is a run while the file compiles, no theorem.

kinds: the twelve kinds of lookup of the two public kits; least: the least forest that Forest.shape
takes (one call of 2^10 keys and 2^5 rows: 260 rounds); toy: three calls of unequal size with a tree
of padding alone. Each is made by the verifier's own Forest.shape from each call's numbers (n, k,
t0) and the cap on a tree's depth. Made up in them: range tables stand for the written tables, and
the sum of the padding is spread evenly over the trees.
Tested: the shapes' numbers are those printed from the kits' files [the prints are not in this
library]; ok holds; as many mask places as
Forest.elems, as many end claims as Forest.lins + 4; the padding's counts sum to Shape.padding; each
order names each variable once; the last key level's order is neither the default nor the identity;
each call's key places are hit once. Controls: ok refuses bent shapes.

-/
import OnBytes.Tie.Pv.Lookup.Port.FoNums

set_option autoImplicit false

namespace FoNums
open OnBytes.Model

/-! ### the twelve kinds and the least shape -/
/-- by the verifier's own Forest.shape; the sum of the padding spread evenly over the trees (made
up) -/
def mk (calls : List (Nat × Nat × Nat)) (lid sumPub : Nat) : Option Sh :=
  (Forest.shape
      (calls.map fun c => ({ n := c.1, k := c.2.1, t0 := c.2.2, kappa := 5 } : Call)).toArray
      lid).toOption.bind fun h0 =>
    let pub := (Array.range h0.NT).map fun y => sumPub / h0.NT + if y = 0 then sumPub % h0.NT else 0
    if (Forest.pubAsk h0 pub).toBool then some { h0 with pub := pub } else none

def kinds : List (String × Option Sh) :=
  [("full G", mk
      [(27,16,0),(27,16,0),(27,16,0),(28,8,0),(27,16,32768),(27,16,32768),(26,16,32768),(26,16,0)]
      28 225941504),
   ("full A", mk [(27,16,0),(27,16,2307),(26,16,0),(25,16,0)] 28 117276672),
   ("full H", mk [(28,16,0),(28,16,0),(28,8,0),(27,16,0),(27,16,0),(27,16,32768)] 28 364519424),
   ("full tG", mk [(26,10,0),(26,8,0)] 28 6291456),
   ("full tA", mk [(25,10,0),(25,8,0)] 28 10485760),
   ("full tH", mk [(26,10,0),(26,8,0)] 28 35651584),
   ("small G", mk
       [(20,16,0),(20,16,0),(20,16,0),(21,8,0),(20,16,32768),(20,16,32768),(20,16,32768),(20,16,0)]
       24 5122944),
   ("small A", mk [(20,16,0),(20,16,2307),(20,16,0),(20,16,0)] 24 3701760),
   ("small H", mk [(20,16,0),(20,16,0),(20,8,0),(20,16,0),(20,16,0),(20,16,32768)] 24 6054400),
   ("small tG", mk [(23,10,0),(23,8,0)] 24 0),
   ("small tA", mk [(22,10,0),(22,8,0)] 24 524288),
   ("small tH", mk [(23,10,0),(23,8,0)] 24 6291456)]
/-- the least forest that Forest.shape takes: one call of 2^10 keys, 2^5 rows -/
def least : Option Sh := mk [(10, 5, 0)] 28 3
def all13 : List (Option Sh) := kinds.map (·.2) ++ [least]

/-! ### Guards -/
-- Forest.shape takes all thirteen; dT, kT, NT, rK, NC, cK, v, d, emptyKeys are those printed from
-- the kits' files
#guard all13.all (·.isSome)
#guard all13.map
    (fun o => o.map fun h => (h.dT, h.kT, h.NT, h.rK, h.NC, h.cK, h.v, h.d, h.emptyKeys)) ==
  [(26,16,16,4,8,3,30,19,0), (25,16,11,4,4,2,29,18,167772160), (27,16,9,4,6,3,31,19,939524096),
      (26,10,2,1,2,1,27,11,0), (25,10,2,1,2,1,26,11,0), (26,10,2,1,2,1,27,11,0),
   (20,16,9,4,8,3,24,19,7340032), (20,16,4,2,4,2,22,18,0), (20,16,6,3,6,3,23,19,2097152),
       (23,10,2,1,2,1,24,11,0), (22,10,2,1,2,1,23,11,0), (23,10,2,1,2,1,24,11,0),
   (10,5,1,0,1,0,10,5,0)].map some
#guard (all13.take 3).map (fun o => o.map fun h => (h.iota, h.first)) ==
  [some (#[1,1,1,2,1,1,0,0], #[4,6,8,0,10,12,14,15]), some (#[2,2,1,0], #[0,4,8,10]), some
      (#[1,1,1,0,0,0], #[0,2,4,6,7,8])]
#guard all13.all fun o => o.any ok
-- as many mask places as scalars sent; as many end claims as the verifier's (lins, three on the
-- planes, one on the keys)
#guard all13.all fun o => o.any fun h => nMasks h == Forest.elems h && nClaims h == Forest.lins
    h + 4
-- the padding: the pairs' counts sum to Shape.padding; the rows differ; each is a row of the joined
-- table
#guard all13.all fun o => o.any fun h => ((pads h).map (·.2)).sum == h.padding &&
    ((pads h).all fun p => decide (p.1 < 2 ^ h.d)) && decide ((pads h).map (·.1)).Nodup
-- the orders: each a list of all the level's variables, each once
#guard all13.all fun o => o.any fun h => (List.range h.v).all fun l =>
    ((ordK h l).toArray.qsort (· < ·)).toList == List.range l
#guard all13.all fun o => o.any fun h => ordE h == orderDefault (w + h.d) && ordB h == orderDefault
    (w + h.d)
-- the last key level's order is neither the default nor the identity, at all thirteen
#guard all13.all fun o => o.any fun h => ordK h (h.v - 1) != orderDefault (h.v - 1) && ordK h
    (h.v - 1) != List.range (h.v - 1)
#guard least.map (fun h => ordK h 9) == some [2, 1, 0, 5, 4, 3, 8, 7, 6]
#guard (kinds.head?.bind (·.2)).map (fun h => ordK h 29) == some
    [6,5,4,9,8,7,12,11,10,28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,3,2,1,0]
-- the key file's lookup's rule for the last key level, at the nine variables above the tree's
-- number, gives the same list
#guard all13.all fun o => o.any fun h => OnBytes.Lkp.orderBeginning (nine h.rK) (h.v - 1) == ordK h
    (h.v - 1)
-- every key below 2^v of the least shape and of a small made-up forest has its place; each call's
-- entries are hit once
#guard least.any fun h => ((List.range (2 ^ h.v)).filterMap (keyOf h)).map (·.2) == List.range 1024
def toy : Option Sh := mk [(10, 5, 1), (12, 6, 0), (11, 5, 3)] 10 5
#guard toy.map (fun h => (h.dT, h.kT, h.NT, h.rK, h.NC, h.cK, h.iota, h.first, h.callOf)) == some
    (10, 6, 7, 3, 3, 2, #[0, 2, 1], #[6, 0, 4], #[1, 1, 1, 1, 2, 2, 0])
#guard toy.any ok
#guard toy.any fun h => (List.range 3).all fun c =>
  ((((List.range (2 ^ h.v)).filterMap (keyOf h)).filter (·.1 == c)).map (·.2)).toArray.qsort (· < ·)
      == Array.range (2 ^ nOf h c)
#guard toy.any fun h => ((List.range (2 ^ h.v)).filter fun X => (keyOf h X).isNone).length ==
    h.emptyKeys
#guard toy.any fun h => (List.range (2 ^ h.d)).all fun u => (cellOf h u 0).isSome == decide
    (u % 4 < 3)
-- controls: ok refuses a bent shape
#guard toy.any fun h => !ok { h with NT := h.NT + 1 } && !ok { h with callOf := h.callOf.set! 0 2 }
    && !ok { h with dT := 9 } && !ok { h with pub := #[] } && !ok
    { h with first := h.first.set! 1 1 } && !ok { h with kT := 17 }


end FoNums
