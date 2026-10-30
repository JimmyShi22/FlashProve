-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Lists/TwPlan.lean.
The rounds of a lookup as a list of data: for each round its entry in a plan, that is its name and
eleven numbers.

Computable, and general in four sizes: 2^(v'+1) keys, 2^d rows of the table, 2^w slots for planes of
bits, n + 2 planes that count; and in wk, the bits of work of a round with a verifier's message.
Main definitions. rd, rdNone: an entry with and without a verifier's message. pscN: the entries of
one short sumcheck. entN wk v' d w n: the entries of a lookup. shiftN: the entry of the round that
draws a shift. wordsOf: an entry's name and its eleven numbers in the
order in which a chain's parameter bytes list them.
Three of an entry's numbers can be tied to a typed round (msg, drawE, drawNZ: see
OnBytes/Tie/Pv/Lookup/Lists/TwLetter.lean).
The name and the other eight (count, work, roots, answers, poss, logN, trits, rows) are tied to a
typed round by nothing; they are held against the planner
(OnBytes/Tie/Pv/Lookup/Lists/TwPlanOne.lean).

-/
import Fmt.Plan

set_option autoImplicit false

namespace TwPlan
open Fmt

/-- a round with a draw of k elements of E, z of them not 0, after a message of s scalars -/
def rd (wk : Nat) (name : String) (s k : Nat) (z : Nat := 0) : Entry :=
  { name := name, work := wk, msg := 24 * s, drawE := k, drawNZ := z }
/-- a round without a verifier's message -/
def rdNone (name : String) (s : Nat) : Entry := { name := name, msg := 24 * s }

/-- A short sumcheck: round 0 (one scalar, one draw); for each variable a round polynomial of degree
g with one coefficient left out (g scalars); then, if withY, gY scalars and Y, and vals end values.
-/
def pscN (wk : Nat) (degs : List Nat) (withY : Bool) (gY vals : Nat) : List Entry :=
  [rd wk "PSC epsilon" 1 1] ++ degs.map (fun g => rd wk "PSC round" g 1) ++
    if withY then [rd wk "PSC Y" gY 1 1, rdNone "PSC values" vals] else []

def entN (wk v' d w n : Nat) : List Entry :=
  [rd wk "LKP" 0 1] ++ pscN wk [] true 3 3 ++ (List.range n).flatMap (fun _ => pscN wk [] true 3 2)
      ++ [rd wk "JOIN" 0 w] ++
  (List.range (v' + 1)).flatMap (fun l => pscN wk (List.replicate l 2) true 2 2 ++
      [rd wk "LINE" 0 1]) ++
  (List.range d).flatMap (fun l => pscN wk (List.replicate (w + l) 2) true 2 2 ++
      [rd wk "LINE" 0 1]) ++
  pscN wk (List.replicate d 2 ++ List.replicate w 1) false 0 0 ++
  [rd wk "ZERO" 0 (w + d)] ++ pscN wk (List.replicate (w + d) 2) true 2 1

/-- The entry of the round that draws a shift. -/
def shiftN (wk : Nat) : Entry := rd wk "LKP shift" 0 1

/-- An entry's name and its eleven numbers, in the order in which a chain's parameter bytes list
them. -/
def wordsOf (e : Entry) : String × List Nat :=
  (e.name, [e.count, e.work, e.msg, e.roots, e.answers, e.drawE, e.drawNZ, e.poss, e.logN, e.trits,
      e.rows])

end TwPlan
