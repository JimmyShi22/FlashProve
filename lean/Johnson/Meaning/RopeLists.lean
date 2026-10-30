-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/RopeLists.lean: the arithmetic of the verifier's rotary table as a recursion that
returns lists. Definitions, and pairList_get: member m of pairList.

ropeTable (OnBytes/Model/LayerTables.lean:203) fills an array of 2 T half words by 2 T half writes.
Lean's kernel holds an array as a list, so it cannot evaluate that text at T = 1024, half = 64 in
reasonable time. Here the same arithmetic is written as a recursion that returns lists (tokList,
pairList): for each pair of channels the list, over the tokens, of the two words. That the routine's
entries are these words is Johnson/Meaning/RopeSpec.lean (table_spec); the evaluation against the
library's stored tables is Johnson/Meaning/RopeWords.lean.
-/
import OnBytes.Model.LayerTables

set_option autoImplicit false

namespace Meaning.Rope

open OnBytes.Model.Layer (fxOne roundD cosSin turn ropeWord rootLoop ropeTokens ropePairs ropeTable)
open OnBytes (ceilLog2)

/-- The two words of pair i for the tokens t, t + 1 and so on, n of them: ropeTokens' arithmetic,
letter for letter, with a list in the array's place. -/
def tokList (cs : Nat) (p : Nat × Nat) (pf : Nat) (r : Int × Int) :
    Nat → Nat → Int → Int → List (Nat × Nat)
  | 0, _, _, _ => []
  | n + 1, t, c, s =>
    let ang := roundD (t * p.1) p.2
    let delta : Int := (ang.1 * fxOne / ang.2 : Nat) - (t * pf : Nat)
    let x := turn c s (cosSin delta)
    let next := turn c s r
    (ropeWord cs x.1, ropeWord cs x.2) :: tokList cs p pf r n (t + 1) next.1 next.2

/-- The lists of the pairs i, i + 1 and so on, n of them: ropePairs' arithmetic. -/
def pairList (cs T u : Nat) : Nat → Nat → List (List (Nat × Nat))
  | 0, _ => []
  | n + 1, x =>
    let p := roundD x fxOne
    let pf := p.1 * fxOne / p.2
    tokList cs p pf (cosSin pf) T 0 fxOne 0 :: pairList cs T u n (x * u / fxOne)

/-- theta0^(-2 / dh) in fixed-point, as ropeTable computes it. -/
def uOf (theta0 half : Nat) : Nat :=
  rootLoop (ceilLog2 half) (fxOne * (roundD theta0 1).2 / (roundD theta0 1).1)

/-- The list of one pair, from the pair's power x of u. -/
def rowOf (cs T x : Nat) : List (Nat × Nat) :=
  tokList cs (roundD x fxOne) ((roundD x fxOne).1 * fxOne / (roundD x fxOne).2)
    (cosSin ((roundD x fxOne).1 * fxOne / (roundD x fxOne).2 : Nat)) T 0 fxOne 0

/-- The power after m more pairs. -/
def xAt (u : Nat) : Nat → Nat → Nat
  | 0, x => x
  | m + 1, x => xAt u m (x * u / fxOne)

/-- Member m of pairList is the list of the pair with the power after m pairs. -/
theorem pairList_get (cs T u : Nat) : ∀ (n x m : Nat), m < n →
    (pairList cs T u n x).getD m [] = rowOf cs T (xAt u m x)
  | 0, _, m, h => absurd h (Nat.not_lt_zero m)
  | n + 1, x, 0, _ => rfl
  | n + 1, x, m + 1, h => by
    have e : pairList cs T u (n + 1) x = rowOf cs T x :: pairList cs T u n (x * u / fxOne) := rfl
    rw [e]
    show (pairList cs T u n (x * u / fxOne)).getD m [] = _
    exact pairList_get cs T u n (x * u / fxOne) m (Nat.lt_of_succ_lt_succ h)

end Meaning.Rope
