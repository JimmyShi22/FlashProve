-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Hot.lean: the inner loops of a lookup's row that passes its tables
on, in a file that imports little: the round polynomial of a kept state, the binding of a challenge,
a level of a product tree out of the level below, the table side's leaves. Definitions with code; no
theorem.

Terms. Honest/K3/GLOSSARY.md. In this file: a kept state is a value of `Kept`
(Honest/K3/KeptTypes.lean).

Why. These loops go over tables of 2 ^ 22 entries and more. Honest/K3/JobsFast.lean,
Honest/K3/JobsKeep.lean and Honest/K3/StoreMake.lean, where they are written first, import the frame
and, through it, Mathlib; a file's compiled code can be loaded beside Lean's evaluator only together
with the compiled code of all that it imports. This file imports the verifier program's own modules
and Honest/K3/KeptTypes.lean, and no other. So its code can be compiled and loaded with these alone.

What is defined. Each definition has the text of the one that is named behind it, with a cube's two
fields read off the kept state.
  `at0`, `bindAt`, `pos`, `coord`: `Fast.at0`, `Fast.bindAt`, `Fast.Cube.pos`, `Fast.coord`.
  `round`: `Fast.keptRound`, which is `Fast.cubeRound` at a kept state.
  `bind`: `Fast.keptBind`.
  `up`, `lvlsFrom`, `lvlsUp`: `Fast.up`, `Fast.lvlsFrom`, `Fast.lvlsUp`.
  `leafTab`: the table side's leaves, 1 + bit times factor: the `Array.zipWith` in `Fast.storeOf`.
  `lessOne`: each entry less 1: the second table of the bits' sumcheck.
  `keyLeaves`, `bitTab`, `facTab`: the leaves of a key tree and the two tables of `Fast.srcOf`, at
    letters for the readers of a key, a bit and a row: the loop is here, the reading is the
    caller's.
  `halves`: the two tables of a level's sumcheck, out of the level below.

Imported. OnBytes/Model/Look.lean, and through it the field's elements (OnBytes/Field/Ext.lean) and
`eqTab` (OnBytes/Model/Frame.lean); Honest/K3/KeptTypes.lean.

Users. Honest/K3/HotLaw.lean, where each is shown to be the definition that is named behind it;
Honest/K3/RowKeepHot.lean.

Limits. As the texts that are copied: no function rejects. An entry beyond a table's end and a
coordinate beyond a point's end count as 0; a table that the kept state lacks counts as the empty
one; beyond the order's end `round` takes bit 0, and `bind` raises the count and binds nothing; in
`coord` a bit's number from m on reads coordinate 0, since m - 1 - b is cut at 0. The point's
coordinates and the value that `bind` binds are letters of the field's type here: the callers lay
challenges. No coin of the prover's and no mask entry is read in this file. How long a loop takes is
not said here.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import OnBytes.Model.Look
import Johnson.Desc.ProofFile.Honest.K3.KeptTypes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Hot
open OnBytes (E addE subE mulE zeroE oneE foldPairE)

/-- Among the entries whose bit at position p is 0: the number of the i-th. -/
def at0 (p i : Nat) : Nat := i / 2 ^ p * 2 ^ (p + 1) + i % 2 ^ p

/-- One bit bound: the bit at position p of a table's numbers is set to r. -/
def bindAt (p : Nat) (r : E) (t : Array E) : Array E :=
  let s := 2 ^ p
  (Array.range (t.size / 2)).map fun i =>
    foldPairE (t.getD (at0 p i) zeroE) (t.getD (at0 p i + s) zeroE) r

/-- The position of bit b in the tables' numbers: how many free bits lie below it. -/
def pos (free : List Nat) (b : Nat) : Nat := (free.filter (· < b)).length

/-- Bit b's coordinate of a point of m coordinates: the highest bit first. -/
def coord (m : Nat) (z : Array E) (b : Nat) : E := z.getD (m - 1 - b) zeroE

/-- **The round polynomial, of a kept state**: three coefficients, lowest first. -/
def round (kappa : E) (m : Nat) (order : List Nat) (k : Kept) : List E :=
  let b := order.getD k.bound 0
  let p := pos k.free b
  let s := 2 ^ p
  let ta := k.tabs.getD 0 #[]
  let tb := k.tabs.getD 1 #[]
  let w := OnBytes.Model.eqTab ((k.free.filter (· != b)).reverse.map (coord m k.z)).toArray
  let out := (Array.range w.size).foldl
    (fun (acc : E × E × E) i =>
      let a0 := ta.getD (at0 p i) zeroE
      let a1 := subE (ta.getD (at0 p i + s) zeroE) a0
      let b0 := tb.getD (at0 p i) zeroE
      let b1 := subE (tb.getD (at0 p i + s) zeroE) b0
      let wi := w.getD i zeroE
      (addE acc.1 (mulE wi (addE kappa (mulE a0 b0))),
       addE acc.2.1 (mulE wi (addE (mulE a0 b1) (mulE a1 b0))),
       addE acc.2.2 (mulE wi (mulE a1 b1))))
    (zeroE, zeroE, zeroE)
  [out.1, out.2.1, out.2.2]

/-- **The kept state behind a challenge**: the order's next bit is bound. -/
def bind (order : List Nat) (k : Kept) (r : E) : Kept :=
  match order[k.bound]? with
  | some b =>
    ⟨k.free.filter (· != b), k.tabs.map (bindAt (pos k.free b) r), k.bound + 1, k.z, k.vals⟩
  | none => { k with bound := k.bound + 1 }

/-- The level above a level of a product tree. -/
def up (a : Array E) : Array E :=
  let h := a.size / 2
  (Array.range h).map fun x => mulE (a.getD x zeroE) (a.getD (h + x) zeroE)

/-- The level a, the n levels above it, and what was gathered: the highest first. -/
def lvlsFrom : Nat → Array E → List (Array E) → List (Array E)
  | 0, a, acc => a :: acc
  | n + 1, a, acc => lvlsFrom n (up a) (a :: acc)

/-- The leaves and the n levels above them, the highest first. -/
def lvlsUp (n : Nat) (leaves : Array E) : Array (Array E) := (lvlsFrom n leaves []).toArray

/-- The table side's leaves: 1 + bit times factor. -/
def leafTab (b a : Array E) : Array E := Array.zipWith (fun b a => addE oneE (mulE b a)) b a

/-- Each entry less 1. -/
def lessOne (b : Array E) : Array E := b.map fun x => subE x oneE

/-- A key tree's leaves: alpha - key, at 2 ^ v places. Here key reads the key at a place. -/
def keyLeaves (alpha : E) (v : Nat) (key : Nat → E) : Array E :=
  (Array.range (2 ^ v)).map fun x => subE alpha (key x)

/-- The bits, by the leaf's number: the plane's bits are the low ones; a plane from `planes` on
counts as 0. Here bit reads the bit of a row and a plane. -/
def bitTab (mu d planes : Nat) (bit : Nat → Nat → E) : Array E :=
  let pl := 2 ^ mu
  (Array.range (2 ^ (mu + d))).map fun X =>
    if X % pl < planes then bit (X / pl) (X % pl) else zeroE

/-- alpha - 1 - row, by the leaf's number. Here row reads the table's row; each row is read once. -/
def facTab (mu d : Nat) (alpha : E) (row : Nat → E) : Array E :=
  let pl := 2 ^ mu
  let R := (Array.range (2 ^ d)).map fun u => subE (subE alpha oneE) (row u)
  (Array.range (2 ^ (mu + d))).map fun X => R.getD (X / pl) zeroE

/-- The lower and the upper half of a level with m + 1 variables. -/
def halves (m : Nat) (n : Array E) : List (Array E) :=
  [n.extract 0 (2 ^ m), n.extract (2 ^ m) (2 ^ (m + 1))]

end ProofFile.Honest.K3.Hot
