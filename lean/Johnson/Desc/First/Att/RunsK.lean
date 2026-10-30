-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/RunsK.lean: kind K5: the named runs "first", "keys" and "second" in the type
that a block's field `claims` takes (Johnson/Desc/Block.lean), general in the carried state, over a
seat. A claim is here the ledger's linear form.

Main names:
  `ParC`: the place's numbers for the claims. `SeatC`: what the runs take of the state: what the
    claims read of what was heard, the columns of the array of tables, and what the lookup hands on.
  `ptsFrom`: the road from what was heard to what the claims read: `leftP`, then `pointsOf`.
  `inOf`, `firstK`, `keysOfK`, `keysK`, `secondK`, `runsK`: the runs. Each hands the state back unturned.
In which order a segment takes the runs is the segment's datum.
The tables are made anew in each run, and "keys" reckons "first" anew: the state has no field for
either. So a segment's tables are made twice: by the step that closes the list, and here. No test
asks that the two are one.
A refusal bears the run's name, not its test's.

Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.Block
import Johnson.Desc.First.Att.RunsP

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes
open OnBytes.Model (Aff Fork)
open VerifiableInference.Desc (named)

structure ParC where
  geo : Geo
  iU3 : Nat
  nW : Nat
  mats : Array (Nat × Nat)

structure SeatC (S : Type) where
  pts : S → Option Pts
  cols : S → Option Nat
  look : S → Option LookIn
  pad : S → Option Runs.PadIn
  zk : S → Option (Array (Array E))

/-- The kind's own road from what was heard to what the claims read. F: the ledger behind the hearing. -/
def ptsFrom (g : Geo) (zk : Array (Array E)) (h : Heard) (F : Fork) : Option Pts := do
  pointsOf g zk h (← leftP g zk h F)

variable {S : Type}

/-- What the runs read, and K. -/
def inOf (seat : SeatC S) (c : ParC) (s : S) : Option (Runs.In × Nat) := do
  let p ← seat.pts s
  let t ← tablesP c.geo c.mats c.nW (← seat.look s) p
  pure ({ g := c.geo, p := p, t := t, zk := ← seat.zk s, iU3 := c.iU3 }, ← seat.cols s)

def firstK (seat : SeatC S) (c : ParC) (s : S) : Option (List Aff × S) := do
  let (i, K) ← inOf seat c s
  pure ((← Runs.firstRun i K).1, s)

/-- The calls' key forms, behind "keys"' tests: for the lookup's run that makes the join. -/
def keysOfK (seat : SeatC S) (c : ParC) (s : S) : Option (Array Aff) := do
  let (i, K) ← inOf seat c s
  Runs.keysRun i (← seat.pad s) (← Runs.firstRun i K).2

def keysK (seat : SeatC S) (c : ParC) (s : S) : Option (List Aff × S) := (keysOfK seat c s).map fun _ => ([], s)

def secondK (seat : SeatC S) (c : ParC) (s : S) : Option (List Aff × S) := do
  let (i, K) ← inOf seat c s
  pure (← Runs.secondRun i K, s)

/-- **K5's claims: the three named runs.** The number of claims gathered so far is not read. -/
def runsK (seat : SeatC S) (c : ParC) : List (String × (Nat → S → Except String (List Aff × S))) :=
  [("first", fun _ s => named "K5.first" (firstK seat c s)), ("keys", fun _ s => named "K5.keys" (keysK seat c s)),
   ("second", fun _ s => named "K5.second" (secondK seat c s))]

end VerifiableInference.Desc.First.Att.P
