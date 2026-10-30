-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/AtS.lean: K4's block (Johnson/Desc/First/K4/Block.lean) at the record that
the proof file's first chain carries (Johnson/Desc/First/State.lean: `S`).
CODE ALONE: no theorem.

Inside a layers' link S holds `LayOwn` (the link; the sub-proof's ledger F; what the lookup
returned, fo; what the own rounds returned, own; the smallness test's record; a slot); at its top
the debt of rows (`rowsOwed`) and the request file's words (`req`), of which `S.tokv` makes the
tokens. `seatOwn` seats the block at these three: it READS F, fo, the debt and the tokens, and LAYS
F, own and the debt; own is `verify-on-bytes`'s own record `Layer.Own`, which the places behind K4
read.

What the lookup returned (`fo`) and what K4's own rounds returned (`own`) are `none` in S (`LayOwn`)
until the step that lays them: so K4's two tests «what the lookup returned is not
there» and «what was heard is not there» can refuse: a step left out in front is a refusal on the
honest proof. The second road for the lookup's return (`lookHeard`) is not read here.

`blockAtS p`: the block at S, by Block.lean's `liftPart`: IT REFUSES UNLESS THE CHAIN STANDS IN A
LAYERS' LINK (`here = .lay a`). All else of S is handed on untouched. `bare`: the same without its
claims and its run behind the batching, at any type of a claim: for a fold in which the batching's
place is still `verify-on-bytes`.
-/
import Johnson.Desc.First.State
import Johnson.Desc.First.K4.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.Model OnBytes.Model.Layer
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S LayOwn)

/-- K4's part of S: what S holds inside a layers' link; the debt of rows; the request's tokens. -/
abbrev Part : Type := LayOwn × Option Nat × Array Nat

/-- Where in K4's part lie the things that K4 reads and writes. -/
def seatOwn : Seat Part where
  fork := (·.1.F)
  setFork := fun a F => ({ a.1 with F := F }, a.2)
  look := fun a => a.1.fo
  own := fun a => a.1.own
  setOwn := fun a o => ({ a.1 with own := some o }, a.2)
  owed := (·.2.1)
  setOwed := fun a d => (a.1, d, a.2.2)
  tokv := (·.2.2)

/-- K4's part of S; nothing outside a layers' link. THE DEBT IS READ BY `S.noneWaits`: "some 0" (the
round closed last counts no rows) and "none" answer alike, as in `verify-on-bytes`'s `settled`
(OnBytes/Iop/Ground.lean:602-605): both are handed on as none. -/
def part? (s : S) : Option Part :=
  match s.here with
  | .lay a => some (a, if s.noneWaits then none else s.rowsOwed, s.tokv)
  | _ => none

/-- Lays the part back. THE TOKENS ARE READ ALONE: nothing of the request is written. -/
def setPart (s : S) (x : Part) : S := { s with here := .lay x.1, rowsOwed := x.2.1 }

/-- **K4 at the first chain's carried record.** -/
def blockAtS (p : Par) : Block S Aff := (block seatOwn p).liftPart part? setPart

/-- A block without its claims and its runs behind the batching, at any type of a claim. -/
def bare {T Cl Cl' : Type} (b : Block T Cl) : Block T Cl' :=
  { name := b.name, place := b.place, planOk := b.planOk, rounds := b.rounds, oracles := b.oracles
    before := b.before, decide := b.decide, claims := [], after := [] }

end OnBytes.Desc.First.K4
