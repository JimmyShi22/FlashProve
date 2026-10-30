-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/WitNamed.lean: TEST SCAFFOLDING: a named reader of a lookup's input
beside the seated one, the lot at it, and a test with code that holds two readers against each
other. A play over the named reader counts apart: no theorem shows that a row at it plays as a row
at the prover's own reader does (what is had: Honest/K3/NamedLaw.lean [not in this library] and
`site_same`, Honest/K3/Law/Keep/ReadsNoFurtherNamed.lean [not in this library]).
Definitions with code; no theorem.

Terms. Honest/K3/GLOSSARY.md. In this file: the seated reader is `boundWit`
(Honest/K3/WitBound.lean); a site is a lookup of a public part at its place (`Site`,
Honest/K3/Lot.lean); a reader's answer at a site is a value of `Ask`, and what that hands out a
value of `Hidden` (Honest/K3/Stages.lean).

What is defined.
  `namedHidden h keyAt count`: keys and bits at a lookup of shape h, by `Named.keyFn` and
    `Named.bitFn` (Honest/K3/NamedKeys.lean). Its two fields are these functions with the plan and
    the caller's function laid in: nothing is made when a key or a bit is asked for.
  `namedAsk`: the same as an `Ask` that ignores the challenges heard.
  `noHidden`: keys and bits that are all 0.
  `NamedRun`, `NamedRun.make`: for each link's number the `Hidden` of the link's lookup on calls. A
    value: whoever binds it has it made once.
  `NamedRun.ask R other`: the reader, site by site, closed: at a site on calls the run's `Hidden` at
    the link's number; at a site on digits the answer of `other`.
  `theLotKeepRun runAsk get set`: the lot at a closed reader runAsk : Site → Ask: the term
    rowLotKeepAt (fun Z => fastFillKeep (codeRows Z) fun s _ => runAsk s) get set.
  `agreeAt a b heard theta places rows`: a test: the two answers hand out the same key at each of
    the places, at the shift theta and part 0, and the same bit at each pair of a row and a plane.

The link's number. Link 2 g holds group g's layers, link 2 g + 1 its attention, and the last link
the head, where attention links stand between (`callerOf`, Honest/K3/Lot.lean).

Imported. Honest/K3/NamedKeys.lean; Honest/K3/LotInstKeepCode.lean. Nothing of whoever supplies
keyAt and count is imported: they are arguments.

Users. Honest/K3/Law/CoverageLotsNamed.lean; outside this library:
Honest/K3/NamedLaw.lean [not in this library], Honest/K3/WitNamedToy.lean [not in this library].
Meant for a test of the honest prover's play.

Limits. THIS FILE IS SCAFFOLDING FOR TESTS: it reads a run's list with a default at an index that
nothing bounds (below), over NamedKeys.lean, which reads keys and bits so: it is not for a filling
at which anything is counted. Nothing is shown. In particular not that a row at this reader shows
what a row at the seated reader shows: that would want that keyAt and count give the keys and the
counts which the seated reader makes of the cells. `agreeAt` speaks of the places and rows that it
is handed, and of no other. At a link's number that no site on calls bears, `NamedRun.make` lays
zeros; and `NamedRun.ask` reads the run's list at the site's link with these zeros as a stand-in
(`R.hid.getD s.link noHidden`): at a link beyond the list's end it hands out zeros without a word,
and nothing here bounds the link by the list's length. `theLotKeepRun` bears the one lot's name:
only one of the lots that bear it may stand in a list of lots' honest sides at a time
(Honest/K3/LotInstKeepBound.lean): a caution; nothing here shows or tests it. It lays a half only at
an address at which a site can be made (`lotBy`, Honest/K3/Lot.lean); that its halves are those of
`rowLotKeep` at its letters: `theLotKeepRun_halves` (Honest/K3/Law/CoverageLotsNamed.lean).

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.NamedKeys
import Johnson.Desc.ProofFile.Honest.K3.LotInstKeepCode

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E zeroE)

variable {V W X : Type}

/-- **Keys and bits at a lookup of shape h**, of a call's keys and counts. -/
def namedHidden (h : OnBytes.Model.Forest.Shape) (keyAt : Nat → Nat → Option Int)
    (count : Nat → Nat → Nat) : Hidden :=
  let P := Named.planOf h
  ⟨Named.keyFn P keyAt, Named.bitFn P count⟩

/-- The same as an answer that ignores the challenges heard. -/
def namedAsk (h : OnBytes.Model.Forest.Shape) (keyAt : Nat → Nat → Option Int)
    (count : Nat → Nat → Nat) : Ask :=
  fun _ => namedHidden h keyAt count

/-- For each link's number: keys and bits of the link's lookup on calls. -/
structure NamedRun where
  hid : Array Hidden

/-- Keys and bits that are all 0. -/
def noHidden : Hidden := ⟨fun _ _ _ => zeroE, fun _ _ => zeroE⟩

/-- **The run's keys and bits, made once.** Here ss are the public part's sites; keyAt is handed the
link's number, the call and the place in the call's own vector; count the link's number, the call
and the row of the call's own table. -/
def NamedRun.make (ss : List Site) (keyAt : Nat → Nat → Nat → Option Int)
    (count : Nat → Nat → Nat → Nat) : NamedRun :=
  ⟨(Array.range ((ss.map (·.link + 1)).foldl max 0)).map fun l =>
    match ss.find? fun s => s.link == l && !s.digits with
    | some s => namedHidden s.shape (keyAt l) (count l)
    | none => noHidden⟩

/-- **The named reader, site by site, closed.** At a site on digits: the answer of `other`. -/
def NamedRun.ask (R : NamedRun) (other : Site → Ask) (s : Site) : Ask :=
  if s.digits then other s else fun _ => R.hid.getD s.link noHidden

/-- **The lot at a closed reader.** -/
def theLotKeepRun (runAsk : Site → Ask) (get : X → RowOwn) (set : X → RowOwn → X) : HLot V W X :=
  rowLotKeepAt (fun Z => fastFillKeep (codeRows Z) fun s _ => runAsk s) get set

/-- **A test: two answers hand out the same** at the shift theta: the key of part 0 at each of the
places, the bit at each pair of a row and a plane. -/
def agreeAt (a b : Ask) (heard : List Fmt.Drawn) (theta : E) (places : List Nat)
    (rows : List (Nat × Nat)) : Bool :=
  let A := a heard
  let B := b heard
  (places.all fun x => A.key theta 0 x == B.key theta 0 x) &&
    rows.all fun y => A.bit y.1 y.2 == B.bit y.1 y.2

end ProofFile.Honest.K3
