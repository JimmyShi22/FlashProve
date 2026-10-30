-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Shared/Ground.lean: the seven ground functions over which the shared chain's steps are
written, and the sending of oracle messages.

Definitions only; no theorem is stated. The words are explained in State.lean, and what has been run
and what is not checked is told in Fold.lean.

The steps change the statement and the book of trees only through a record of seven functions,
Ground, which they take as an argument. The decision uses the value callG, in which each function is
one call of a routine of the program: Blk.newGroup, Blk.receiveOracles, Send.admit, Blk.join,
Blk.addRow, Blk.addRowsOnView and Blk.takeMask. For each call, ctxAt builds a context of the program
from the state and the parameters, with no round and no entry of a plan. callAt runs the routine
there. It refuses if the routine fails, if a named test is marked as failed or if a message is left
open. Otherwise it copies the statement, the book of trees, the number of roots and the opened
columns back into the state and drops the rest of the context. So the checks inside these seven
routines are the program's own: they are not written a second time here.

Main names:
  silent r: the round draws no element, position or matrix entry.
  answersOf r: the round's items, if all of them are answers to a sample.
  Ground; ctxAt, callAt, callG: as told above.
  rowsFor, sampleLoop, sendP: a sending. It follows Send.verify and sendVerify
    (OnBytes/Iop/Send.lean) and takes two rounds: the first holds no item and draws the seeds, the
    second holds the answers and draws nothing. sendP returns the messages' numbers, the elements
    drawn and the answers, and it builds the sample rows from these two lists. Send.verify takes its
    rounds from the program's context, so it cannot be a ground call: its checks are written a
    second time here.

What is not claimed. That a check which is written a second time here is the same as the program's.
Nothing on soundness, on an honest prover or on hiding.
What this comment says of the code rests on reading and is not machine-checked.


-/
import Johnson.Desc.Shared.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.Shared
open OnBytes OnBytes.Params

variable {L : Type}

/-- The round draws no element, position or matrix entry. -/
def silent (r : Fmt.RoundView) : Bool :=
  r.drawn.elems.isEmpty && r.drawn.poss.isEmpty && r.drawn.trits.isEmpty

/-- The round's items as field elements, if all of them are answers to a sample. -/
def answersOf (r : Fmt.RoundView) : Option (List E) :=
  r.vals.mapM fun
    | .answer x => some (E.ofTriple x)
    | _ => none

/-- The seven ground functions. Each takes the parameters and the state, and returns the new state
or refuses. -/
structure Ground (L : Type) where
  newGroup : Par → DState L → Nat → Nat → Option (Nat × DState L)
  recv : Par → DState L → Array OracleNotice → Option (Array Nat × DState L)
  admit : Par → DState L → Nat → Array Row → Option (DState L)
  join : Par → DState L → Nat → Nat → Bool → Option (DState L)
  addRow : Par → DState L → Nat → Row → Option (DState L)
  addRows : Par → DState L → Nat → List Row → Option (DState L)
  takeMask : Par → DState L → Nat → Option (Nat × DState L)

/-- The sample rows of the oracle message o for the answers whose numbers are in the first list.
Each row takes the next element of ys as its target. Returns the rows and what is left of ys.
Refuses if ys runs out, if a seed is missing or if Send.form makes no row. -/
def rowsFor (codes : Codes) (s : OracleShape) (o : Nat) (seeds : List SampleSeed) :
    List Nat → List E → Array Row → Option (Array Row × List E)
  | [], ys, acc => some (acc, ys)
  | _ :: _, [], _ => none
  | i :: is, y :: ys, acc =>
    match seeds[i]? with
    | none => none
    | some seed =>
      match Send.form codes s o seed i with
      | none => none
      | some row => rowsFor codes s o seeds is ys (acc.push { row with target := y })

/-- For each oracle message in turn: builds its sample rows and admits it (Ground.admit). Returns
the state and the answers that are left. -/
def sampleLoop (G : Ground L) (p : Par) (codes : Codes) (seeds : List SampleSeed) :
    List (Nat × OracleShape) → List E → DState L → Option (DState L × List E)
  | [], ys, d => some (d, ys)
  | (o, s) :: l, ys, d =>
    match rowsFor codes s o seeds (List.range s.answers) ys #[] with
    | none => none
    | some (rows, ys') =>
      match G.admit p d o rows with
      | none => none
      | some d' => sampleLoop G p codes seeds l ys' d'

/-- A sending, over two rounds. Refuses unless some message has answers, the messages with answers
have increasing numbers and none of them is sampled yet, the first round holds no item and draws
exactly (bits + 1) * answers elements and nothing else, no seed has the factor 0, the second round
holds answers only and draws nothing, and every answer is used. Returns the messages' numbers, the
elements drawn, the answers and the state. -/
def sendP (G : Ground L) (p : Par) (d : DState L) (sent : Array OracleNotice) (r₁ r₂ : Fmt.RoundView) :
    Option (Array Nat × List E × List E × DState L) := do
  let (ids, d₁) ← G.recv p d sent
  let S := d₁.st
  let todo := ids.toList.filter fun o => ((S.oracles[o]?).map (·.shape.answers)).getD 0 != 0
  let shapes ← todo.mapM fun o => (S.oracles[o]?).map (·.shape)
  let bits := shapes.foldl (fun b s => max b (Send.cube S.codes s).bits) 0
  let answers := shapes.foldl (fun a s => max a s.answers) 0
  let sd := r₁.drawn.elems.map E.ofTriple
  let seeds ← Send.seedsOf bits answers sd
  let an ← answersOf r₂
  if !todo.isEmpty && Fmt.increasing todo &&
      todo.all (fun o => ((S.oracles[o]?).map (!·.sampled)).getD false) &&
      r₁.vals.isEmpty && r₁.drawn.poss.isEmpty && r₁.drawn.trits.isEmpty &&
      sd.length == (bits + 1) * answers && seeds.all (fun s => !isZeroE s.beta) && silent r₂ then
    let (d₂, left) ← sampleLoop G p S.codes seeds (todo.zip shapes) an d₁
    if left.isEmpty then some (ids, sd, an, d₂) else none
  else none

/-- A context of the program built from the state and the parameters: a run on a view with no round,
no entry of a plan, no open message and no failed test. -/
def ctxAt (p : Par) (d : DState L) : Ctx :=
  { ch := { dry := false, firstTree := p.firstTree, samples := p.samples, entries := [],
            left := [], opened := d.opened, roots := d.roots },
    st := d.st, book := d.book }

/-- One call of a routine of the program at ctxAt. Refuses if the routine fails, if a named test has
failed or if a message is left open. Otherwise the statement, the book of trees, the number of roots
and the opened columns are copied back into the state, and the rest of the context is dropped. -/
def callAt {α : Type} (p : Par) (d : DState L) (b : Blk α) : Option (α × DState L) :=
  match b (ctxAt p d) with
  | .error _ => none
  | .ok (a, c) =>
    if c.failed.isNone && c.ch.cur.isNone then
      some (a, { d with st := c.st, book := c.book, roots := c.ch.roots, opened := c.ch.opened })
    else none

/-- The ground functions as single calls of the program's routines. -/
def callG : Ground L :=
  { newGroup := fun p d code maskCode => callAt p d (Blk.newGroup code maskCode)
    recv := fun p d sent => callAt p d (Blk.receiveOracles sent)
    admit := fun p d o rows => (callAt p d (Send.admit o rows)).map (·.2)
    join := fun p d g o kept => (callAt p d (Blk.join g o kept)).map (·.2)
    addRow := fun p d g row => (callAt p d (Blk.addRow g row)).map (·.2)
    addRows := fun p d g rows => (callAt p d (Blk.addRowsOnView g fun _ => some rows)).map (·.2)
    takeMask := fun p d o => callAt p d (Blk.takeMask o) }

end Desc.Shared
