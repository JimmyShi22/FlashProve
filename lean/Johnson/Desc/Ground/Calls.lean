-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ground/Calls.lean: the record of seven ground functions over which a chain's steps are
written, its value in plain functions, and a sending.

This file holds definitions only; no theorem is stated.

The steps of a description change the statement and the book of trees through a record of seven
functions (Ground): a new group; messages received; a message's sample admitted; a message joins a
group; a row, or rows, added to a group; an entry of a mask taken. groundG is the description's
value of that record: each field is a plain function of Johnson/Desc/First/Base/Ground.lean, a test
in named clauses and an effect. Of GPar's two numbers groundG hands on firstTree alone, to recv;
GPar.samples is read by none of the seven.

Main names:
  silent: the round draws nothing. answersOf: a round's items, where all are answers.
  Ground, groundG.
  rowsFor, sampleLoop, sendP: a sending, written after Send.verify and sendVerify
    (OnBytes/Iop/Send.lean) and calling its plain function Send.cube; the cut of the drawn elements
    into seeds, the sample row's left side and "a seed's factor is not 0" are seedsMade, formMade
    (Johnson/Desc/Own/Send.lean) and allZero (Johnson/Desc/Own/Rows.lean), which compares an
    element's three words with 0 and speaks of the field's zero only where every word is below the
    prime: two rounds. The first holds no item and draws the seeds. The second
    holds the answers and draws nothing (own = true); at a switch the answers are the first items of
    a round in which the caller goes on (own = false). sendP returns the messages' numbers, the
    elements drawn, the answers, how many items were taken, and the state. The sample rows are made
    out of the elements drawn and the answers. That the numbers of the messages to be sampled rise
    is asked by rising (Johnson/Desc/Own/Rising.lean).

Johnson/Desc/Shared/Ground.lean holds other definitions of the same short names, in the namespace
Desc.Shared. No theorem ties the two files.

What is not claimed. That a test or a sending written here is the program's. Nothing on soundness,
on an honest prover or on hiding.

-/
import Johnson.Desc.First.Base.DescState
import Johnson.Desc.First.Base.Ground
import Johnson.Desc.Own.Send
import Johnson.Desc.Own.Rows
import Johnson.Desc.Own.Rising

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.Plain
open OnBytes OnBytes.Params

variable {L : Type}

/-- The round draws nothing. -/
def silent (r : Fmt.RoundView) : Bool :=
  r.drawn.elems.isEmpty && r.drawn.poss.isEmpty && r.drawn.trits.isEmpty

/-- A round's items, where all are answers to a sample. -/
def answersOf (r : Fmt.RoundView) : Option (List E) :=
  r.vals.mapM fun
    | .answer x => some (E.ofTriple x)
    | _ => none

/-- The seven ground functions over which the steps are written. -/
structure Ground (L : Type) where
  newGroup : GPar → DState L → Nat → Nat → Option (Nat × DState L)
  recv : GPar → DState L → Array OracleNotice → Option (Array Nat × DState L)
  admit : GPar → DState L → Nat → Array Row → Option (DState L)
  join : GPar → DState L → Nat → Nat → Bool → Option (DState L)
  addRow : GPar → DState L → Nat → Row → Option (DState L)
  addRows : GPar → DState L → Nat → List Row → Option (DState L)
  takeMask : GPar → DState L → Nat → Option (Nat × DState L)

/-- The sample rows of the message o, for the answers number is: each takes the next answer of ys as
its target. Returns the rows and the answers that are left. -/
def rowsFor (codes : Codes) (s : OracleShape) (o : Nat) (seeds : List SampleSeed) :
    List Nat → List E → Array Row → Option (Array Row × List E)
  | [], ys, acc => some (acc, ys)
  | _ :: _, [], _ => none
  | i :: is, y :: ys, acc =>
    match seeds[i]? with
    | none => none
    | some seed =>
      match VerifiableInference.Desc.Own.formMade codes s o seed i with
      | none => none
      | some row => rowsFor codes s o seeds is ys (acc.push { row with target := y })

/-- Message by message: its sample rows, and it is admitted. -/
def sampleLoop (G : Ground L) (p : GPar) (codes : Codes) (seeds : List SampleSeed) :
    List (Nat × OracleShape) → List E → DState L → Option (DState L × List E)
  | [], ys, d => some (d, ys)
  | (o, s) :: l, ys, d =>
    match rowsFor codes s o seeds (List.range s.answers) ys #[] with
    | none => none
    | some (rows, ys') =>
      match G.admit p d o rows with
      | none => none
      | some d' => sampleLoop G p codes seeds l ys' d'

/-- A sending: two rounds. own: the second round is the sending's own (the program's flag ownRound,
OnBytes/Iop/Send.lean:187): it then holds the answers alone and draws nothing. Else the answers are
the round's FIRST items, nothing is asked of what the round draws or of its other items, and the
caller goes on in that round. Returns the numbers, the elements drawn, the answers, how many items
of the second round were taken, and the state. -/
def sendP (G : Ground L) (p : GPar) (own : Bool) (d : DState L) (sent : Array OracleNotice)
    (r₁ r₂ : Fmt.RoundView) : Option (Array Nat × List E × List E × Nat × DState L) := do
  let (ids, d₁) ← G.recv p d sent
  let S := d₁.st
  let todo := ids.toList.filter fun o => ((S.oracles[o]?).map (·.shape.answers)).getD 0 != 0
  let shapes ← todo.mapM fun o => (S.oracles[o]?).map (·.shape)
  let bits := shapes.foldl (fun b s => max b (Send.cube S.codes s).bits) 0
  let answers := shapes.foldl (fun a s => max a s.answers) 0
  let need := shapes.foldl (fun a s => a + s.answers) 0
  let sd := r₁.drawn.elems.map E.ofTriple
  let seeds ← VerifiableInference.Desc.Own.seedsMade bits answers sd
  let an ← answersOf { r₂ with vals := r₂.vals.take need }
  if !todo.isEmpty && VerifiableInference.Desc.Own.rising todo &&
      todo.all (fun o => ((S.oracles[o]?).map (!·.sampled)).getD false) &&
      r₁.vals.isEmpty && r₁.drawn.poss.isEmpty && r₁.drawn.trits.isEmpty &&
      sd.length == (bits + 1) * answers &&
      seeds.all (fun s => !VerifiableInference.Desc.Own.allZero s.beta) &&
      an.length == need && (!own || (r₂.vals.length == need && silent r₂)) then
    let (d₂, left) ← sampleLoop G p S.codes seeds (todo.zip shapes) an d₁
    if left.isEmpty then some (ids, sd, an, need, d₂) else none
  else none

/-- **The description's value of the seven ground functions**: plain functions on data: a test in
named clauses and an effect each (Johnson/Desc/First/Base/Ground.lean). -/
def groundG : Ground L :=
  { newGroup := fun _ => VerifiableInference.Desc.Ground.newGroupP,
    recv := fun p => VerifiableInference.Desc.Ground.recvP p.firstTree,
    admit := fun _ => VerifiableInference.Desc.Ground.admitP,
    join := fun _ => VerifiableInference.Desc.Ground.joinP,
    addRow := fun _ => VerifiableInference.Desc.Ground.addRowP,
    addRows := fun _ => VerifiableInference.Desc.Ground.addRowsP,
    takeMask := fun _ => VerifiableInference.Desc.Ground.takeMaskP }

end Desc.Plain
