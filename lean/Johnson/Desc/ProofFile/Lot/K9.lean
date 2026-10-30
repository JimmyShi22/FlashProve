-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Lot/K9.lean: DEFINITIONS WITH CODE; NO THEOREM: what a segment of the proof
file's first chain takes of kind K9 (the batching draw and the one equation), as a lot
(LotCore.lean):
  batch   K9.batch atS p at the batching's place: it is handed the segment's gatherer.
  each    K9.eachAtS: after each list of claims: the window of slots, by the list's name; the number
          of claims of the lookup on the digits.
  tests   the tests after the adding that change nothing: "every sent scalar stands in a claim";
          the counts of the segment's sort. (At a layers' segment K4's list "free-slot" after the
          batching asks the first once more, if K4's numbers are the same plan's: a harmless
          double.)
  own     K9.closeOf p P: the three blocks that close a segment: the one equation (K9), the closing
          (K10), "shut" (K9).
THE PIECES, with n hearing blocks (Johnson/Desc/First/Driver/Chain.lean: closeAddresses): hearing
1 … n · the batching n + 1 · the block that Link.blocksInOrder lays after it n + 2 · the one equation n + 3 ·
the closing n + 4 · shut n + 5 · "cleared" n + 6. So pieceEq = the batching's piece + 2, and K10's
Par.piece = pieceEq + 1.
THE NUMBERS OF A PLACE ARE READ OFF THE DECLARED ROUNDS' STRETCH (rows; work) AND OFF THE FIRST
STATE's FRAME (k; h), as in Lots/Makers.lean: so the test that these blocks' rounds are the plan's
is idle for these numbers.
Limits. Where a number cannot be read, a block that refuses is laid. letters := false: nothing here
reads the request's tokens. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.LotCore
import Johnson.Desc.ProofFile.Places
import Johnson.Desc.ProofFile.Lots.Makers
import Johnson.Desc.First.Batch.CloseAt
import Johnson.Desc.First.Batch.EachAtS
import Johnson.Desc.First.Batch.TestsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (Where SegSort atS)

/-- The places that have rounds, each with its stretch of the declared rounds and the roots counted
in front (Makers.lean: stretched). -/
def k9Stretches (Z : Pub) : List (Spot × List Fmt.DeclaredRound × Nat) :=
  ((spotsOf Z.cuts).map fun ps => stretched ps Z.D.1 0).getD []

/-- K9's numbers at segment l: off the batching's place. xs: k9Stretches Z, MADE ONCE by the caller.
-/
def k9Where (xs : List (Spot × List Fmt.DeclaredRound × Nat)) (l : Nat) : Option Where :=
  (xs.find? fun x =>
      x.1.place.kind == .K9 && !x.1.cuts.isEmpty && x.1.place.link == some l).bind fun x =>
    x.2.1.head?.map fun d =>
      { chain := 1, link := l, piece := x.1.place.piece, pieceEq := x.1.place.piece + 2
        rows := d.entry.rows, work := d.entry.work, sent := x.2.2 }

/-- K10's numbers at segment l: off the closing's place's stretch and the first state's frame. -/
def k10Par (Z : Pub) (xs : List (Spot × List Fmt.DeclaredRound × Nat)) (p : Where) :
    Option VerifiableInference.Desc.First.Close.Par :=
  (xs.find? fun x => x.1.place.kind == .K10 && x.1.place.link == some p.link).bind fun x =>
    (Z.s₀.check.frame.groups[p.link]?).bind fun Gr =>
      match x.2.1 with
      | bat :: _ :: round :: _ =>
        some { link := p.link, piece := p.pieceEq + 1, k := Gr.k, h := Gr.h
               rows := bat.entry.rows, workField := bat.entry.work
               workClose := round.entry.work, sent := List.range x.2.2 }
      | _ => none

/-- The numbers of the segments, each once: off the batching's places: of K9's three places a
segment that one alone has steps (cuts); the one equation's and shut's have none. -/
def k9Links (xs : List (Spot × List Fmt.DeclaredRound × Nat)) : List Nat :=
  xs.filterMap fun x =>
    if x.1.place.kind == .K9 && !x.1.cuts.isEmpty then x.1.place.link else none

/-- The tests behind the adding that turn nothing, at segment l. -/
def k9Tests (Z : Pub) (l : Nat) : Option (S → Except String Unit) :=
  (VerifiableInference.Desc.K9.testsWhere Z.p.X l 0).map fun w => fun s => do
    let part ← VerifiableInference.Desc.K9.there "K9.in-a-segment"
      (VerifiableInference.Desc.K9.tAtS.get? s)
    VerifiableInference.Desc.K9.freeSlot w.2.2.filled part.merge part.F
    VerifiableInference.Desc.K9.countsHold (VerifiableInference.Desc.K9.countsAt w.1 w.2.1) s

/-- **Kind K9's lot.** Where a number cannot be read a block that refuses aloud is laid. THE
TABLES OFF THE PLAN ARE MADE ONCE, IN FRONT OF THE RECORD: the stretches; each segment's numbers. -/
def k9Ninth (Z : Pub) : Lot :=
  let xs := k9Stretches Z
  let ws : List (Nat × Option Where) := (k9Links xs).map fun l => (l, k9Where xs l)
  let close : List (Block S Unit) :=
    ws.flatMap fun w =>
      match w.2.bind fun p => (k10Par Z xs p).map fun P => (p, P) with
      | some (p, P) => VerifiableInference.Desc.K9.closeOf p P
      | none =>
        [refuser s!"link {w.1}: the closing" ⟨1, some w.1, 0, .K10⟩ "K9's or K10's numbers"]
  { name := "K9: the batching at the gatherer; each; tests; the closing as three blocks"
    letters := false
    own := fun _ => close
    batch := fun _ a =>
      match a.kind, a.link with
      | .K9, some l =>
        ((ws.lookup l).bind id).bind fun p =>
          if p.piece == a.piece then
            some fun g => VerifiableInference.Desc.K9.batch atS p g
          else none
      | _, _ => none
    each := fun _ l =>
      (VerifiableInference.Desc.K9.testsWhere Z.p.X l 0).map fun w =>
        VerifiableInference.Desc.K9.eachAtS w.1
    tests := fun _ l => k9Tests Z l
    still := [] }

end ProofFile
