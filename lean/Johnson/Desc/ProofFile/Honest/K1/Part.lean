-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Part.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR THE
HONEST SIDE: the part: one sending with the round that holds its answers: two moves. Definitions
with code; no theorem.

  SendJob       what a caller says of its sending: the place P : K1.Par · the number that the first
                new message gets · which tables ride · the data of the main rows, as a function of
                the input and of Front (the challenges and the rounds shown IN FRONT OF THE PART,
                what was handed on, and the opened columns as the move is handed them:
                Honest/Sum.lean): so both moves lay the same rows at a job whose data does not
                read the columns; at one that does, where both moves are handed the same columns
  stAt          a statement that holds the place's messages at their numbers and nothing else that
                has a table
  treeTables    for each tree of the place its table: the core's written column, word by word
  seedsAt       the seeds, cut off the part's own first challenge as K1's text cuts them
  seedsFit      the part's own first challenge holds just the seeds' elements
  SendJob.rows  the rows at the part's round number n: Front is cut in front of the part: the
                rounds by Seen.front (Honest/Frame.lean), which keeps the opened columns
  sendPart      THE PART: takes dueR P ride; spends and carries nothing; bad and hid: never. A MOVE
                RETURNS AN ERROR, which is an error of the play, where the job does not fit its
                place (sendFits, Honest/K1/Coins.lean) and, at the second move, where the part's own
                challenge does not hold the seeds.
                Move 1 ("SEND seed"): no item; the trees' tables. Move 2 ("SEND answer"): the core's
                answers at the held words
  proverSideOfSending      the part, alone in its row, at P's own place

All that is sent is the core's (Johnson/Prover/Send/Core.lean: col, answers, held); the rows are
Honest/K1/Coins.lean's.

Limits. A job whose data reads Front.seen stands under the condition that the head of
Honest/Sum.lean states of such a job: nothing here holds it. With seen := s.front n a job's data is
handed, in Front.seen.opened, what the move itself was handed in that field, whole; the part reads
the field nowhere. So a job can, by its type, read the opened columns; no job that this folder
builds does. With seen := s.front n, (sendPart J).Blind is not had from the text alone; under
heardOnly it would follow, and no theorem of the library states it, under heardOnly or without.
(Part.Blind, Honest/Blind.lean: the frame's word for a part
none of whose moves depends
on the columns handed to it.
heardOnly: the job's data reads of Front what was heard alone: a field of K1Seated,
Honest/K1/Seated.lean.) A caller whose data hangs on another part's coins (a code switch) has no
seat here: spends and carries are empty. That the answers do not hang on stAt's choice, that a
table's column is the core's column, and every law on a verifier's yes: not here
(Johnson/Prover/Send/ has the core's laws). No simulator. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Coins
import Johnson.Desc.ProofFile.Honest.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt col answers)

variable {V W X : Type}

/-- **What a caller says of its sending.** -/
structure SendJob (W X : Type) where
  P : K1.Par
  /-- the number that the first new message gets: public -/
  first : Nat
  ride : Nat → Option Ride
  data : W → Front X → Nat → Nat → Nat → Option (GF ⊕ GE)

/-- A statement that holds the place's messages at their numbers; in front of them messages without
a row. -/
def stAt (P : K1.Par) (first : Nat) : Statement :=
  stSent { codes := P.codes, groups := #[]
           oracles := Array.replicate first
             { shape := { mainRows := 0, maskRows := 0, answers := 0 } } } P.sent

/-- For each tree of the place: its table. -/
def treeTables (P : K1.Par) (Vr : Nat → Rows) : List Table :=
  P.trees.zipIdx.map fun x =>
    { logLength := x.1.logN, words := x.1.mainWidth + x.1.maskWidth
      sym := fun pos i => toF ((col P Vr x.2 pos).getD i.val 0) }

/-- The seeds, off a challenge. -/
def seedsAt (P : K1.Par) (ds : List Fmt.Drawn) : List (List E × E) :=
  K1.cutSeeds P.coordinates P.seeds (((ds.head?.map (·.elems)).getD []).map E.ofTriple)

/-- The challenge holds just the seeds' elements: each seed its coordinates and a factor. -/
def seedsFit (P : K1.Par) (ds : List Fmt.Drawn) : Bool :=
  ((ds.head?.map (·.elems.length)).getD 0) == P.seeds * (P.coordinates + 1)

/-- The rows, at the part's round number n. Of what the move is handed (s) the job's data gets the
rounds but for the part's own n, and the opened columns whole (Seen.front). -/
def SendJob.rows (J : SendJob W X) (c : Cs (dueR J.P J.ride)) (s : Seen) (t : State W X)
    (n : Nat) : Nat → Rows :=
  rowsR J.P J.ride (J.data t.input
    { heard := t.heard.take (t.heard.length - n), own := t.own
      seen := s.front n }) c

/-- **The part.** -/
def sendPart (J : SendJob W X) : Part V W X :=
  { takes := dueR J.P J.ride, spends := [], carries := []
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves :=
      [⟨fun c s t =>
          if !sendFits J.P J.ride then .error "K1: the job does not fit its place" else
          .ok ⟨[], treeTables J.P (J.rows c.1 s t 0)⟩, fun t => t.own⟩,
       ⟨fun c s t =>
          if !sendFits J.P J.ride then .error "K1: the job does not fit its place" else
          if !seedsFit J.P (t.lately 1) then .error "K1: the challenge does not hold the seeds" else
          .ok
          ⟨(answers J.P (stAt J.P J.first) J.first
              (Johnson.Prover.Send.held (fun _ _ _ => 0) J.first J.P (J.rows c.1 s t 1))
              (seedsAt J.P (t.lately 1))).map fun a => .answer (toE a), []⟩,
        fun t => t.own⟩] }

/-- **The half**: the part, alone in its row, at the place. -/
def proverSideOfSending (J : SendJob W X) : Placed V W X := ⟨J.P.place, [sendPart J]⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.SendJob
#print axioms ProofFile.Honest.K1.stAt
#print axioms ProofFile.Honest.K1.treeTables
#print axioms ProofFile.Honest.K1.seedsAt
#print axioms ProofFile.Honest.K1.seedsFit
#print axioms ProofFile.Honest.K1.SendJob.rows
#print axioms ProofFile.Honest.K1.sendPart
#print axioms ProofFile.Honest.K1.proverSideOfSending
