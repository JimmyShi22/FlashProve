-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Send.lean: the kind K1, sending an encoding with an out-of-domain sample, as a block
of the format in which a file's protocol is written (Johnson/Desc/Block.lean): a place's public
numbers, its rounds, its oracle messages and its tests on the plan.

This file holds definitions only; no theorem is stated.

The block in words. The prover sends the words of a tuple of oracle messages, and with them words
without a sample that belong to later blocks. The verifier sends seeds: a point and a factor each.
The prover answers. Nothing is compared with an answer: for each message and answer a sample row is
laid.

ROUNDS   "SEND seed":   the prover: one root for each tree that holds this place's messages;
                        the verifier: a seeds, each v elements of E and one that is never 0.
         "SEND answer": the prover: the answers, message by message; the verifier: nothing.
         a: the largest number of answers among the messages; v: the largest cube among the sampled
         (Msg.v).
READS    nothing.
DECIDES  send and commit, in this file, call the sending of Johnson/Desc/Sending/SendRow.lean and
         SendCommit.lean, which call the program's plain functions for the cube, the pad and the
         sample row by name. The kind's own decision, which calls none of these, is
         Johnson/Desc/K1/Own.lean. That round 1 shows no item, that round 2 shows just the answers,
         and that each round draws what ROUNDS says, is asked by Block.step (roundsFit) out of
         ROUNDS; the called texts ask it once more.

Main names: Msg, Msg.v; Par, Par.sent, seedEntry, answerEntry, rounds, oracles, before, planOk;
Owing; send (a sending by itself); commit (a segment's later moment, with the sub-proof's arrays).

Par.groups is read by no test of this kind: it is handed on into the tenants' records (oracles).
Where a maker of a Par leaves it empty, a tenant says that it belongs to no group, which is untrue
of a sampled message that joins one.

What is not claimed. That the entries written here are the planner's: no theorem ties them. Which
later draw each of this kind's messages must stand before: that is the matter of the block that
draws. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.Block
import Johnson.Desc.Own.Sent
import Johnson.Desc.Own.Trees
import Johnson.Desc.Sending.SendCommit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First.Send

/-! ## The cube of an oracle message -/

/-- ⌈log₂ n⌉. -/
def clog (n : Nat) : Nat := if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

/-- An oracle message's public numbers: K main rows of 2 ^ logEll entries, over E or over F; Kzk
mask rows of 2 ^ logEllZk entries, over E; its answers. -/
structure Msg where
  K : Nat
  logEll : Nat
  overE : Bool
  Kzk : Nat
  logEllZk : Nat
  answers : Nat

/-- Read off the statement's page. -/
def Msg.of (codes : Codes) (s : OracleShape) : Msg :=
  { K := s.mainRows, logEll := (codes.base.getD s.code default).logEll, overE := s.mainDeg == 3
    Kzk := s.maskRows, logEllZk := (codes.mask.getD s.maskCode default).logEll,
    answers := s.answers }

/-- The index bits of the main table, and of the mask table: the row's bits, then the position's. -/
def Msg.mainBits (m : Msg) : Nat := if m.K == 0 then 0 else clog m.K + m.logEll
def Msg.maskBits (m : Msg) : Nat := if m.Kzk == 0 then 0 else clog m.Kzk + m.logEllZk

/-- v_o: the coordinates that the message reads. With both tables: one more than the larger. -/
def Msg.v (m : Msg) : Nat :=
  if m.K != 0 && m.Kzk != 0 then max m.mainBits m.maskBits + 1 else m.mainBits + m.maskBits

/-! ## What is public at a place -/

/-- The numbers of a place. No entry of a plan and no declared round is among them. -/
structure Par where
  place : Place
  codes : Codes
  /-- the answers to a sample; the number of the first tree that the chain sends -/
  gp : GPar
  /-- the bits of proof of work on the round of the seeds -/
  work : Nat
  /-- the oracle messages announced, as named parts, in the order of sending -/
  parts : List (String × Array OracleNotice)
  /-- for each message, in the order of sending, the groups that it belongs to; none where the list
  is shorter: for the tenants' records alone: no test of this kind reads it -/
  groups : List (List Nat) := []

/-- All messages of the place, in the order of sending. -/
def Par.sent (P : Par) : Array OracleNotice := (P.parts.flatMap (·.2.toList)).toArray

/-- The tuple: the messages that are sampled. -/
def Par.tuple (P : Par) : List OracleShape :=
  (P.sent.toList.map (·.shape)).filter (·.answers != 0)

/-- a: the seeds. -/
def Par.seeds (P : Par) : Nat := P.tuple.foldl (fun a s => max a s.answers) 0

/-- v: the coordinates of a seed's point. -/
def Par.coordinates (P : Par) : Nat := P.tuple.foldl (fun b s => max b (Msg.of P.codes s).v) 0

/-- All answers of the place. -/
def Par.answers (P : Par) : Nat := P.tuple.foldl (fun a s => a + s.answers) 0

/-- The trees that hold the place's messages (Johnson/Desc/Own/Trees.lean: treesMade). WHERE NO
TREES CAN BE LAID: none, in silence HERE: planOk's second clause, "the trees can be laid", refuses
such a place on the plan, before any round is read. -/
def Par.trees (P : Par) : List TreeShape :=
  ((Own.treesMade P.codes P.sent).map (·.shapes.toList)).getD []

/-! ## ROUNDS -/

def seedEntry (P : Par) : Fmt.Entry :=
  { name := "SEND seed", work := P.work, msg := 32 * P.trees.length, roots := P.trees.length,
    drawE := P.seeds * (P.coordinates + 1), drawNZ := P.seeds }

def answerEntry (P : Par) : Fmt.Entry :=
  { name := "SEND answer", msg := 24 * P.answers, answers := P.answers }

def rounds (P : Par) : List Fmt.DeclaredRound := [{ entry := seedEntry P }, { entry := answerEntry P }]

/-- For each root of round 1 the oracle message beneath it: the log-length, the words of a symbol,
and who shares a symbol, in the order of sending. Where no trees can be laid: no root, as in
Par.trees: planOk refuses there. -/
def oracles (P : Par) : List (List VerifiableInference.Desc.Oracle) :=
  let lay := (Own.treesMade P.codes P.sent).getD {}
  [P.trees.zipIdx.map fun (t, i) =>
    { logLength := t.logN, words := t.mainWidth + t.maskWidth
      tenants := (P.sent.toList.zipIdx.filter fun x => lay.tree[x.2]? == some i).map fun x =>
        let s := x.1.shape
        { main := s.mainRows * s.mainDeg, mask := s.maskRows * 3, degree := s.mainDeg
          sampled := s.answers != 0, groups := P.groups.getD x.2 [] } }, []]

/-- FIXED BEFORE THE DRAW: none. The one draw of this kind is its seeds', which stands behind its
own messages by the order inside the round "SEND seed" and IN FRONT of their answers; and the
format's test asks of a sampled message that is named here that its sample has been answered. WHICH
BLOCK's LIST HOLDS EACH OF THIS KIND's MESSAGES BEFORE WHICH LATER DRAW IS NOT HELD BY THIS KIND: it
is the matter of the block that draws. -/
def before : List (Nat × Nat) := []

/-- TESTS ON THE PLAN ALONE: every message has an admitted shape; the trees can be laid; some
message is sampled. -/
def planOk (P : Par) : Bool :=
  P.sent.all (fun n => Own.sentShapeFits P.codes n.shape) && Own.treesCan P.codes P.sent &&
    !P.tuple.isEmpty

/-! ## DECIDES -/

/-- A carried record with the channel's debt: the number of rows that the entry of the round closed
before counts, until it has been compared. -/
structure Owing (S : Type) where
  owed : Option Nat
  held : S

variable {Cl : Type}

/-- **A sending by itself.** The record's own value: the new messages' numbers. -/
def send (P : Par) : Block (Owing (DState (Array Nat))) Cl :=
  { name := "K1: a sending", place := P.place, planOk := planOk P, rounds := rounds P
    oracles := oracles P, before := before, claims := [], after := []
    decide := fun s rs _ => named "K1: the sending refuses"
      ((sendD P.gp s.owed P.sent (seedEntry P) (answerEntry P) s.held rs []).map fun x =>
        { owed := none, held := x.1 }) }

/-- **A segment's later moment**, where the sub-proof commits to arrays. link, moment: the place's,
by the plan; arrays: the numbers of the arrays named; none: the list of arrays has none where the
program unwraps one. -/
def commit (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    Block (Owing (L3.St (DState Unit))) Cl :=
  { name := "K1: a commitment", place := P.place, planOk := planOk P && arrays.isSome
    rounds := rounds P, oracles := oracles P, before := before, claims := [], after := []
    decide := fun s rs _ =>
      let f := s.held.L.check.frame
      -- on the carried record alone: it stands at this place, and announces what ROUNDS says
      if f.link == link && f.moment == moment &&
          ReqFrame.notices (f.atMoment f.moment) == P.sent then
        match arrays with
        | none => .error "K1: the plan names no arrays"
        | some ts =>
          (commitD P.gp s.owed (seedEntry P) (answerEntry P) ts s.held rs).map fun x =>
            { owed := none, held := x }
      else .error "K1: the record does not stand at this place, or announces other messages" }

end VerifiableInference.Desc.K1
