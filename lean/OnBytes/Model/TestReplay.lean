-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestReplay.lean: from a record of what a verifier read and drew to the rounds of a
view, for tests that run a check of a sub-proof on recorded messages.

The program does not import this file. Tests of the sub-proofs import it.

A sub-proof speaks to its chain through a few routines: it reads scalars into the open message, and
it closes the message's round and takes what the verifier drew. A record lists these calls in their
order, as words with blanks or ends of lines between them. A number is written in decimal, and an
element of the extension field as its three words. In a round's name '_' stands for a blank.
   read N x..            N scalars join the open message
   sum x                 the sum of a hiding polynomial joins the open message
   answer NAME x         the round NAME is closed; one element is drawn
   point NAME N x..      the round NAME is closed; N elements are drawn
   batch ROWS x          the round BAT-sigma is closed; the drawn element batches ROWS rows
   open x                the same where the number of rows is said later
   rows ROWS             says that number, of the round that was closed last
   trits NAME N t..      the round NAME is closed; N entries -1, 0 or 1 are drawn
   empty NAME            the round NAME is closed; nothing is drawn
   number NAME N         a number noted during the run, stored under a name; not a call
   element NAME x        an element noted during the run, stored under a name; not a call
A message ends only where a round is closed. So several reads and a sum can make one message, and a
round that is closed right after another has an empty message.

Main definitions: Record, parse, ofText, Record.start, Record.number, Record.element,
Record.alterScalar, Record.alterDrawn, rho, sumAt.

The file holds no theorem.
-/
import OnBytes.Iop.Ground

namespace OnBytes.Model.Replay

/-- What has been made of a record so far. -/
structure Record where
  /-- the scalars of the open message, the last one first -/
  sent : List E := []
  /-- the plan's entries of the rounds that are closed -/
  entries : Array Fmt.Entry := #[]
  /-- these rounds as a view has them -/
  rounds : Array Fmt.RoundView := #[]
  /-- the numbers noted during the run -/
  numbers : List (String × Nat) := []
  /-- the elements noted during the run -/
  elements : List (String × E) := []

/-- Closes the open message under a round's name. The round PSC Y draws the challenge of the further
variable of a sumcheck. It is the only round whose entry here says that its element is drawn by the
rule that never gives 0 (drawNZ = 1). -/
def Record.close (p : Record) (name : String) (drawn : List E) (rows : Nat := 0)
    (trits : List Int := []) : Record :=
  let plain := name.replace "_" " "
  { p with
    sent := []
    entries := p.entries.push
      { name := plain, msg := 24 * p.sent.length, drawE := drawn.length,
        drawNZ := if plain == "PSC Y" then 1 else 0, trits := trits.length, rows := rows }
    rounds := p.rounds.push
      { vals := p.sent.reverse.map fun x => Fmt.ItemValue.e x.triple
        drawn := { elems := drawn.map E.triple, poss := [], trits := trits, digest := none } } }

/-- Says how many rows the round that was closed last batches. -/
def Record.rows (p : Record) (rows : Nat) : Record :=
  { p with entries := p.entries.modify (p.entries.size - 1) fun e => { e with rows := rows } }

/-- Reads n elements, three words each, from the head of a list of words. Returns the rest too. -/
def takeE : Nat → List String → Option (List E × List String)
  | 0, ws => some ([], ws)
  | n + 1, a :: b :: c :: t => do
    let x :=
      E.mk3 (UInt64.ofNat (← a.toNat?)) (UInt64.ofNat (← b.toNat?)) (UInt64.ofNat (← c.toNat?))
    let r ← takeE n t
    pure (x :: r.1, r.2)
  | _, _ => none

/-- Reads the words of a record. The first argument bounds the number of calls. -/
def parse : Nat → List String → Record → Option Record
  | _, [], p => some p
  | 0, _, _ => none
  | k + 1, "read" :: n :: t, p => do
    let r ← takeE (← n.toNat?) t
    parse k r.2 { p with sent := r.1.reverse ++ p.sent }
  | k + 1, "sum" :: t, p => do
    let r ← takeE 1 t
    parse k r.2 { p with sent := r.1 ++ p.sent }
  | k + 1, "answer" :: name :: t, p => do
    let r ← takeE 1 t
    parse k r.2 (p.close name r.1)
  | k + 1, "point" :: name :: n :: t, p => do
    let r ← takeE (← n.toNat?) t
    parse k r.2 (p.close name r.1)
  | k + 1, "batch" :: rows :: t, p => do
    let r ← takeE 1 t
    parse k r.2 (p.close "BAT-sigma" r.1 (← rows.toNat?))
  | k + 1, "open" :: t, p => do
    let r ← takeE 1 t
    parse k r.2 (p.close "BAT-sigma" r.1)
  | k + 1, "rows" :: rows :: t, p => do parse k t (p.rows (← rows.toNat?))
  | k + 1, "trits" :: name :: n :: t, p => do
    let n ← n.toNat?
    let v ← (t.take n).mapM (·.toInt?)
    if v.length == n then parse k (t.drop n) (p.close name [] 0 v) else none
  | k + 1, "empty" :: name :: t, p => parse k t (p.close name [])
  | k + 1, "number" :: name :: n :: t, p => do
    parse k t { p with numbers := (name, ← n.toNat?) :: p.numbers }
  | k + 1, "element" :: name :: t, p => do
    let r ← takeE 1 t
    parse k r.2 { p with elements := (name, r.1.headD zeroE) :: p.elements }
  | _, _, _ => none

/-- The words of a text. -/
def wordsOfText (text : String) : List String :=
  ((text.splitOn "\n").flatMap (·.splitOn " ")).filter (· != "")

/-- What a record's text gives. Nothing if it is no record or ends within a message. -/
def ofText (text : String) : Option Record :=
  let ws := wordsOfText text
  (parse ws.length ws {}).filter (·.sent.isEmpty)

/-- What a block starts from if it is run only on the record's rounds. -/
def Record.start (p : Record) : Start := { entries := p.entries.toList, st := {} }

/-- The number that was stored under a name. -/
def Record.number (p : Record) (name : String) : Option Nat := p.numbers.lookup name

/-- The element that was stored under a name. -/
def Record.element (p : Record) (name : String) : Option E := p.elements.lookup name

/-- The rounds, the scalars of all messages, and the elements drawn. -/
def Record.counts (p : Record) : Nat × Nat × Nat :=
  (p.rounds.size, (p.rounds.toList.map (·.vals.length)).sum,
    (p.rounds.toList.map (·.drawn.elems.length)).sum)

/-! ## Altered records -/

/-- The list with f applied to member number k, counted over the lists that part gives for the
rounds in their order. put writes a round's changed list back. -/
def alterIn {α : Type} (part : Fmt.RoundView → List α) (put : Fmt.RoundView → List α → Fmt.RoundView) (f : α → α) :
    Nat → List Fmt.RoundView → List Fmt.RoundView
  | _, [] => []
  | k, r :: rs =>
    let l := part r
    if k < l.length then put r (l.zipIdx.map fun x => if x.2 == k then f x.1 else x.1) :: rs
    else r :: alterIn part put f (k - l.length) rs

/-- The record with 1 added to scalar number k of its messages. -/
def Record.alterScalar (p : Record) (k : Nat) : Record :=
  let f : Fmt.ItemValue → Fmt.ItemValue
    | .e x => .e (addE (E.ofTriple x) oneE).triple
    | g => g
  { p with rounds :=
      (alterIn (·.vals) (fun r l => { r with vals := l }) f k p.rounds.toList).toArray }

/-- The record with 1 added to drawn element number k. -/
def Record.alterDrawn (p : Record) (k : Nat) : Record :=
  { p with rounds :=
      (alterIn (·.drawn.elems) (fun r l => { r with drawn := { r.drawn with elems := l } })
        (fun x => (addE oneE (E.ofTriple x)).triple) k p.rounds.toList).toArray }

/-! ## Comparing long vectors -/

/-- The point at which vectors are compared. -/
def rho : E := E.mk3 3 5 7

/-- The element sum_j rho^j v[j]. Two different vectors of the same length have the same sum only
for a few values of rho, so in a test one element is compared in place of a long vector. rho is
fixed above, not drawn, so that two different vectors agree at it is unlikely but not excluded. -/
def sumAt (v : Array E) : E := v.foldr (fun x s => addE x (mulE rho s)) zeroE

/-! ## Tests -/

-- two reads and a sum are one message; a batching round has an empty one
#guard ((ofText "read 2 1 2 3 4 5 6 read 1 7 8 9\nsum 1 1 1 answer PSC_epsilon 5 5 5\nbatch 8 6 6 6
    read 1 2 2 2 answer PSC_Y 9 9 9 read 1 3 3 3 empty PSC_values number end 6").map fun p =>
  (p.entries.toList.map fun e => (e.name, e.msg, e.drawE, e.drawNZ, e.rows), p.number "end",
    p.rounds.toList.map fun r => ((elemsOf r).map E.triple, r.drawn.elems))) ==
  some ([("PSC epsilon", 96, 1, 0, 0), ("BAT-sigma", 0, 1, 0, 8), ("PSC Y", 24, 1, 1, 0),
      ("PSC values", 24, 0, 0, 0)], some 6,
    [([(1, 2, 3), (4, 5, 6), (7, 8, 9), (1, 1, 1)], [(5, 5, 5)]), ([], [(6, 6, 6)]),
      ([(2, 2, 2)], [(9, 9, 9)]), ([(3, 3, 3)], [])])
-- the rows said later; entries of a matrix; an element noted during the run
#guard ((ofText "trits RNG 3 -1 0 1 open 4 4 4 rows 7 element theta 1 2 3").map fun p =>
  (p.entries.toList.map fun e => (e.name, e.trits, e.drawE, e.rows),
    p.rounds.toList.map (·.drawn.trits), (p.element "theta").map E.triple)) ==
  some ([("RNG", 3, 0, 0), ("BAT-sigma", 0, 1, 7)], [[-1, 0, 1], []], some (1, 2, 3))
-- a message that no round closes, a word that is no call, an element cut short
#guard (ofText "read 1 1 2 3").isNone && (ofText "red 1 1 2 3").isNone && (ofText "sum 1 2").isNone
-- scalar number 2 is in the second message; drawn element number 1 is in the second round
#guard ((ofText "read 2 1 1 1 2 2 2 answer LINE 5 5 5 read 1 3 3 3 answer LINE 6 6 6").map fun p =>
  ((p.alterScalar 2).rounds.toList.map fun r => (elemsOf r).map E.triple,
    (p.alterDrawn 1).rounds.toList.map (·.drawn.elems))) ==
  some ([[(1, 1, 1), (2, 2, 2)], [(4, 3, 3)]], [[(5, 5, 5)], [(7, 6, 6)]])
-- 1 + 2 rho, at rho = 3 + 5 X + 7 X^2
#guard sumAt #[E.mk3 1 0 0, E.mk3 2 0 0] == E.mk3 7 10 14

end OnBytes.Model.Replay
