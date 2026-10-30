-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/FrameToy.lean: controls for Honest/Frame.lean, Honest/Rows.lean,
Honest/Side.lean and Honest/Rule.lean: a toy prover, toy books of coins and toy simulators for the
toy description `BlockToy.F` (Johnson/Desc/BlockToy.lean). Definitions and `#guard` lines, as in
that file; no theorem.

The lines that begin with `#guard` are tests, checked by evaluation: Lean's evaluator runs each of
them when the file is compiled, and the build fails if one is false. The kernel does not check them,
and they prove nothing.

What the lines check. At the example's own challenges and at coins that are 0 the honest run's three
views are the example's own `v₁`, `v₂`, `v₃`, and the description accepts.
The input's parts: the trace is computed from the instance; an instance without a trace; the stored
column is computed from the word of `Rc` (the stored tables' pads and encoding randomness). The key:
a prover's side of the shared chain reads it; it is computed from the instance by the prover's
function; with another function it does not arrive. In range: an index out of range; a named element
out of range.
Coins: each of the five coins, changed alone, changes one item or one column, at its own place or at
the place that the book's entry names, and nothing else in the three views; coins on which the
decision does not depend: accepted at each, and other views; an element is put into a word below the
prime; a part that takes a coin too many or too few, of either field, gives an error; one that asks
a coin beyond its count is at fault; one that is typed at other entries than the book gives it gives
an error; two blocks of one count stated the other way round give an error by their names. The book:
each of its eleven tests fails once; a coin that is spent twice; a block that is spent, carried
before its spender, by its spender, and after it; a block of the shared chain that is spent outside
it. The cut: a list that is cut otherwise than the book has it; a place without a cut.
Stops: one of each kind; one on a part's own last challenge; three runs that return an error, in
three classes, have `none` for their outcome; the stops of the second chain are given eight
challenges before the part, not eleven.
The errors of `run`: a prover's side left out; another number of rounds; another shape; a prover's
side at no place of its chain; two at one place; two sub-protocols at one place; too few challenges;
a sealing round that draws. Each chain's state: what a prover's side of the first chain passes on,
and one of the shared chain, reach the second chain's last prover's side.
The rows (Honest/Rows.lean), with a stored run to fall back on: none, some, all of the prover's
sides; negative rows coin by coin: a place's own coin (another put in its place), the word of `Rc`
(which row 2 does not see and row 3 does); a changed word of the index; a stored run with a column
too few or too many; a place at which nothing is compared; the printout's two notes.
Parts: the prover's side at `look` as a list of two parts, as the two joined by `Part.andThen`, and
as the one part written by hand: the same views at the same coins, and the same stops; two parts
that each have a coin of either field and spend a block, as a list and joined: the same views, at
coins that are all different, and other views where two coins change places; a book that has a row,
or an entry, for a part that the prover's side does not have; a list of two at the book of one. A
block from a part to a later part of the same place: it arrives; the other part of the list, typed
to spend it, gives an error, and so does the spender that is not typed to; an entry that runs
backwards inside a place. One toy part, placed twice by `Part.lift`: each placement reads its own
last challenge and stops on its own; the two placements the other way round; the lens on what is
passed on.
A part's section of a run; what a simulator is given of the run before its part; that it holds a
column for every read of the part's own rounds: the run's own passes, at another challenge it fails,
and so does one that lists another position; three sides: one of one plain part, one of one part
that is not plain, one of two parts; a part played alone shows what the run shows at its address;
`Part.stopAt` and `Side.stopAt` say where it stops and by which stop; a toy simulator outputs the
same as its part at coins that are chosen to fit, not at others, and `none` where the first stop
stops the part: evaluations at fixed coins, no lemma. A simulator that reads what comes before. The
shares that parts state of their stops, added up.
The hypotheses of a statement about lists of parts (Honest/Rule.lean): the one silent set says what
`stopOf` says, and still says it where a fault comes first; `midAt`, `midSharedAt` (`Owed` takes
`midAtW`, `midSharedAtW`: not evaluated here) and `carriedAt` return, in four numbers, what this
file had written by hand; the example's four prover's sides as one value of `Sides`, whose prover
has the outcome of the example's prover; two toy examples that fail these hypotheses: a bound that
reads challenges, and a condition at the entry that ties the index to the instance: the first
returns false at a run's own challenges, the second at what `midAt` returns, at a list outside the
silent set.
A toy list of three parts, at a description in which the owner's table is read at one position: an
owner, whose column is read after the spender; the spender of one of its coins; a carrier after the
spender, which puts both of the owner's coins under a coin of its own. The book passes all its tests
and the description accepts; the run reads of the owner's table just one position, and the owner's
coins are added at every position; which entries `Good.fresh` reads for which part; and, for each of
the three, what it shows at coins that are chosen so that the sum stays: evaluations at fixed coins,
no lemma: that the list meets `Good` is not said.

What no line can check. That `outcome` forgets, that `Move.hand`, `Part.bad` and `Part.hid` are
given no coin, and that a part's moves are given the part's own three kinds of coins and no other
part's, is their type: a definition that puts a coin there does not compile, so it cannot be in this
file.

Limits.
  * A toy example: toy prover's sides, none of a kind of the protocol.
  * No part of this file reads the field `opened`, and no line has a state whose field holds a
    column. `midAt` and `midSharedAt` return a state whose field is `none` (two lines test it); that
    `run` hands no columns either is read off Honest/Frame.lean, not tested. `mid₁` and `mid₄₉`,
    which lines hold against these two functions, have `none`, and so have two states that are
    written in place. A state that is set beside a simulator's output has the field that the
    simulator's `front` holds. `mid₀` and `midZ`, at `none₀`, have `some []` (three lines test it:
    at `mid₀` at two lists of rounds, at `midZ` at one; at every `pre` it is read, not tested).
    `mid₁At` and the state beside `frontA` have the frame's own term,
    `front.opened (readsBefore pre front)`, at the `pre` that `Owed.good` lays at the place
    (`preLook`, `preAsk`, and the like in `Fz`); a line pins each value: `some []`. So these pairs
    meet the premise of `Good.exact` on the field. The two pairs of `lookU₁` at `none₀` still miss
    `m.seen = front.seen`. The lines say nothing where a column has been opened (`runC`, `midAtW`).
  * Of the definitions of Honest/Frame.lean, Honest/Side.lean and Honest/Rule.lean no line evaluates
    `Seen.front`, `Seen.plus`, `Mid.bare` or `Mid.took`; `Before.opened`, `readsBefore` and, through
    them, `Before.drawnOf` are evaluated at `none₀`, at `frontA 9` and at one `Before` written in
    place: each value is `some []`, so no read is made there, and `Before.colAt` is called at no
    read.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Rows
import Johnson.Desc.ProofFile.Honest.Rule
import Johnson.Desc.BlockToy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Toy
open VerifiableInference.Desc (Place Block FileDescription need)
open VerifiableInference.Desc.BlockToy (F St v₁ v₂ v₃ orc look table send₃ peek peekAt ask rvE tree₃
  thePlans drawD drawT sendR)
open OnBytes.Slice (toF toE ofF ofE)

/-! ## The toy example's parameters -/

/-- What all requests share: the shared chain's table and answer. -/
structure Wit₀ where
  a : Nat → UInt64
  ans : UInt64

/-- A request's trace: the second chain's table and last word. -/
structure Trace where
  b : Nat → UInt64
  last : UInt64

def w₀ : Wit₀ := ⟨fun p => if p == 4 then 100 else if p == 6 then 4 else 0, 9⟩

/-- `Rc` (the stored tables' pads and encoding randomness) is one word here; the instance is a
number, as in `BlockToy.F`. -/
abbrev L : Type := Local Wit₀ UInt64 Nat Trace

/-- What the shared chain's prover's sides are given as their input: the key is one word. -/
abbrev L₀ : Type := Common Wit₀ UInt64 UInt64

def pHear : Place := ⟨1, some 0, 1, .K4⟩
def pLook : Place := ⟨2, none, 0, .K2⟩
def pSend : Place := ⟨3, some 0, 4, .K1⟩
def pAsk : Place := ⟨3, some 0, 6, .K10⟩

/-- The first part at each of the four places. -/
def sHear : Addr := ⟨pHear, 0⟩
def sLook : Addr := ⟨pLook, 0⟩
def sSend : Addr := ⟨pSend, 0⟩
def sAsk : Addr := ⟨pAsk, 0⟩

def dE (x : UInt64) : Fmt.Drawn := ⟨[(x, 0, 0)], [], [], none⟩
def dP (p : Nat) : Fmt.Drawn := ⟨[], [p], [], none⟩
def d0 : Fmt.Drawn := ⟨[], [], [], none⟩

/-! ## The book and the coins -/

def toAsk₁ : Ahead := ⟨"hear to ask", sHear, ⟨0, 0⟩, ⟨1, 0⟩, sAsk, true⟩
def toAsk₂ : Ahead := ⟨"look to ask", sLook, ⟨1, 0⟩, ⟨1, 0⟩, sAsk, false⟩
def toAsk₃ : Ahead := ⟨"send to ask", sSend, ⟨0, 0⟩, ⟨1, 0⟩, sAsk, true⟩

/-- The three blocks by name and count, as the part that is given them states them. -/
abbrev nHear : String × Due := ("hear to ask", ⟨1, 0⟩)
abbrev nLook : String × Due := ("look to ask", ⟨1, 0⟩)
abbrev nSend : String × Due := ("send to ask", ⟨1, 0⟩)

/-- The cut where each of the four prover's sides is a list of one part. -/
def cuts₁ : List (Place × List Nat) := [(pHear, [2]), (pLook, [2]), (pSend, [1]), (pAsk, [1])]
/-- The same with the two rounds of `look` cut in two. -/
def cuts₂ : List (Place × List Nat) := [(pHear, [2]), (pLook, [1, 1]), (pSend, [1]), (pAsk, [1])]

/-- The example's book: `hear` has one coin, `look` two and one of the extension field, `send` one.
`ask` has none of its own: it spends the coin of `hear` and that of `send`, and carries the second
coin of `look`, which is owned in the shared chain. -/
abbrev B : ProverCoinCounts :=
  { first := [(sHear, ⟨1, 0⟩)], shared := [(sLook, ⟨2, 1⟩)], second := [(sSend, ⟨1, 0⟩)]
    ahead := [toAsk₁, toAsk₂, toAsk₃], cuts := cuts₁ }

/-- Coins from words. -/
def mk (d : Due) (f e : Nat → UInt64) : Cs d :=
  ⟨fun i => toF (f i.1), fun i => toE (e i.1, 0, 0)⟩

/-- A run's coins: that of `hear`; the two of `look`; that of `look` in the extension field; that of
`send`. -/
def coins (h l₀ l₁ lE s : UInt64) : Coins B :=
  ⟨(mk ⟨1, 0⟩ (fun _ => h) fun _ => 0, ()),
    (mk ⟨2, 1⟩ (fun i => if i == 0 then l₀ else l₁) fun _ => lE, ()),
    (mk ⟨1, 0⟩ (fun _ => s) fun _ => 0, ())⟩

def zero : Coins B := coins 0 0 0 0 0

/-! ## The prover's sides -/

/-- A move that sends nothing. -/
def quiet {C W : Type} (hand : State W Nat → Nat) : Move C W Nat :=
  ⟨fun _ _ _ => .ok ⟨[], []⟩, hand⟩

/-- The prover's side for `BlockToy.hear` in the first chain: it sends nothing, as the sub-protocol
declares, and passes on 40 and the number of challenges that it has heard: 42. A list of one part:
what a kind that needs no cut has to write. -/
def hearH : Placed L L Nat :=
  ⟨pHear, [{ takes := ⟨1, 0⟩, spends := [], carries := []
             bad := fun _ _ => none, hid := fun _ _ _ => none
             badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
             moves := [quiet fun t => t.own, quiet fun t => 40 + t.heard.length] }]⟩

/-- The prover's side for `BlockToy.look`, as one part, typed at the count d: a table whose word at
position 4 is the index's plus the part's coin number i, and the number 7 passed on; then the answer
plus the key plus the part's coin of the extension field, if just one round has been shown: the
shared chain's own first. It stops where the first of its own challenges is the element 13, or the
second the position 13: that one is its own last. -/
def lookPart (d : Due) (i : Nat := 0) : Part Empty L₀ Nat :=
  { takes := d, spends := [], carries := []
    bad := fun _ own =>
      if own.head? == some (dE 13) then some "the first challenge is 13"
      else if own[1]? == some (dP 13) then some "the second challenge is 13" else none
    hid := fun v _ _ => nomatch v
    badShare := ⟨1, 8⟩, hidShare := ⟨0, 1⟩
    moves := [
      ⟨fun c _ t => (c.1.fAt i).map fun k =>
          ⟨[], [⟨3, 1, fun p _ =>
            if p == 4 then toF (t.input.w₀.a p) + k else toF (t.input.w₀.a p)⟩]⟩,
        fun _ => 7⟩,
      ⟨fun c s t => (c.1.eAt 0).map fun k =>
          ⟨[.answer (if s.rounds.length == 1 then
              ⟨toF t.input.w₀.ans + toF t.input.key + k.c0, k.c1, k.c2⟩
            else toE (0, 0, 0))], []⟩,
        fun t => t.own⟩] }

def lookAt (d : Due) (i : Nat := 0) : Placed Empty L₀ Nat := ⟨pLook, [lookPart d i]⟩

def lookH : Placed Empty L₀ Nat := lookAt ⟨2, 1⟩

/-- The prover's side for `BlockToy.send₃`: the trace's table; its coin is at position 1, which is
not read. -/
def sendPart : Part L L Nat :=
  { takes := ⟨1, 0⟩, spends := [], carries := []
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [⟨fun c _ t => (c.1.fAt 0).map fun k =>
        ⟨[], [⟨2, 1, fun p _ => if p == 1 then k else toF (t.input.trace.b p)⟩]⟩,
      fun t => t.own⟩] }

def sendH : Placed L L Nat := ⟨pSend, [sendPart]⟩

/-- The prover's side for `BlockToy.ask`: an element whose three coordinates are the trace's last
word plus the second coin of `look` (unless `drops`), the coin of `send`, and the coin of `hear`: if
what was passed on is 42 + 7, and all eleven challenges so far have been heard and all eleven rounds
shown: four of the first chain, three of the shared, four of the second. It stops where the trace's
last word is 5; and, if `loc` is given, where its stops are given another number of challenges than
that before the part. -/
def askPart (drops : Bool := false) (loc : Option Nat := none) : Part L L Nat :=
  { takes := ⟨0, 0⟩, spends := [nHear, nSend], carries := [nLook]
    bad := fun front _ =>
      if loc.any fun n => n != front.length then some "another number of challenges" else none
    hid := fun w _ _ => if w.trace.last == 5 then some "the trace's last word is 5" else none
    badShare := if loc.isSome then ⟨1, 1⟩ else ⟨0, 1⟩, hidShare := ⟨1, 1⟩
    moves := [⟨fun c s t =>
        (c.2.1.1.fAt 0).bind fun kH => (c.2.1.2.1.fAt 0).bind fun kS =>
        (c.2.2.1.fAt 0).map fun kL =>
          ⟨[.e (if t.own == 49 && t.heard.length == 11 && s.rounds.length == 11 then
              ⟨if drops then toF t.input.trace.last else toF t.input.trace.last + kL, kS, kH⟩
            else toE (0, 0, 0))], []⟩,
      fun t => t.own⟩] }

def askAt (drops : Bool := false) (loc : Option Nat := none) : Placed L L Nat :=
  ⟨pAsk, [askPart drops loc]⟩

def askH : Placed L L Nat := askAt

/-- A prover's side at the place of `ask` that is typed at other entries and sends a fixed element.
-/
def askTyped (sp ca : List (String × Due)) : Placed L L Nat :=
  ⟨pAsk, [{ takes := ⟨0, 0⟩, spends := sp, carries := ca
            bad := fun _ _ => none, hid := fun _ _ _ => none
            badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
            moves := [⟨fun _ _ _ => .ok ⟨[.e (toE (1, 0, 0))], []⟩, fun t => t.own⟩] }]⟩

/-- The example's prover. A stored column is 7 and the word of `Rc`. A request's trace is computed
from the instance: its last word is the instance less 2136; the instance 0 has none. The key is
the instance's ten thousands: 0 at the example's own instance. In range is an index whose answer is
not 0. -/
def P : Prover Wit₀ UInt64 Nat UInt64 Trace Nat Nat :=
  { stored := fun _ rc _ _ => some [toF 7, toF rc]
    trace := fun _ x =>
      if x == 0 then none else some ⟨fun p => if p == 2 then 6 else 0, UInt64.ofNat (x - 2136)⟩
    key := fun x => UInt64.ofNat (x / 10000)
    inRange := fun w => w.ans != 0
    dummy := ⟨fun _ => 0, 1⟩
    own₀ := 0, ownShared₀ := 0
    first := [hearH], shared := [lookH], second := [sendH, askH]
    meet := fun x s => x + s.own }

/-- A prover without a prover's side. -/
def P₀ : Prover Wit₀ UInt64 Nat UInt64 Trace Nat Nat :=
  { P with first := [], shared := [], second := [] }

/-- The challenges of the example's own views; the first chain's last is the sealing round's. -/
def ρ : Draws := ⟨[dE 1, dE 10, dE 2, d0], [dE 5, dP 12, dP 3], [dE 5, dE 3, d0, dP 6, d0]⟩

/-- The example's own three views, as a stored run: its coins are `zero`. -/
def U : Views := (v₁, v₂, v₃)

/-- A stored run whose coins are `coins 0 0 5 0 0`. -/
def U₅ : Views := (v₁, v₂, v₃ (last := rvE 6))

/-- The shared chain's view with another answer. -/
def vA (x : UInt64) : Fmt.View :=
  ⟨[⟨[], dE 5⟩, ⟨[.answer (x, 0, 0)], dP 12⟩, ⟨[], dP 3⟩], [(0, 4, [100]), (65536, 3, [7, 7])]⟩

/-- Whether a run's views are these three. -/
def shows (r : Except Refusal Run) (a b c : Fmt.View) : Bool :=
  match r with
  | .ok x => sameView x.views.1 a && sameView x.views.2.1 b && sameView x.views.2.2 c
  | .error _ => false

/-- The four rows in one line, or the error. -/
def line (r : Except String Rows) : String :=
  match r with
  | .ok R => R.short
  | .error e => e

/-- The run at an instance and coins, with nothing to fall back on. -/
def at_ (x : Nat) (c : Coins B) : Except Refusal Run := run F B P w₀ 7 x c ρ none

/-! ## The honest run -/

-- with nothing to fall back on: accepted, and the three views are the example's own
#guard say F B P w₀ 7 2137 zero ρ none == "yes"
#guard shows (at_ 2137 zero) v₁ v₂ v₃
#guard lacking F.shared.blocksInOrder P.shared == [] && lacking F.second.blocksInOrder P.second == []
#guard strays F.first.blocksInOrder P.first == [] && strays F.shared.blocksInOrder P.shared == [] &&
  strays F.second.blocksInOrder P.second == []
#guard B.word F == none
#guard (drawsOf U).same ρ
-- the challenges are such as the rounds can draw; and are not: a word not below the prime; a count;
-- a position out of the range; a seed's factor that is 0
#guard ρ.due F
#guard !({ ρ with first := [dE 1, dE 0xFFFFFFFF00000001, dE 2, d0] } : Draws).due F
#guard !({ ρ with first := [dE 1, dE 10, d0, d0] } : Draws).due F
#guard !({ ρ with shared := [dE 5, dP 16, dP 3] } : Draws).due F
#guard !({ ρ with shared := [dE 0, dP 12, dP 3] } : Draws).due F
-- a sealed digest: at a sealing round a challenge may show one; at another round not; the first
-- chain's own sealing round has the empty challenge, as `run` asks
#guard drawFit { entry := { name := "SEAL" } } ⟨[], [], [], some (ByteArray.mk #[1])⟩
#guard drawFit { entry := { name := "SEAL" } } d0
#guard !drawFit { entry := { name := "CS" } } ⟨[], [], [], some (ByteArray.mk #[1])⟩
#guard !({ ρ with first := [dE 1, dE 10, dE 2, ⟨[], [], [], some (ByteArray.mk #[1])⟩] } :
  Draws).due F

/-! ## The input's parts -/

-- another instance: the description rejects; the trace is computed from the instance: the last item
#guard say F B P w₀ 7 2138 zero ρ none == "no: the ends fail the last test"
#guard shows (at_ 2138 zero) v₁ v₂ (v₃ (last := rvE 2))
-- an instance without a trace
#guard say F B P w₀ 7 0 zero ρ none == "the honest side: the request has no trace"
#guard stopOf F B P w₀ 7 0 zero ρ == some .noTrace
-- another word of `Rc`: the stored column is computed from it
#guard say F B P w₀ 8 2137 zero ρ none == "no: the shared chain: refused at table: table.words"
-- the key: the prover's side at `look`, in the shared chain, adds it to its answer. At the instance
-- 12137 the key is 1: the answer is 10. With a function that is 0 everywhere it is 9, as at 2137
#guard shows (at_ 12137 zero) v₁ (vA 10) (v₃ (last := rvE 10001))
#guard shows (run F B { P with key := fun _ => 0 } w₀ 7 12137 zero ρ none) v₁ v₂
  (v₃ (last := rvE 10001))
-- in range: an index out of range: an error of a class of its own, and `none`; a named element out
-- of range
#guard say F B P { w₀ with ans := 0 } 7 2137 zero ρ none ==
  "the honest side: what all requests share is out of range"
#guard stopOf F B P { w₀ with ans := 0 } 7 2137 zero ρ == some .noIndex
#guard (outcome F B P { w₀ with ans := 0 } 7 2137 zero ρ).isNone
#guard say F B { P with dummy := ⟨fun _ => 0, 0⟩ } w₀ 7 2137 zero ρ none ==
  "the honest side: the named member of the range is out of range"
-- no stored column, and nothing to fall back on
#guard say F B { P with stored := fun _ _ _ _ => none } w₀ 7 2137 zero ρ none ==
  "the honest side: a column is read of a table that is not at hand"
-- a stored column of another width than the round declares: an error; also with a stored run to
-- fall back on: it is not replaced silently
#guard say F B { P with stored := fun _ _ _ _ => some [toF 7] } w₀ 7 2137 zero ρ none ==
  "the honest side: a column has another width than the round states"
#guard say F B { P with stored := fun _ _ _ _ => some [toF 7] } w₀ 7 2137 zero ρ (some U) ==
  "the honest side: a column has another width than the round states"
-- a stored run's own column of another width, where the prover has none
#guard say F B { P with stored := fun _ _ _ _ => none } w₀ 7 2137 zero ρ
    (some (v₁, v₂ [(0, 4, [100])] [(65536, 3, [7])], v₃)) ==
  "the honest side: a column has another width than the round states"
-- two errors at once: a stored run with other challenges, and what all requests share out of range:
-- the second is reported: the test on a stored run's challenges comes after those of `ready`
#guard say F B P { w₀ with ans := 0 } 7 2137 zero { ρ with second := [dE 5, dE 4, d0, dP 6, d0] }
    (some U) == "the honest side: what all requests share is out of range"

/-! ## Coins -/

-- the first coin of `look`: the second view differs, the old instance is rejected, another accepted
#guard shows (at_ 2137 (coins 0 2 0 0 0)) v₁ (v₂ [(0, 4, [102])]) v₃
#guard say F B P w₀ 7 2137 (coins 0 2 0 0 0) ρ none == "no: the ends fail the last test"
#guard say F B P w₀ 7 2139 (coins 0 2 0 0 0) ρ none == "yes"
-- coins on which the decision does not depend: accepted at each, and the views differ: the block
-- that `ask` carries of the coins of `look`; the blocks that it spends of those of `hear` and of
-- `send`; the coin of `look` in the other field
#guard say F B P w₀ 7 2137 (coins 9 0 5 3 4) ρ none == "yes"
#guard shows (at_ 2137 (coins 0 0 5 0 0)) v₁ v₂ (v₃ (last := rvE 6))
#guard shows (at_ 2137 (coins 9 0 0 0 0)) v₁ v₂ (v₃ (last := ⟨[.e (1, 0, 9)], d0⟩))
#guard shows (at_ 2137 (coins 0 0 0 0 4)) v₁ v₂ (v₃ (last := ⟨[.e (1, 4, 0)], d0⟩))
#guard shows (at_ 2137 (coins 0 0 0 3 0)) v₁ (vA 12) v₃
-- a word is computed from an element: a coin that is the prime less 1 and a word 100 give 99
#guard shows (at_ 2137 (coins 0 0xFFFFFFFF00000000 0 0 0)) v₁ (v₂ [(0, 4, [99])]) v₃
-- a part that takes a coin too many, or too few: an error
#guard say F B { P with shared := [lookAt ⟨3, 1⟩] } w₀ 7 2137 zero ρ none ==
  "the honest side: look: part 0: it takes more or fewer coins than the book has for it"
#guard say F B { P with shared := [lookAt ⟨1, 1⟩] } w₀ 7 2137 zero ρ none ==
  "the honest side: look: part 0: it takes more or fewer coins than the book has for it"
#guard say F B { P with shared := [lookAt ⟨2, 0⟩] } w₀ 7 2137 zero ρ none ==
  "the honest side: look: part 0: it takes more or fewer coins than the book has for it"
#guard say F B { P with shared := [lookAt ⟨2, 2⟩] } w₀ 7 2137 zero ρ none ==
  "the honest side: look: part 0: it takes more or fewer coins than the book has for it"
-- a part that states the book's count and asks a coin beyond it: a fault, no value takes its place
#guard say F B { P with shared := [lookAt ⟨2, 1⟩ 2] } w₀ 7 2137 zero ρ none ==
  "the honest side: look: a coin is asked beyond the count"
-- a part that is typed at another count than an entry has; at another number of entries
#guard say F B { P with second := [sendH, askTyped [("hear to ask", ⟨2, 0⟩), nSend] [nLook]] } w₀ 7
    2137 zero ρ none ==
  "the honest side: ask: part 0: hear to ask: the part is typed at another count than the entry has"
#guard say F B { P with second := [sendH, askTyped [nHear] [nLook]] } w₀ 7 2137 zero ρ none ==
  "the honest side: ask: part 0: it is typed at another number of entries than the book hands it"
#guard say F B { P with second := [sendH, askTyped [nHear, nSend] []] } w₀ 7 2137 zero ρ none ==
  "the honest side: ask: part 0: it is typed at another number of entries than the book hands it"
#guard say F B { P with second := [sendH, askTyped [nHear, nSend] [nLook]] } w₀ 7 2137 zero ρ
    none == "yes"
-- two blocks of one count, stated the other way round: the counts fit, the names do not: an error
#guard say F B { P with second := [sendH, askTyped [nSend, nHear] [nLook]] } w₀ 7 2137 zero ρ
    none ==
  "the honest side: ask: part 0: hear to ask: the part names another run here: send to ask"
-- an entry's coins are available though the owner's prover's side is not written: the coin of
-- `hear` is shown by `ask` (the 42 that the prover's side at `hear` would pass on is put in at the
-- start)
#guard shows (run F B { P with first := [], own₀ := 42 } w₀ 7 2137 (coins 9 0 0 0 0) ρ none) v₁ v₂
  (v₃ (last := ⟨[.e (1, 0, 9)], d0⟩))

/-! ## The tests on the book -/

#guard ({ B with first := [(sLook, ⟨1, 0⟩)] } : ProverCoinCounts).word F ==
  some "a row stands at no place of its chain"
#guard ({ B with second := [(sSend, ⟨1, 0⟩), (sSend, ⟨1, 0⟩)] } : ProverCoinCounts).word F ==
  some "a part has two rows"
#guard ({ B with ahead := [{ toAsk₂ with start := ⟨2, 0⟩ }] } : ProverCoinCounts).word F ==
  some "an entry's run is not within its owner's count"
#guard ({ B with ahead := [⟨"back", sAsk, ⟨0, 0⟩, ⟨0, 0⟩, sSend, true⟩] } : ProverCoinCounts).word F ==
  some "an entry's spender does not stand behind its owner"
#guard ({ B with ahead := [{ toAsk₁ with spender := sLook }] } : ProverCoinCounts).word F ==
  some "the shared chain is handed a coin of the first chain"
-- a coin that is spent twice
#guard ({ B with ahead := B.ahead ++ [{ toAsk₁ with name := "again", spender := sSend }] } :
  ProverCoinCounts).word F == some "a coin stands in two entries that spend it"
-- the eighth test: the block that `ask` spends, carried by a part before `ask`; by `ask` itself;
-- and by a part after `ask`, which passes
#guard ({ B with ahead := B.ahead ++ [{ toAsk₁ with name := "again", spender := sSend
                                                    once := false }] } : ProverCoinCounts).word F ==
  some "a coin that a part spends is handed to a part in front of it, or to itself as carried"
#guard ({ B with ahead := B.ahead ++ [{ toAsk₁ with name := "again", once := false }] } :
  ProverCoinCounts).word F ==
  some "a coin that a part spends is handed to a part in front of it, or to itself as carried"
#guard ({ B with ahead := B.ahead ++ [{ toAsk₁ with name := "again"
                                                    spender := ⟨⟨3, some 0, 7, .frame⟩, 0⟩
                                                    once := false }] } : ProverCoinCounts).word F == none
-- the ninth test: a block that is owned in the shared chain and spent outside it; carried there, as
-- in B, it passes
#guard ({ B with ahead := [{ toAsk₂ with once := true }] } : ProverCoinCounts).word F ==
  some "a coin of the shared chain is spent outside it"
#guard B.word F == none
-- the tenth: a cut at no place; one that does not add up; one with a part without a round; twice
#guard ({ B with cuts := [(⟨1, none, 77, .frame⟩, [])] } : ProverCoinCounts).word F ==
  some "a cut stands at no place, stands twice, has a part without a round or does not add up"
#guard ({ B with cuts := [(pLook, [1])] } : ProverCoinCounts).word F ==
  some "a cut stands at no place, stands twice, has a part without a round or does not add up"
#guard ({ B with cuts := [(pLook, [2, 0])] } : ProverCoinCounts).word F ==
  some "a cut stands at no place, stands twice, has a part without a round or does not add up"
#guard ({ B with cuts := [(pLook, [2]), (pLook, [1, 1])] } : ProverCoinCounts).word F ==
  some "a cut stands at no place, stands twice, has a part without a round or does not add up"
-- the eleventh: two entries have one name
#guard ({ B with ahead := B.ahead ++ [{ toAsk₂ with spender := sSend }] } : ProverCoinCounts).word F ==
  some "two entries bear one name"
/-- `look` with a tenant of one mask word. -/
def lookM : Block St Nat :=
  { look [(3, 1)] true () with oracles := [[⟨3, 1, [⟨0, 1, 1, true, []⟩]⟩], []] }
#guard maskWords lookM == 1 && maskWords (look [(3, 1)] true ()) == 0
#guard B.word (F (shared := some [lookM])) == none
#guard ({ B with shared := [], ahead := [toAsk₁, toAsk₃] } : ProverCoinCounts).word
  (F (shared := some [lookM])) == some "a place states more mask words than its parts have coins"
/-- The book with the coin of `hear` spent twice. Its tables are B's, so B's coins fit it. -/
abbrev B₂ : ProverCoinCounts :=
  { B with ahead := B.ahead ++ [{ toAsk₁ with name := "again", spender := sSend }] }
#guard say F B₂ P w₀ 7 2137 (⟨zero.first, zero.shared, zero.second⟩ : Coins B₂) ρ none ==
  "the honest side: the book: a coin stands in two entries that spend it"

/-! ## Stops, and a run's outcome -/

/-- Challenges at which `look` stops. -/
def ρ₁₃ : Draws := { ρ with shared := [dE 13, dP 12, dP 3] }
#guard say F B P w₀ 7 2137 zero ρ₁₃ none ==
  "the honest side stops (Bad): look: the first challenge is 13"
#guard say F B P w₀ 7 2141 zero ρ none ==
  "the honest side stops (Hid): ask: the trace's last word is 5"
#guard stopOf F B P w₀ 7 2137 zero ρ₁₃ == some .bad && stopOf F B P w₀ 7 2141 zero ρ == some .hid &&
  stopOf F B P w₀ 7 2137 zero ρ == none
-- a stop is asked after a part's last challenge too: `look` stops on its own second
#guard say F B P w₀ 7 2137 zero { ρ with shared := [dE 5, dP 13, dP 3] } none ==
  "the honest side stops (Bad): look: the second challenge is 13"
-- a run's outcome. That it forgets an error's class and words, and that a stop is computed without
-- the run's coins, are types, which no line can test. What these lines check: each of three runs
-- that return an error, in three classes, has `none` for its outcome; the honest run has its views
#guard (outcome F B P w₀ 7 2137 zero ρ₁₃).isNone && (outcome F B P w₀ 7 2141 zero ρ).isNone &&
  (outcome F B P w₀ 7 0 zero ρ).isNone
#guard sameOutcome (outcome F B P w₀ 7 2137 zero ρ) (some U)
#guard !sameOutcome (outcome F B P w₀ 7 2137 zero ρ) (outcome F B P w₀ 7 2137 zero ρ₁₃)
#guard !sameOutcome (outcome F B P w₀ 7 2137 zero ρ) (outcome F B P w₀ 7 2137 (coins 0 0 5 0 0) ρ)
-- in the second chain the stops of `ask` are given eight challenges before the part: the first
-- chain's four and the second chain's four, not the shared chain's three, which the moves there
-- have heard
#guard say F B { P with second := [sendH, askAt false (some 8)] } w₀ 7 2137 zero ρ none == "yes"
#guard say F B { P with second := [sendH, askAt false (some 11)] } w₀ 7 2137 zero ρ none ==
  "the honest side stops (Bad): ask: another number of challenges"

/-! ## The other errors of `run` -/

-- a prover's side left out, and nothing to fall back on
#guard say F B { P with shared := [] } w₀ 7 2137 zero ρ none ==
  "the honest side: a column is read of a table that is not at hand"
#guard say F B { P with second := [sendH] } w₀ 7 2137 zero ρ none ==
  "no: the second chain: refused at ask: the rounds"
#guard lacking F.shared.blocksInOrder ([] : List (Placed Empty L₀ Nat)) == ["look"]
#guard lacking F.second.blocksInOrder [sendH] == ["ask"]
-- a prover's side with another number of rounds
#guard say F B { P with shared := [⟨pLook, [{ lookPart ⟨2, 1⟩ with
    moves := (lookPart ⟨2, 1⟩).moves.take 1 }]⟩] } w₀ 7 2137 zero ρ none ==
  "the honest side: look: the prover's half has another number of rounds"
-- a message of another shape: a table of another length; an item of another class
#guard say F B { P with second := [⟨pSend, [{ sendPart with moves :=
    [⟨fun _ _ _ => .ok ⟨[], [⟨3, 1, fun _ _ => toF 0⟩]⟩, fun t => t.own⟩] }]⟩, askH] }
    w₀ 7 2137 zero ρ none ==
  "the honest side: send: the message has another shape than the sub-protocol states"
#guard say F B { P with second := [sendH, ⟨pAsk, [{ askPart false none with moves :=
    [⟨fun _ _ _ => .ok ⟨[.f (toF 1)], []⟩, fun t => t.own⟩] }]⟩] } w₀ 7 2137 zero ρ none ==
  "the honest side: ask: the message has another shape than the sub-protocol states"
-- a prover's side at no place of its chain: one that is in another chain's list; two at one place
#guard strays F.first.blocksInOrder [sendH] == [pSend]
#guard say F B { P with first := [sendH] } w₀ 7 2137 zero ρ none ==
  "the honest side: a half stands at no place of its chain"
#guard say F B { P with shared := [lookH, lookH] } w₀ 7 2137 zero ρ none ==
  "the honest side: two halves stand at one place"
-- two sub-protocols at one place
#guard say (F (second := [send₃, send₃, ask ()])) B P w₀ 7 2137 zero ρ none ==
  "the honest side: the description fails its own test on the places"
-- too few challenges; a sealing round that draws
#guard say F B P w₀ 7 2137 zero { ρ with shared := [dE 5, dP 12] } none ==
  "the honest side: the challenges are not as many as the rounds"
#guard say F B P w₀ 7 2137 zero { ρ with first := [dE 1, dE 10, dE 2, dE 7] } none ==
  "the honest side: the sealing round sends or draws something"
-- each chain's state: the honest run above shows that `look` has been shown one round at its
-- second, not the first chain's four too, and that `ask` has heard all eleven and was given 42 + 7:
-- what `hear` passed on in the first chain and `look` in the shared; with another `meet` the 7 does
-- not arrive; without the prover's side at `hear` the 42 does not
#guard shows (run F B { P with meet := fun x _ => x } w₀ 7 2137 zero ρ none) v₁ v₂
  (v₃ (last := rvE 0))
#guard shows (run F B { P with first := [] } w₀ 7 2137 zero ρ none) v₁ v₂ (v₃ (last := rvE 0))

/-! ## With a stored run to fall back on: the rows -/

#guard say F B P₀ w₀ 7 2137 zero ρ (some U) == "yes"
#guard line (rows true F B P₀ w₀ 7 2137 zero U) ==
  "told 0 of 3 · equal 0 of 0 · idle 0 · the decision: yes · stored columns read: [(0, 1)]"
#guard line (rows true F B { P with second := [sendH] } w₀ 7 2137 zero U) ==
  "told 2 of 3 · equal 2 of 2 · idle 0 · the decision: yes · stored columns read: [(0, 1)]"
#guard line (rows true F B P w₀ 7 2137 zero U) ==
  "told 3 of 3 · equal 3 of 3 · idle 0 · the decision: yes · stored columns read: [(0, 1)]"
-- the stored tables' columns too can be taken from the stored run
#guard line (rows true F B { P with stored := fun _ _ _ _ => none } w₀ 7 2137 zero U) ==
  "told 3 of 3 · equal 3 of 3 · idle 0 · the decision: yes · stored columns read: [(0, 1)]"
-- other challenges than the stored run's
#guard say F B P₀ w₀ 7 2137 zero { ρ with second := [dE 5, dE 4, d0, dP 6, d0] } (some U) ==
  "the honest side: the challenges are not the stored run's"
-- negative rows, coin by coin, each against a stored run that was made at a coin which is not 0.
-- (1) the block that `ask` adds to its word, of the coins of `look`, at U₅ (`coins 0 0 5 0 0`): at
-- its own coins all is equal; the prover's side drops it; it is 0 in the coins
#guard line (rows true F B P w₀ 7 2137 (coins 0 0 5 0 0) U₅) ==
  "told 3 of 3 · equal 3 of 3 · idle 0 · the decision: yes · stored columns read: [(0, 1)]"
#guard line (rows true F B { P with second := [sendH, askAt true] } w₀ 7 2137 (coins 0 0 5 0 0) U₅)
  == "told 3 of 3 · equal 2 of 3 · idle 0 · the decision: yes · stored columns read: [(0, 1)]"
#guard line (rows true F B P w₀ 7 2137 zero U₅) ==
  "told 3 of 3 · equal 2 of 3 · idle 0 · the decision: yes · stored columns read: [(0, 1)]"
-- a book in which a coin (that of `hear`) is spent twice: an error before any row is made
#guard line (rows true F B₂ P w₀ 7 2137 (⟨zero.first, zero.shared, zero.second⟩ : Coins B₂) U₅) ==
  "the book: a coin stands in two entries that spend it"
-- (2) the coin of `look` in the extension field, which is added to its answer: its own; 0
#guard line (rows true F B P w₀ 7 2137 (coins 0 0 0 3 0) (v₁, vA 12, v₃)) ==
  "told 3 of 3 · equal 3 of 3 · idle 0 · the decision: yes · stored columns read: [(0, 1)]"
#guard line (rows true F B P w₀ 7 2137 zero (v₁, vA 12, v₃)) ==
  "told 3 of 3 · equal 2 of 3 · idle 0 · the decision: yes · stored columns read: [(0, 1)]"
-- (3) the block that `ask` spends of the coins of `send`: its own; 0
#guard line (rows true F B P w₀ 7 2137 (coins 0 0 0 0 4)
    (v₁, v₂, v₃ (last := ⟨[.e (1, 4, 0)], d0⟩))) ==
  "told 3 of 3 · equal 3 of 3 · idle 0 · the decision: yes · stored columns read: [(0, 1)]"
#guard line (rows true F B P w₀ 7 2137 zero (v₁, v₂, v₃ (last := ⟨[.e (1, 4, 0)], d0⟩))) ==
  "told 3 of 3 · equal 2 of 3 · idle 0 · the decision: yes · stored columns read: [(0, 1)]"
-- (4) the first coin of `look`, which a column shows: its own; the prover's side puts another there
#guard line (rows true F B P w₀ 7 2139 (coins 0 2 0 0 0)
    (v₁, v₂ [(0, 4, [102])], v₃ (last := rvE 3))) ==
  "told 3 of 3 · equal 3 of 3 · idle 0 · the decision: yes · stored columns read: [(0, 1)]"
#guard line (rows true F B { P with shared := [lookAt ⟨2, 1⟩ 1] } w₀ 7 2139 (coins 0 2 0 0 0)
    (v₁, v₂ [(0, 4, [102])], v₃ (last := rvE 3))) ==
  "told 3 of 3 · equal 2 of 3 · idle 0 · " ++
  "the decision: no: the ends fail the last test · stored columns read: [(0, 1)]"
-- (5) the word of `Rc`: row 2 does not see it (no place sends a stored table): row 3 does
#guard line (rows true F B P w₀ 8 2137 zero U) == "told 3 of 3 · equal 3 of 3 · idle 0 · " ++
  "the decision: no: the shared chain: refused at table: table.words · " ++
  "stored columns read: [(0, 1)]"
-- the count of equal rounds drops: at a coin that a column shows; at a changed word of the index
-- that is read; and not at one that is not read
#guard line (rows true F B P w₀ 7 2137 (coins 0 2 0 0 0) U) ==
  "told 3 of 3 · equal 2 of 3 · idle 0 · " ++
  "the decision: no: the ends fail the last test · stored columns read: [(0, 1)]"
#guard line (rows true F B P { w₀ with ans := 8 } 7 2137 zero U) ==
  "told 3 of 3 · equal 2 of 3 · idle 0 · the decision: yes · stored columns read: [(0, 1)]"
#guard line (rows true F B P { w₀ with a := fun p => if p == 5 then 1 else w₀.a p } 7 2137 zero U)
  ==
  "told 3 of 3 · equal 3 of 3 · idle 0 · the decision: yes · stored columns read: [(0, 1)]"
-- a stored run that lacks a column; one that has a column too many
#guard line (rows true F B { P with shared := [] } w₀ 7 2137 zero (v₁, v₂ [], v₃)) ==
  "a stored column stands at another key or position than the one that is read"
#guard line (rows true F B P w₀ 7 2137 zero
    (v₁, v₂ [(0, 4, [100])] [(65536, 3, [7, 7]), (65536, 3, [7, 7])], v₃)) ==
  "the run and the stored run differ in size"
-- a place at which nothing is compared: where `peek` opens nothing, no column of the table of
-- `send` is read
#guard ((rows true (F (second := [send₃, peekAt [], ask ()])) B P w₀ 7 2137 zero
    (v₁, v₂, v₃ [])).toOption.map fun R =>
      (R.all, R.told, R.equal, R.idle, R.falls.length)) == some (3, 3, 2, 1, 0)
-- the printout: the two notes are on it
#guard ((rows true F B P w₀ 7 2137 zero U).toOption.map (·.print)) == some (
  "told 3 of 3 · equal 3 of 3 · idle 0 · the decision: yes · stored columns read: [(0, 1)]" ++
  " · the coins: the stored run's own" ++
  " · A YES SHOWS NOTHING OF WHAT WAS TAKEN FROM THE STORED RUN")
#guard ((rows false F B P w₀ 7 2137 (coins 0 0 1 0 0) U).toOption.map (·.print)) == some (
  "told 3 of 3 · equal 2 of 3 · idle 0 · the decision: yes · stored columns read: [(0, 1)]" ++
  " · the coins: NOT the stored run's: «equal» is not due; what is left is the decision" ++
  " · A YES SHOWS NOTHING OF WHAT WAS TAKEN FROM THE STORED RUN")

/-! ## Parts -/

/-- The first coin of the first block of a list of blocks; 0 where there is none. -/
def firstCoin : (l : List (String × Due)) → CsAll l → Cb.Gl.F
  | [], _ => toF 0
  | _ :: _, c => (c.1.fAt 0).toOption.getD (toF 0)

/-- The first round of `look` as a part of its own, typed at the count d and at the blocks sp that
it spends: the table. It stops where its own challenge is the element 13. -/
def lookSend (d : Due := ⟨2, 0⟩) (sp : List (String × Due) := []) : Part Empty L₀ Nat :=
  { takes := d, spends := sp, carries := []
    bad := fun _ own => if own.head? == some (dE 13) then some "the first challenge is 13" else none
    hid := fun v _ _ => nomatch v
    badShare := ⟨1, 1000⟩, hidShare := ⟨0, 1⟩
    moves := [⟨fun c _ t => (c.1.fAt 0).map fun k =>
        ⟨[], [⟨3, 1, fun p _ =>
          if p == 4 then toF (t.input.w₀.a p) + k else toF (t.input.w₀.a p)⟩]⟩,
      fun _ => 7⟩] }

/-- The second round of `look` as a part of its own: the answer, plus the key, plus its coin, plus
the first coin of the first block that it spends. It stops where its own challenge is the
position 13. -/
def lookAns (sp : List (String × Due) := []) : Part Empty L₀ Nat :=
  { takes := ⟨0, 1⟩, spends := sp, carries := []
    bad := fun _ own =>
      if own.head? == some (dP 13) then some "the second challenge is 13" else none
    hid := fun v _ _ => nomatch v
    badShare := ⟨1, 16⟩, hidShare := ⟨0, 1⟩
    moves := [⟨fun c s t => (c.1.eAt 0).map fun k =>
        ⟨[.answer (if s.rounds.length == 1 then
            ⟨toF t.input.w₀.ans + toF t.input.key + k.c0 + firstCoin sp c.2.1, k.c1, k.c2⟩
          else toE (0, 0, 0))], []⟩,
      fun t => t.own⟩] }

/-- The prover's side as a list of two parts; and as the two joined to one. -/
def lookTwo : Placed Empty L₀ Nat := ⟨pLook, [lookSend, lookAns]⟩
def lookOne : Placed Empty L₀ Nat := ⟨pLook, [lookSend.andThen lookAns]⟩

/-- The book for the list of two: the three coins of `look` in two rows. The entries are B's. -/
abbrev Bp : ProverCoinCounts :=
  { B with shared := [(⟨pLook, 0⟩, ⟨2, 0⟩), (⟨pLook, 1⟩, ⟨0, 1⟩)], cuts := cuts₂ }

/-- The same five coins as `coins`, typed by that book. -/
def coinsP (h l₀ l₁ lE s : UInt64) : Coins Bp :=
  ⟨(mk ⟨1, 0⟩ (fun _ => h) fun _ => 0, ()),
    (mk ⟨2, 0⟩ (fun i => if i == 0 then l₀ else l₁) fun _ => 0, mk ⟨0, 1⟩ (fun _ => 0) fun _ => lE,
      ()),
    (mk ⟨1, 0⟩ (fun _ => s) fun _ => 0, ())⟩

def P₂ : Prover Wit₀ UInt64 Nat UInt64 Trace Nat Nat := { P with shared := [lookTwo] }
def P₁ : Prover Wit₀ UInt64 Nat UInt64 Trace Nat Nat := { P with shared := [lookOne] }

#guard Bp.word F == none
#guard say F Bp P₂ w₀ 7 2137 (coinsP 0 0 0 0 0) ρ none == "yes"
#guard say F B P₁ w₀ 7 2137 zero ρ none == "yes"
-- the same views at the same coins: two parts; the two joined; the one part written by hand
#guard (outcome F B P w₀ 7 2139 (coins 9 2 5 3 4) ρ).isSome
#guard sameOutcome (outcome F Bp P₂ w₀ 7 2139 (coinsP 9 2 5 3 4) ρ)
  (outcome F B P w₀ 7 2139 (coins 9 2 5 3 4) ρ)
#guard sameOutcome (outcome F B P₁ w₀ 7 2139 (coins 9 2 5 3 4) ρ)
  (outcome F B P w₀ 7 2139 (coins 9 2 5 3 4) ρ)
#guard !sameOutcome (outcome F Bp P₂ w₀ 7 2139 (coinsP 9 2 5 0 4) ρ)
  (outcome F B P w₀ 7 2139 (coins 9 2 5 3 4) ρ)
-- which parts made a round at the place
#guard ((run F Bp P₂ w₀ 7 2137 (coinsP 0 0 0 0 0) ρ none).toOption.map (partsToldAt · pLook)) ==
  some [0, 1]
#guard ((run F B P₁ w₀ 7 2137 zero ρ none).toOption.map (partsToldAt · pLook)) == some [0]
-- the same stops: each part on its own challenge
#guard say F Bp P₂ w₀ 7 2137 (coinsP 0 0 0 0 0) ρ₁₃ none ==
  "the honest side stops (Bad): look: the first challenge is 13"
#guard say F Bp P₂ w₀ 7 2137 (coinsP 0 0 0 0 0) { ρ with shared := [dE 5, dP 13, dP 3] } none ==
  "the honest side stops (Bad): look: the second challenge is 13"
#guard say F B P₁ w₀ 7 2137 zero ρ₁₃ none ==
  "the honest side stops (Bad): look: the first challenge is 13"
#guard say F B P₁ w₀ 7 2137 zero { ρ with shared := [dE 5, dP 13, dP 3] } none ==
  "the honest side stops (Bad): look: the second challenge is 13"
-- the rows, with a stored run to fall back on, count the prover's side as a whole
#guard line (rows true F Bp P₂ w₀ 7 2137 (coinsP 0 0 0 0 0) U) ==
  "told 3 of 3 · equal 3 of 3 · idle 0 · the decision: yes · stored columns read: [(0, 1)]"
-- the book has the cut: the prover's side of one part at the book of two; the list of two at the
-- book of one; a prover's side at a place for which the book has no cut
#guard say F Bp P w₀ 7 2137 (coinsP 0 0 0 0 0) ρ none ==
  "the honest side: look: the book has no cut for this place, or the row is cut otherwise"
#guard say F B P₂ w₀ 7 2137 zero ρ none ==
  "the honest side: look: the book has no cut for this place, or the row is cut otherwise"
#guard say F { B with cuts := [] } P w₀ 7 2137 ⟨zero.first, zero.shared, zero.second⟩ ρ none ==
  "the honest side: hear 2: the book has no cut for this place, or the row is cut otherwise"
-- the same two with the cut made to fit the prover's side, and the rows not
#guard say F { Bp with cuts := cuts₁ } P w₀ 7 2137
    ⟨(coinsP 0 0 0 0 0).first, (coinsP 0 0 0 0 0).shared, (coinsP 0 0 0 0 0).second⟩ ρ none ==
  "the honest side: look: the book has a row for a part that the half does not have"
#guard say F { B with cuts := cuts₂ } P₂ w₀ 7 2137 ⟨zero.first, zero.shared, zero.second⟩ ρ none ==
  "the honest side: look: part 0: it takes more or fewer coins than the book has for it"

/-- An entry from the first part of `look` to its second: the first part's third coin. -/
def inLook : Ahead := ⟨"look to look", ⟨pLook, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨pLook, 1⟩, true⟩

/-- The book with that entry: the first part has three coins. -/
abbrev Bq : ProverCoinCounts :=
  { B with shared := [(⟨pLook, 0⟩, ⟨3, 0⟩), (⟨pLook, 1⟩, ⟨0, 1⟩)], ahead := B.ahead ++ [inLook]
           cuts := cuts₂ }

/-- Coins that are 0 but for the first part's third. -/
def coinsQ (l₂ : UInt64) : Coins Bq :=
  ⟨(mk ⟨1, 0⟩ (fun _ => 0) fun _ => 0, ()),
    (mk ⟨3, 0⟩ (fun i => if i == 2 then l₂ else 0) fun _ => 0, mk ⟨0, 1⟩ (fun _ => 0) fun _ => 0,
      ()),
    (mk ⟨1, 0⟩ (fun _ => 0) fun _ => 0, ())⟩

/-- The example's prover with this list at the place of `look`. -/
def PQ (ps : List (Part Empty L₀ Nat)) : Prover Wit₀ UInt64 Nat UInt64 Trace Nat Nat :=
  { P with shared := [⟨pLook, ps⟩] }

-- a block from a part to a later part of the same place: it arrives: the answer is 9 + 4
#guard Bq.word F == none
#guard shows (run F Bq (PQ [lookSend ⟨3, 0⟩, lookAns [inLook.named]]) w₀ 7 2137 (coinsQ 4) ρ none)
  v₁ (vA 13) v₃
-- the other part of the list, typed to spend that block: an error; so does the spender that is
-- not typed to
#guard say F Bq (PQ [lookSend ⟨3, 0⟩ [inLook.named], lookAns]) w₀ 7 2137 (coinsQ 4) ρ none ==
  "the honest side: look: part 0: it is typed at another number of entries than the book hands it"
#guard say F Bq (PQ [lookSend ⟨3, 0⟩, lookAns]) w₀ 7 2137 (coinsQ 4) ρ none ==
  "the honest side: look: part 1: it is typed at another number of entries than the book hands it"
-- an entry that runs backwards inside a place; one from a part to itself
#guard ({ Bq with ahead := [⟨"back", ⟨pLook, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨pLook, 0⟩, true⟩] } : ProverCoinCounts).word F
  == some "an entry's spender does not stand behind its owner"
#guard ({ Bq with ahead := [{ inLook with spender := ⟨pLook, 0⟩ }] } : ProverCoinCounts).word F ==
  some "an entry's spender does not stand behind its owner"
/-- B with an entry for a second part at the place of `look`. Its tables are B's, so B's coins fit
it. -/
abbrev Br : ProverCoinCounts :=
  { B with ahead := B.ahead ++ [{ inLook with start := ⟨0, 0⟩, once := false }] }
#guard Br.word F == none
#guard say F Br P w₀ 7 2137 (⟨zero.first, zero.shared, zero.second⟩ : Coins Br) ρ none ==
  "the honest side: look: an entry of the book names a part that the half does not have"

/-! ### Two parts as one, at a cut of coins that can go wrong -/

/-- The place of the shared chain's front, which is before `look`. There is no prover's side there:
the book gives it two coins, which are sent ahead. -/
def sFront : Addr := ⟨⟨2, none, 8, .frame⟩, 0⟩

/-- The first round of `look`: the word at position 4 plus the part's coin of the base field, plus
the first coordinate of its coin of the extension field, plus the block that it spends. -/
def cutA : Part Empty L₀ Nat :=
  { takes := ⟨1, 1⟩, spends := [("to the first", ⟨1, 0⟩)], carries := []
    bad := fun _ _ => none, hid := fun v _ _ => nomatch v
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [⟨fun c _ t => (c.1.fAt 0).bind fun k => (c.1.eAt 0).map fun e =>
        ⟨[], [⟨3, 1, fun p _ =>
          if p == 4 then toF (t.input.w₀.a p) + k + e.c0 + firstCoin _ c.2.1
          else toF (t.input.w₀.a p)⟩]⟩,
      fun _ => 7⟩] }

/-- The second round of `look`: the answer plus the corresponding three of its own. -/
def cutB : Part Empty L₀ Nat :=
  { takes := ⟨1, 1⟩, spends := [("to the second", ⟨1, 0⟩)], carries := []
    bad := fun _ _ => none, hid := fun v _ _ => nomatch v
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [⟨fun c _ t => (c.1.fAt 0).bind fun k => (c.1.eAt 0).map fun e =>
        ⟨[.answer ⟨toF t.input.w₀.ans + k + e.c0 + firstCoin _ c.2.1, toF 0, toF 0⟩], []⟩,
      fun t => t.own⟩] }

/-- The book for the two as a list; and for the two as one. -/
abbrev Bc : ProverCoinCounts :=
  { first := [], second := [(sSend, ⟨1, 0⟩)]
    shared := [(sFront, ⟨2, 0⟩), (⟨pLook, 0⟩, ⟨1, 1⟩), (⟨pLook, 1⟩, ⟨1, 1⟩)]
    ahead := [⟨"to the first", sFront, ⟨0, 0⟩, ⟨1, 0⟩, ⟨pLook, 0⟩, true⟩,
      ⟨"to the second", sFront, ⟨1, 0⟩, ⟨1, 0⟩, ⟨pLook, 1⟩, true⟩]
    cuts := cuts₂ }
abbrev Bj : ProverCoinCounts :=
  { first := [], second := [(sSend, ⟨1, 0⟩)]
    shared := [(sFront, ⟨2, 0⟩), (⟨pLook, 0⟩, ⟨2, 2⟩)]
    ahead := [⟨"to the first", sFront, ⟨0, 0⟩, ⟨1, 0⟩, ⟨pLook, 0⟩, true⟩,
      ⟨"to the second", sFront, ⟨1, 0⟩, ⟨1, 0⟩, ⟨pLook, 0⟩, true⟩]
    cuts := cuts₁ }

/-- Six coins, all different: the two blocks; the first part's two; the second part's two. -/
def coinsC (r₁ r₂ f₁ e₁ f₂ e₂ : UInt64) : Coins Bc :=
  ⟨(), (mk ⟨2, 0⟩ (fun i => if i == 0 then r₁ else r₂) fun _ => 0,
      mk ⟨1, 1⟩ (fun _ => f₁) fun _ => e₁, mk ⟨1, 1⟩ (fun _ => f₂) fun _ => e₂, ()),
    (mk ⟨1, 0⟩ (fun _ => 0) fun _ => 0, ())⟩
def coinsJ (r₁ r₂ f₁ e₁ f₂ e₂ : UInt64) : Coins Bj :=
  ⟨(), (mk ⟨2, 0⟩ (fun i => if i == 0 then r₁ else r₂) fun _ => 0,
      mk ⟨2, 2⟩ (fun i => if i == 0 then f₁ else f₂) fun i => if i == 0 then e₁ else e₂, ()),
    (mk ⟨1, 0⟩ (fun _ => 0) fun _ => 0, ())⟩

/-- The example's prover with this list at the place of `look`, and a prover's side at that of `ask`
that is given nothing. -/
def PC (ps : List (Part Empty L₀ Nat)) : Prover Wit₀ UInt64 Nat UInt64 Trace Nat Nat :=
  { P with first := [], shared := [⟨pLook, ps⟩], second := [sendH, askTyped [] []] }

/-- The shared chain's view with this word at position 4 and this answer. -/
def vC (w x : UInt64) : Fmt.View :=
  ⟨[⟨[], dE 5⟩, ⟨[.answer (x, 0, 0)], dP 12⟩, ⟨[], dP 3⟩], [(0, 4, [w]), (65536, 3, [7, 7])]⟩

#guard Bc.word F == none && Bj.word F == none
-- as a list: 100 + 1 + 4 + 16 and 9 + 2 + 8 + 32; joined: the same
#guard shows (run F Bc (PC [cutA, cutB]) w₀ 7 2137 (coinsC 16 32 1 4 2 8) ρ none) v₁ (vC 121 51) v₃
#guard shows (run F Bj (PC [cutA.andThen cutB]) w₀ 7 2137 (coinsJ 16 32 1 4 2 8) ρ none) v₁
  (vC 121 51) v₃
-- the joined part's coins with two of one field swapped; the two blocks swapped
#guard shows (run F Bj (PC [cutA.andThen cutB]) w₀ 7 2137 (coinsJ 16 32 2 4 1 8) ρ none) v₁
  (vC 122 50) v₃
#guard shows (run F Bj (PC [cutA.andThen cutB]) w₀ 7 2137 (coinsJ 16 32 1 8 2 4) ρ none) v₁
  (vC 125 47) v₃
#guard shows (run F Bj (PC [cutA.andThen cutB]) w₀ 7 2137 (coinsJ 32 16 1 4 2 8) ρ none) v₁
  (vC 137 35) v₃
-- the eighth test inside one place: the block that the second part spends, carried by the first
#guard ({ Bc with ahead := [⟨"to the second", sFront, ⟨1, 0⟩, ⟨1, 0⟩, ⟨pLook, 1⟩, true⟩,
    ⟨"to the first too", sFront, ⟨1, 0⟩, ⟨1, 0⟩, ⟨pLook, 0⟩, false⟩] } : ProverCoinCounts).word F ==
  some "a coin that a part spends is handed to a part in front of it, or to itself as carried"
-- and the other way round: spent by the first, carried by the second, after it: it passes
#guard ({ Bc with ahead := [⟨"to the first", sFront, ⟨1, 0⟩, ⟨1, 0⟩, ⟨pLook, 0⟩, true⟩,
    ⟨"to the second too", sFront, ⟨1, 0⟩, ⟨1, 0⟩, ⟨pLook, 1⟩, false⟩] } : ProverCoinCounts).word F == none

/-! ## One toy part, placed twice -/

/-- A toy part, typed at no input and at a state of its own: one round that sends nothing. After its
challenge it passes on 21 more, if its own last challenge is d. It stops where its own challenge is
the element 99. -/
def tick (d : Fmt.Drawn) (takes : Due) : Part Unit Unit Nat :=
  { takes := takes, spends := [], carries := []
    bad := fun _ own => if own == [dE 99] then some "its own challenge is 99" else none
    hid := fun _ _ _ => none
    badShare := ⟨1, 1000⟩, hidShare := ⟨0, 1⟩
    moves := [⟨fun _ _ _ => .ok ⟨[], []⟩, fun t => if t.lately 1 == [d] then t.own + 21 else t.own⟩]
  }

/-- The part placed in the first chain's types: its state is what is passed on, below 1000. -/
def seat (p : Part Unit Unit Nat) : Part L L Nat :=
  p.lift (fun _ => ()) (fun _ => ()) (fun x => x % 1000) fun x y => x / 1000 * 1000 + y

/-- The prover's side for `BlockToy.hear`: a list of two placements of the one part. The first takes
the place's coin. -/
def hearTwo : Placed L L Nat := ⟨pHear, [seat (tick (dE 1) ⟨1, 0⟩), seat (tick (dE 10) ⟨0, 0⟩)]⟩

/-- B with the two rounds of `hear` cut in two. Its tables are B's, so B's coins fit it. -/
abbrev Bh : ProverCoinCounts :=
  { B with cuts := [(pHear, [1, 1]), (pLook, [2]), (pSend, [1]), (pAsk, [1])] }
def zeroH : Coins Bh := ⟨zero.first, zero.shared, zero.second⟩

-- 21 + 21 arrive at `ask`, as the 42 of `hear` did
#guard shows (run F Bh { P with first := [hearTwo] } w₀ 7 2137 zeroH ρ none) v₁ v₂ v₃
-- the two placements the other way round: neither finds its own challenge
#guard shows (run F Bh { P with first := [⟨pHear, [seat (tick (dE 10) ⟨1, 0⟩),
  seat (tick (dE 1) ⟨0, 0⟩)]⟩] } w₀ 7 2137 zeroH ρ none) v₁ v₂ (v₃ (last := rvE 0))
-- each placement stops on its own challenge, and not on the other's
#guard say F Bh { P with first := [hearTwo] } w₀ 7 2137 zeroH
    { ρ with first := [dE 99, dE 10, dE 2, d0] } none ==
  "the honest side stops (Bad): hear 2: its own challenge is 99"
#guard say F Bh { P with first := [hearTwo] } w₀ 7 2137 zeroH
    { ρ with first := [dE 1, dE 99, dE 2, d0] } none ==
  "the honest side stops (Bad): hear 2: its own challenge is 99"
#guard (seat (tick (dE 1) ⟨1, 0⟩)).stopAt none [dE 99] [dE 1] == none
#guard (seat (tick (dE 1) ⟨1, 0⟩)).stopAt none [dE 1] [dE 99] == some .bad

/-! ## A part's section of a run; a side; the simulator's form -/

/-- The honest run at coins, as a run. -/
def runAt (c : Coins B) : Option Run := (at_ 2137 c).toOption

/-- The stored tables' columns that a run reads, by the example's own function for columns. -/
def stOf (r : Run) : List (Nat × Nat × List UInt64) :=
  storedShown (P.storedWords w₀ 7) r.storedAsked

/-- What a simulator paired with the part at a is given of a run, with these columns put in. -/
def bf (r : Run) (a : Addr) : Before := r.beforeAt (stOf r) a

#guard (runAt zero).map (·.storedRead) == some [(0, 1)]
-- the table of `look` is read at 4 in its own chain and at 6 in the second; that of `send` at 2
#guard (runAt zero).map (·.askedAt sLook) == some [[[4, 6]], []]
#guard (runAt zero).map (·.askedAt sSend) == some [[[2]]]
#guard (runAt zero).map (·.drawnAt sLook) == some [dE 5, dP 12]
#guard (runAt (coins 0 2 0 3 0)).map (·.shownAt sLook) ==
  some [⟨[], [[(4, [102]), (6, [4])]]⟩, ⟨[.answer (12, 0, 0)], []⟩]
#guard (runAt zero).map (·.shownAt sAsk) == some [⟨[.e (1, 0, 0)], []⟩]
#guard (runAt zero).map (fun r => ((r.seenAt sHear).rounds.length, (r.seenAt sLook).rounds.length,
  (r.seenAt sAsk).rounds.length)) == some (0, 0, 11)
-- there is no part at the number 1 of a list of one
#guard (runAt zero).map (·.shownAt ⟨pLook, 1⟩) == some []

/-- A toy simulator paired with the one part of `look`. At position 4 it shows its own coin,
elsewhere 0, and as the answer its coin of the extension field. Where the part's first stop stops
the part it outputs `none`: it reads that from the challenges, which it is given in advance. -/
def lookS : Sim UInt64 :=
  { addr := sLook, takes := ⟨1, 1⟩
    tell := fun _ _ ds asks c =>
      if ds.head? == some (dE 13) || ds[1]? == some (dP 13) then none else
      some [⟨[], (asks.headD []).map fun ps => ps.map fun p =>
          (p, [if p == 4 then ofF (c.f ⟨0, by decide⟩) else 0])⟩,
        ⟨[.answer (ofE (c.e ⟨0, by decide⟩))], []⟩] }

/-- The example's side at the place of `look`, with the prover's side of one part. -/
def lookSide : Side St Nat Empty L₀ Nat UInt64 :=
  { block := look [(3, 1)] true (), row := [(lookPart ⟨2, 1⟩, lookS)] }

/-- Nothing comes before. -/
def none₀ : Before := ⟨[], []⟩

/-- The rounds of `look`, each with its oracle messages. -/
def lookRounds : List (Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle) :=
  (look [(3, 1)] true ()).rounds.zip (look [(3, 1)] true ()).oracles

/-- That side's one `Member`, written out: so that coins can be typed at its counts. -/
def lookU : Member Empty L₀ Nat UInt64 := ⟨0, lookRounds, lookPart ⟨2, 1⟩, lookS⟩

/-- The state of the shared chain's run before `look`, as `ChainProgress.start` (Honest/Walk.lean) lays it:
no column has been opened (`some []`). So the pair of this state and `none₀` meets the premise of
`Good.exact` on the field (Honest/Side.lean). `startShared` (Honest/Frame.lean), from which `run`
and `midSharedAt` go, lays `none` there. -/
def mid₀ : Mid L₀ Nat := ⟨⟨⟨w₀, 7, 0⟩, [], 0⟩, [], [], some []⟩

-- its field is what `none₀` holds for the reads of declared rounds: at no round, and at the rounds
-- of `look`
#guard mid₀.opened == none₀.opened (readsBefore [] none₀)
#guard mid₀.opened == none₀.opened (readsBefore [(1, 0, lookRounds.map (·.1))] none₀)

#guard lookSide.fits
-- a simulator that names another address; an empty list: `Good` asks `fits`. A part without a
-- simulator cannot be written: the list is a list of pairs
#guard !({ lookSide with row := [(lookPart ⟨2, 1⟩, { lookS with addr := sSend })] } :
  Side St Nat Empty L₀ Nat UInt64).fits
#guard !({ lookSide with row := [] } : Side St Nat Empty L₀ Nat UInt64).fits
-- the side's prover's side is the one that the example's prover plays
#guard sameOutcome (outcome F B { P with shared := [lookSide.half] } w₀ 7 2139 (coins 9 2 5 3 4) ρ)
  (outcome F B P w₀ 7 2139 (coins 9 2 5 3 4) ρ)
#guard lookSide.members.map (fun u => (u.number, u.rounds.length, u.part.takes, u.sim.takes)) ==
  [(0, 2, ⟨2, 1⟩, ⟨1, 1⟩)]
-- the part, played alone, shows what the run shows at its address
#guard (runAt (coins 0 2 2 3 0)).isSome
#guard lookSide.shows .shared lookU (mk ⟨2, 1⟩ (fun _ => 2) fun _ => 3, (), ()) mid₀ [dE 5, dP 12]
  [[[4, 6]], []] == (runAt (coins 0 2 2 3 0)).map (·.shownAt sLook)
-- where the part stops: `none`; and `Side.stopAt`, which is given no coin, says so and how
#guard lookSide.shows .shared lookU (mk ⟨2, 1⟩ (fun _ => 2) fun _ => 3, (), ()) mid₀ [dE 13, dP 12]
  [[[4, 6]], []] == none
#guard lookSide.stopAt .shared ⟨w₀, 7, 0⟩ [] [dE 13, dP 12] == some .bad
#guard lookSide.stopAt .shared ⟨w₀, 7, 0⟩ [] [dE 5, dP 12] == none
-- this part's stop reads its own challenges: a 13 before the part does not stop it
#guard lookSide.stopAt .shared ⟨w₀, 7, 0⟩ [dE 13] [dE 5, dP 12] == none
-- after its last challenge too; and there the toy simulator outputs `none`, as the part
#guard lookSide.stopAt .shared ⟨w₀, 7, 0⟩ [] [dE 5, dP 13] == some .bad
#guard lookSide.shows .shared lookU (mk ⟨2, 1⟩ (fun _ => 2) fun _ => 3, (), ()) mid₀ [dE 5, dP 13]
  [[[5]], []] == none
#guard lookU.tells .shared (mk ⟨1, 1⟩ (fun _ => 102) fun _ => 12) ⟨w₀, 7, 0⟩ none₀ [dE 5, dP 13]
  [[[5]], []] == none
#guard lookU.tells .shared (mk ⟨1, 1⟩ (fun _ => 102) fun _ => 12) ⟨w₀, 7, 0⟩ none₀ [dE 13, dP 12]
  [[[4]], []] == none
-- an evaluation at fixed coins, no lemma: at the simulator's coins 102 and 12 it outputs what the
-- part shows at the part's coins 2 and 3, at position 4; at another coin it does not; nor at
-- position 6, where the part adds no coin
#guard lookU.tells .shared (mk ⟨1, 1⟩ (fun _ => 102) fun _ => 12) ⟨w₀, 7, 0⟩ none₀ [dE 5, dP 12]
    [[[4]], []] ==
  lookSide.shows .shared lookU (mk ⟨2, 1⟩ (fun _ => 2) fun _ => 3, (), ()) mid₀ [dE 5, dP 12]
    [[[4]], []]
#guard lookU.tells .shared (mk ⟨1, 1⟩ (fun _ => 103) fun _ => 12) ⟨w₀, 7, 0⟩ none₀ [dE 5, dP 12]
    [[[4]], []] !=
  lookSide.shows .shared lookU (mk ⟨2, 1⟩ (fun _ => 2) fun _ => 3, (), ()) mid₀ [dE 5, dP 12]
    [[[4]], []]
#guard lookU.tells .shared (mk ⟨1, 1⟩ (fun _ => 102) fun _ => 12) ⟨w₀, 7, 0⟩ none₀ [dE 5, dP 12]
    [[[4, 6]], []] !=
  lookSide.shows .shared lookU (mk ⟨2, 1⟩ (fun _ => 2) fun _ => 3, (), ()) mid₀ [dE 5, dP 12]
    [[[4, 6]], []]
-- of the input a simulator is given the public part alone, by the `Face`: in the shared chain the
-- key, in the two others the instance
#guard Face.shared.pub (⟨w₀, 7, 3⟩ : L₀) == 3
#guard (Face.shared.sees (⟨w₀, 7, 3⟩ : L₀)).isNone

/-! ### What a simulator is given of the run before its part -/

-- before `ask`: eleven rounds; the first of `look`, the fifth of them, with its table's columns at
-- both positions that the run reads, the second of which is read in the second chain; and the
-- stored column that the run reads
#guard (runAt zero).map (fun r => ((bf r sAsk).rounds.length, (bf r sAsk).stored)) ==
  some (11, [(0, 3, [7, 7])])
#guard (runAt zero).map (fun r => ((bf r sAsk).rounds[4]?).map (·.2.1.cols)) ==
  some (some [[(4, [100]), (6, [4])]])
-- its rounds are those that the part is given
#guard (runAt (coins 0 2 0 3 0)).map
    (fun r => (bf r sAsk).seen.map fun v => (v.vals, v.drawn)) ==
  (runAt (coins 0 2 0 3 0)).map (fun r => (r.seenAt sAsk).rounds.map fun v => (v.vals, v.drawn))
#guard (runAt zero).map (fun r => (bf r sLook).rounds.length) == some 0
-- each round has its chain's number: four of the first chain, three of the shared, four of the
-- second
#guard (runAt zero).map (fun r => (bf r sAsk).rounds.map (·.1)) ==
  some [0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 2]

/-! ### What comes before holds a column for every read of the part's own rounds -/

/-- The address of `BlockToy.peek`: there is no prover's side there; its one round draws a position
and reads, there, the table of `look`, which the shared chain sent, and that of `send`. -/
def sPeek : Addr := ⟨⟨3, some 0, 5, .K12⟩, 0⟩

-- the run's own `beforeAt` passes at the run's own challenge: the position 6
#guard (runAt zero).map (fun r => (bf r sPeek).holds 2 F.lastChainFirstTreeNumber peek.rounds [dP 6]) ==
  some true
-- and so at every address of the run, at the challenges that the run has there: sub-protocol by
-- sub-protocol of the three chains
#guard (runAt zero).map (fun r =>
    F.first.blocksInOrder.all (fun b => (bf r ⟨b.place, 0⟩).holds 0 0 b.rounds (r.drawnAt ⟨b.place, 0⟩)) &&
    F.shared.blocksInOrder.all (fun b => (bf r ⟨b.place, 0⟩).holds 1 0 b.rounds (r.drawnAt ⟨b.place, 0⟩)) &&
    F.second.blocksInOrder.all fun b =>
      (bf r ⟨b.place, 0⟩).holds 2 F.lastChainFirstTreeNumber b.rounds (r.drawnAt ⟨b.place, 0⟩)) == some true
-- with one column dropped from the run's own `front` (that of `look` at the position 6) it fails;
-- with the stored columns dropped it fails at the round of `table`
#guard (runAt zero).map (fun r =>
    ({ bf r sPeek with rounds := (bf r sPeek).rounds.map fun x =>
        (x.1, { x.2.1 with cols := x.2.1.cols.map fun l => l.filter (·.1 != 6) }, x.2.2) } :
      Before).holds 2 F.lastChainFirstTreeNumber peek.rounds [dP 6]) == some false
#guard (runAt zero).map (fun r =>
    ({ bf r sAsk with stored := [] } : Before).holds 1 0 table.rounds [dP 3]) == some false
-- at another challenge it fails: the position 5 is read of neither table in that run
#guard (runAt zero).map (fun r => (bf r sPeek).holds 2 F.lastChainFirstTreeNumber peek.rounds [dP 5]) ==
  some false
-- a `front` that lists another position of the table of `look` than the one that is drawn: it
-- fails; with the position that is drawn: it passes. (The table of `send`, the second chain's
-- first, too.)
#guard !(⟨[(1, ⟨[], [[(3, [0])]]⟩, dE 5), (2, ⟨[], [[(2, [6])]]⟩, d0)], []⟩ : Before).holds 2
  F.lastChainFirstTreeNumber peek.rounds [dP 6]
#guard (⟨[(1, ⟨[], [[(6, [4])]]⟩, dE 5), (2, ⟨[], [[(2, [6])]]⟩, d0)], []⟩ : Before).holds 2
  F.lastChainFirstTreeNumber peek.rounds [dP 6]
-- a tree that is taken over from another chain and of which `front` holds nothing: it fails
#guard !(⟨[(2, ⟨[], [[(2, [6])]]⟩, d0)], []⟩ : Before).holds 2 F.lastChainFirstTreeNumber peek.rounds [dP 6]
-- what the test does not see: a `front` that leaves out a tree of the part's own chain (the round
-- of `send` with no list of columns): that tree then counts as the part's own, and the test passes
#guard (⟨[(1, ⟨[], [[(6, [4])]]⟩, dE 5), (2, ⟨[], []⟩, d0)], []⟩ : Before).holds 2 F.lastChainFirstTreeNumber
  peek.rounds [dP 6]
-- a stored table: the run reads the item 0 at the position 3; at another position it fails
#guard (runAt zero).map (fun r => (bf r sAsk).holds 1 0 table.rounds [dP 3]) ==
  some true
#guard (runAt zero).map (fun r => (bf r sAsk).holds 1 0 table.rounds [dP 4]) ==
  some false

/-- Two toy simulators, one paired with each part of the list of two. -/
def lookS₀ : Sim UInt64 :=
  { addr := ⟨pLook, 0⟩, takes := ⟨1, 0⟩
    tell := fun _ _ ds asks c =>
      if ds.head? == some (dE 13) then none else
      some [⟨[], (asks.headD []).map fun ps => ps.map fun p =>
        (p, [if p == 4 then ofF (c.f ⟨0, by decide⟩) else 0])⟩] }
def lookS₁ : Sim UInt64 :=
  { addr := ⟨pLook, 1⟩, takes := ⟨0, 1⟩
    tell := fun _ _ ds _ c =>
      if ds.head? == some (dP 13) then none else some [⟨[.answer (ofE (c.e ⟨0, by decide⟩))], []⟩] }

/-- The example's side at the place of `look`, with the list of two parts. -/
def lookSide₂ : Side St Nat Empty L₀ Nat UInt64 :=
  { lookSide with row := [(lookSend, lookS₀), (lookAns, lookS₁)] }

/-- Its two `Member`s, written out. -/
def lookU₀ : Member Empty L₀ Nat UInt64 := ⟨0, lookRounds.take 1, lookSend, lookS₀⟩
def lookU₁ : Member Empty L₀ Nat UInt64 := ⟨1, lookRounds.drop 1, lookAns, lookS₁⟩

/-- The state of the shared chain's run between the two parts. No columns are handed. -/
def mid₁ : Mid L₀ Nat := ⟨⟨⟨w₀, 7, 0⟩, [dE 5], 7⟩, [dE 5], [⟨[], dE 5⟩], none⟩

/-- `mid₁` as it is set beside a simulator's output at `fr`: its field is the frame's own term, what
`fr` holds for the reads of `pre` (the premise of `Good.exact` on the field, Honest/Side.lean). -/
def mid₁At (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (fr : Before) : Mid L₀ Nat :=
  { mid₁ with opened := fr.opened (readsBefore pre fr) }

/-- The `pre` of the place of `look` in the shared chain of `F`, as `Owed.good` lays it
(Honest/Owed.lean; `earlierOf` is empty at the shared chain). -/
def preLook : List (Nat × Nat × List Fmt.DeclaredRound) := preOf 1 0 [] F.shared.blocksInOrder pLook

/-- The run with the list of two, at coins. -/
def runP (c : Coins Bp) : Option Run := (run F Bp P₂ w₀ 7 2137 c ρ none).toOption

#guard lookSide₂.fits
-- a list with a round too few; with a move too many; the two simulators the other way round
#guard !({ lookSide₂ with row := [(lookSend, lookS₀)] } : Side St Nat Empty L₀ Nat UInt64).fits
#guard !({ lookSide₂ with row := [(lookPart ⟨2, 1⟩, lookS₀), (lookAns, lookS₁)] } :
  Side St Nat Empty L₀ Nat UInt64).fits
#guard !({ lookSide₂ with row := [(lookSend, lookS₁), (lookAns, lookS₀)] } :
  Side St Nat Empty L₀ Nat UInt64).fits
#guard sameOutcome (outcome F Bp { P with shared := [lookSide₂.half] } w₀ 7 2139
  (coinsP 9 2 5 3 4) ρ) (outcome F Bp P₂ w₀ 7 2139 (coinsP 9 2 5 3 4) ρ)
#guard lookSide₂.members.map (fun u => (u.number, u.rounds.length, u.part.takes, u.sim.takes)) ==
  [(0, 1, ⟨2, 0⟩, ⟨1, 0⟩), (1, 1, ⟨0, 1⟩, ⟨0, 1⟩)]
-- each part, played alone, shows what the run shows at its address; the second from the state of
-- the run between the two
#guard (runP (coinsP 0 2 2 3 0)).isSome
#guard lookSide₂.shows .shared lookU₀ (mk ⟨2, 0⟩ (fun _ => 2) fun _ => 0, (), ()) mid₀ [dE 5]
  [[[4, 6]]] == (runP (coinsP 0 2 2 3 0)).map (·.shownAt ⟨pLook, 0⟩)
#guard lookSide₂.shows .shared lookU₁ (mk ⟨0, 1⟩ (fun _ => 0) fun _ => 3, (), ()) mid₁ [dP 12] [[]]
  == (runP (coinsP 0 2 2 3 0)).map (·.shownAt ⟨pLook, 1⟩)
#guard (runP (coinsP 0 2 2 3 0)).map (·.shownAt ⟨pLook, 1⟩) == some [⟨[.answer (12, 0, 0)], []⟩]
#guard (runP (coinsP 0 0 0 0 0)).map (fun r => ((r.seenAt ⟨pLook, 0⟩).rounds.length,
  (r.seenAt ⟨pLook, 1⟩).rounds.length, r.drawnAt ⟨pLook, 1⟩)) == some (0, 1, [dP 12])
-- before the second part its simulator is given the first part's round, with both columns
#guard (runP (coinsP 0 2 0 0 0)).map (fun r => (bf r ⟨pLook, 1⟩).rounds.map (·.2.1.cols)) ==
  some [[[(4, [102]), (6, [4])]]]
-- an item in the clear is shown whatever positions are asked: at no list of positions at all the
-- second part still shows its answer, and the first its round with no column
#guard lookSide₂.shows .shared lookU₁ (mk ⟨0, 1⟩ (fun _ => 0) fun _ => 3, (), ()) mid₁ [dP 12] [] ==
  some [⟨[.answer (12, 0, 0)], []⟩]
#guard lookSide₂.shows .shared lookU₀ (mk ⟨2, 0⟩ (fun _ => 2) fun _ => 0, (), ()) mid₀ [dE 5] [] ==
  some [⟨[], [[]]⟩]
-- the second part's own round reads the first part's table: what comes before the second part holds
-- that column at the run's own challenge, not at another; before the one part that sends the table
-- itself nothing has to be there
#guard (runP (coinsP 0 0 0 0 0)).map (fun r =>
  (bf r ⟨pLook, 1⟩).holds 1 0 ((lookRounds.drop 1).map (·.1)) [dP 12]) == some true
#guard (runP (coinsP 0 0 0 0 0)).map (fun r =>
  (bf r ⟨pLook, 1⟩).holds 1 0 ((lookRounds.drop 1).map (·.1)) [dP 13]) == some false
#guard none₀.holds 1 0 (lookRounds.map (·.1)) [dE 5, dP 12]
-- where the list stops, and where each part does
#guard lookSide₂.stopAt .shared ⟨w₀, 7, 0⟩ [] [dE 5, dP 13] == some .bad
#guard lookSide₂.stopAt .shared ⟨w₀, 7, 0⟩ [] [dE 5, dP 12] == none
#guard lookSend.stopAt none [] [dE 5] == none && lookAns.stopAt none [dE 5] [dP 13] == some .bad
-- each simulator paired with its part, at coins chosen to fit; and `none` at the part's stop. The
-- pairs of `lookU₁` have the field that `none₀` holds at `preLook` (the next line pins its value);
-- they still miss `m.seen = front.seen`: `mid₁` has seen one round, and `none₀` shows none
#guard (mid₁At preLook none₀).opened == some []
#guard lookU₀.tells .shared (mk ⟨1, 0⟩ (fun _ => 102) fun _ => 0) ⟨w₀, 7, 0⟩ none₀ [dE 5] [[[4]]] ==
  lookSide₂.shows .shared lookU₀ (mk ⟨2, 0⟩ (fun _ => 2) fun _ => 0, (), ()) mid₀ [dE 5] [[[4]]]
#guard lookU₁.tells .shared (mk ⟨0, 1⟩ (fun _ => 0) fun _ => 12) ⟨w₀, 7, 0⟩ none₀ [dP 12] [[]] ==
  lookSide₂.shows .shared lookU₁ (mk ⟨0, 1⟩ (fun _ => 0) fun _ => 3, (), ()) (mid₁At preLook none₀)
    [dP 12] [[]]
#guard lookU₁.tells .shared (mk ⟨0, 1⟩ (fun _ => 0) fun _ => 12) ⟨w₀, 7, 0⟩ none₀ [dP 13] [[]] ==
    none &&
  lookSide₂.shows .shared lookU₁ (mk ⟨0, 1⟩ (fun _ => 0) fun _ => 3, (), ()) (mid₁At preLook none₀)
    [dP 13] [[]] == none

/-- A toy simulator paired with the part of `ask`: it shows its three coins. -/
def askS : Sim Nat :=
  { addr := sAsk, takes := ⟨3, 0⟩
    tell := fun _ _ _ _ c => some [⟨[.e (ofF (c.f ⟨0, by decide⟩), ofF (c.f ⟨1, by decide⟩),
      ofF (c.f ⟨2, by decide⟩))], []⟩] }

/-- The example's side at the place of `ask`, whose part has a second stop. -/
def askSide : Side St Nat L L Nat Nat := { block := ask (), row := [(askPart false none, askS)] }

/-- Its one `Member`, written out. -/
def askU : Member L L Nat Nat :=
  ⟨0, (ask ()).rounds.zip (ask ()).oracles, askPart false none, askS⟩

/-- What the prover's side at `ask` is given as its input, at an instance. -/
def wAt (x : Nat) : L := ⟨w₀, 7, x, ⟨fun p => if p == 2 then 6 else 0, UInt64.ofNat (x - 2136)⟩⟩

/-- The coins of `ask`: none of its own, two blocks that it spends, one that it carries: all 0. -/
def askCoins : Cs ⟨0, 0⟩ × CsAll [nHear, nSend] × CsAll [nLook] :=
  (Cs.empty, (mk ⟨1, 0⟩ (fun _ => 0) fun _ => 0, mk ⟨1, 0⟩ (fun _ => 0) fun _ => 0, ()),
    (mk ⟨1, 0⟩ (fun _ => 0) fun _ => 0, ()))

/-- The state of the second chain's run before `ask`: eleven challenges heard, eleven rounds shown,
42 + 7 passed on. No columns are handed. -/
def mid₄₉ : Mid L Nat :=
  ⟨⟨wAt 2137, List.replicate 11 d0, 49⟩, List.replicate 8 d0, List.replicate 11 ⟨[], d0⟩, none⟩

#guard askSide.fits
#guard Face.own.pub (wAt 2141) == 2141
-- the second stop: `Side.stopAt` returns `hid` just where the part, played alone, shows `none`;
-- where nothing is given that this stop may read, the stop is not asked
#guard askSide.stopAt .own (wAt 2141) [] [d0] == some .hid
#guard askSide.shows .own askU askCoins ⟨⟨wAt 2141, [], 49⟩, [], [], none⟩ [d0] [[]] == none
#guard askSide.stopAt .own (wAt 2137) [] [d0] == none
#guard (askSide.shows .own askU askCoins ⟨⟨wAt 2137, [], 49⟩, [], [], none⟩ [d0] [[]]).isSome
#guard (askPart false none).stopAt (some (wAt 2141)) [] [d0] == some .hid &&
  (askPart false none).stopAt none [] [d0] == none
#guard hidAt F B P w₀ 7 2141 zero ρ && !hidAt F B P w₀ 7 2137 zero ρ &&
  !hidAt F B P w₀ 7 2137 zero ρ₁₃
-- the parts of `look` are plain; that of `ask` is not: it spends two blocks and carries one. What
-- it shows depends on the block that it carries: at two carried blocks the part shows two things
#guard (lookPart ⟨2, 1⟩).plain && lookSend.plain && lookAns.plain && !(askPart false none).plain
#guard !(lookAns [inLook.named]).plain
#guard askSide.shows .own askU askCoins mid₄₉ [d0] [[]] !=
  askSide.shows .own askU (askCoins.1, askCoins.2.1, (mk ⟨1, 0⟩ (fun _ => 4) fun _ => 0, ())) mid₄₉
    [d0] [[]]
-- the lens of `seat`: what is passed on above 1000 stays, what is below goes through the part
#guard ((seat (tick (dE 1) ⟨1, 0⟩)).moves.head?.map fun mv => mv.hand ⟨wAt 2137, [dE 1], 5007⟩) ==
  some 5028

/-! ### A simulator that reads what comes before -/

/-- The first sample answer among rounds as a view shows them: its first word; 0 if there is none.
-/
def answerIn (rs : List Fmt.RoundView) : Cb.Gl.F :=
  ((rs.flatMap (·.vals)).findSome? fun g =>
    match g with
    | .answer x => some (toF x.1)
    | _ => none).getD (toF 0)

/-- A part at the place of `ask` that sends what `look` has shown as its answer, from `Seen`, plus a
coin of its own. -/
def echoPart : Part L L Nat :=
  { takes := ⟨1, 0⟩, spends := [], carries := []
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [⟨fun c s _ => (c.1.fAt 0).map fun k =>
        ⟨[.e ⟨answerIn s.rounds + k, toF 0, toF 0⟩], []⟩,
      fun t => t.own⟩] }

/-- Its simulator reads `front`: the same answer from the rounds that are there, plus its own coin.
-/
def echoS : Sim Nat :=
  { addr := sAsk, takes := ⟨1, 0⟩
    tell := fun _ front _ _ c =>
      some [⟨[.e (ofF (answerIn front.seen + c.f ⟨0, by decide⟩), 0, 0)], []⟩] }

def echoSide : Side St Nat L L Nat Nat := { block := ask (), row := [(echoPart, echoS)] }
def echoU : Member L L Nat Nat := ⟨0, (ask ()).rounds.zip (ask ()).oracles, echoPart, echoS⟩

/-- What comes before: one round of the shared chain, which shows this answer. -/
def frontA (x : UInt64) : Before := ⟨[(1, ⟨[.answer (x, 0, 0)], []⟩, dP 12)], []⟩

/-- The `pre` of the place of `ask` in the second chain of `F`, as `Owed.good` lays it
(Honest/Owed.lean; the two entries of `earlierOf` written out). -/
def preAsk : List (Nat × Nat × List Fmt.DeclaredRound) :=
  preOf 2 F.lastChainFirstTreeNumber [(0, 0, F.roundsDeclaredByBlocks.1), (1, 0, F.roundsDeclaredByBlocks.2.1)] F.second.blocksInOrder pAsk

#guard echoSide.fits
-- at one coin the two give the same, 9 + 5; the part is given the rounds of that very `front`, and
-- the field that it holds at `preAsk` (the next line pins its value)
#guard (frontA 9).opened (readsBefore preAsk (frontA 9)) == some []
#guard echoU.tells .own (mk ⟨1, 0⟩ (fun _ => 5) fun _ => 0) (wAt 2137) (frontA 9) [d0] [[]] ==
  some [⟨[.e (14, 0, 0)], []⟩]
#guard echoSide.shows .own echoU (mk ⟨1, 0⟩ (fun _ => 5) fun _ => 0, (), ())
  ⟨⟨wAt 2137, [], 0⟩, [], (frontA 9).seen, (frontA 9).opened (readsBefore preAsk (frontA 9))⟩ [d0]
    [[]] == some [⟨[.e (14, 0, 0)], []⟩]
-- at another `front` the simulator outputs something else
#guard echoU.tells .own (mk ⟨1, 0⟩ (fun _ => 5) fun _ => 0) (wAt 2137) (frontA 10) [d0] [[]] ==
  some [⟨[.e (15, 0, 0)], []⟩]

/-! ### The shares that parts state of their stops -/

-- stated numbers, added up as fractions; two parts as one state the sum; a placement its part's
#guard (⟨1, 1000⟩ : Odds).plus ⟨1, 16⟩ == ⟨1016, 16000⟩
#guard (lookSend.andThen lookAns).badShare == ⟨1016, 16000⟩
#guard (seat (tick (dE 1) ⟨1, 0⟩)).badShare == ⟨1, 1000⟩
#guard statedShares P.shared == (⟨1, 8⟩, ⟨0, 1⟩)
#guard statedShares P.second == (⟨0, 1⟩, ⟨1, 1⟩)

/-! ## A toy list of parts: an owner, a spender, a carrier after the spender -/

/-- The owner, at the first round of `look`. Two coins: t and u. The table's word at every position
is the index's plus t plus 2 u; one position is read, after the spender's message: whichever the
second round of `look` draws. -/
def zOwn : Part Empty L₀ Nat :=
  { takes := ⟨2, 0⟩, spends := [], carries := []
    bad := fun _ _ => none, hid := fun v _ _ => nomatch v
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [⟨fun c _ s => (c.1.fAt 0).bind fun t => (c.1.fAt 1).map fun u =>
        ⟨[], [⟨3, 1, fun p _ => toF (s.input.w₀.a p) + t + u + u⟩]⟩,
      fun _ => 7⟩] }

/-- The spender, at the second round of `look`. No coin of its own. It sends the index's answer plus
u, which it spends. -/
def zSpend : Part Empty L₀ Nat :=
  { takes := ⟨0, 0⟩, spends := [("u to the spender", ⟨1, 0⟩)], carries := []
    bad := fun _ _ => none, hid := fun v _ _ => nomatch v
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [⟨fun c _ s => (c.2.1.1.fAt 0).map fun u =>
        ⟨[.answer ⟨toF s.input.w₀.ans + u, toF 0, toF 0⟩], []⟩,
      fun s => s.own⟩] }

/-- The carrier, at the round of `ask`, after the spender. One coin of its own, r. It carries u and
t and sends the trace's last word plus r plus 3 u plus 4 t. -/
def zCarry : Part L L Nat :=
  { takes := ⟨1, 0⟩, spends := []
    carries := [("u to the carrier", ⟨1, 0⟩), ("t to the carrier", ⟨1, 0⟩)]
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [⟨fun c _ s => (c.1.fAt 0).bind fun r => (c.2.2.1.fAt 0).bind fun u =>
        (c.2.2.2.1.fAt 0).map fun t =>
          ⟨[.e ⟨toF s.input.trace.last + r + (u + u + u) + (t + t + t + t), toF 0, toF 0⟩], []⟩,
      fun s => s.own⟩] }

/-- `BlockToy.peek` that opens the second chain's own tree alone: so the table of `look` is read at
one position, in its own chain. -/
def peekOwn : Block St Nat :=
  { peek with
    rounds := [{ entry := drawT, opens := [(tree₃, .own 0)] }]
    decide := fun s _ gs => (need "peek.one-group" (gs == [[(2, [6])]])).map fun _ => s }

/-- This list's description: `BlockToy.F` with that sub-protocol, and the plan's rounds to fit. -/
def Fz : FileDescription Nat :=
  F (second := [send₃, peekOwn, ask ()])
    (plans := (thePlans.1, thePlans.2.1,
      [{ entry := drawD }, { entry := drawD }, { entry := sendR },
        { entry := drawT, opens := [(tree₃, .own 0)] }, { entry := { name := "CS", msg := 24 } }]))

def zO : Addr := ⟨pLook, 0⟩
def zP : Addr := ⟨pLook, 1⟩

/-- This list's book. -/
abbrev Bz : ProverCoinCounts :=
  { first := [], shared := [(zO, ⟨2, 0⟩)], second := [(sSend, ⟨1, 0⟩), (sAsk, ⟨1, 0⟩)]
    ahead := [⟨"u to the spender", zO, ⟨1, 0⟩, ⟨1, 0⟩, zP, true⟩,
      ⟨"u to the carrier", zO, ⟨1, 0⟩, ⟨1, 0⟩, sAsk, false⟩,
      ⟨"t to the carrier", zO, ⟨0, 0⟩, ⟨1, 0⟩, sAsk, false⟩]
    cuts := cuts₂ }

/-- A run's coins: the owner's t and u; the carrier's r. -/
def coinsZ (t u r : UInt64) : Coins Bz :=
  ⟨(), (mk ⟨2, 0⟩ (fun i => if i == 0 then t else u) fun _ => 0, ()),
    (mk ⟨1, 0⟩ (fun _ => 0) fun _ => 0, mk ⟨1, 0⟩ (fun _ => r) fun _ => 0, ())⟩

def Pz : Prover Wit₀ UInt64 Nat UInt64 Trace Nat Nat :=
  { P with first := [], shared := [⟨pLook, [zOwn, zSpend]⟩], second := [sendH, ⟨pAsk, [zCarry]⟩] }

def runZ (x : Nat) (c : Coins Bz) : Option Run := (run Fz Bz Pz w₀ 7 x c ρ none).toOption

-- the book passes all its tests, and the description accepts (the instance changes with the
-- column)
#guard Bz.word Fz == none
#guard say Fz Bz Pz w₀ 7 2145 (coinsZ 2 3 4) ρ none == "yes"
-- the run reads the owner's table at one position; the owner's coins are added at every position
#guard (runZ 2145 (coinsZ 2 3 4)).map (·.askedAt zO) == some [[[4]]]
-- at another list another one: there too the owner's word is under its coins (0 + 2 + 6)
#guard ((run Fz Bz Pz w₀ 7 2145 (coinsZ 2 3 4) { ρ with shared := [dE 5, dP 13, dP 3] }
  none).toOption.map fun r => (r.askedAt zO, r.shownAt zO)) ==
    some ([[[5]]], [⟨[], [[(5, [8])]]⟩])
-- what each of the three shows: 100 + 2 + 6; 9 + 3; 9 + 4 + 9 + 8
#guard (runZ 2145 (coinsZ 2 3 4)).map (fun r => (r.shownAt zO, r.shownAt zP, r.shownAt sAsk)) ==
  some ([⟨[], [[(4, [108])]]⟩], [⟨[.answer (12, 0, 0)], []⟩], [⟨[.e (30, 0, 0)], []⟩])
-- which entries `Good.fresh` reads. For the spender: it spends u; nothing else of the owner's is
-- given to it or to a part before it: the carrier is after it. For the carrier: it spends nothing;
-- all three entries give coins of the owner's to it or to a part before it
#guard (Bz.spentBy zO zP).map (·.name) == ["u to the spender"]
#guard (Bz.knownBy (orderOf Fz) zO zP).map (·.name) == []
#guard (Bz.spentBy zO sAsk).map (·.name) == []
#guard (Bz.knownBy (orderOf Fz) zO sAsk).map (·.name) ==
  ["u to the spender", "u to the carrier", "t to the carrier"]
#guard (cutAll (mk ⟨2, 0⟩ (fun i => if i == 0 then 2 else 3) fun _ => 0) (Bz.spentBy zO zP)).isSome
#guard (cutAll (mk ⟨1, 0⟩ (fun _ => 2) fun _ => 0) (Bz.spentBy zO zP)).isNone
-- the same list with spender and carrier the other way round: the eighth test fails
#guard ({ Bz with ahead := [⟨"u to the last", zO, ⟨1, 0⟩, ⟨1, 0⟩, sAsk, true⟩,
    ⟨"u to the middle", zO, ⟨1, 0⟩, ⟨1, 0⟩, zP, false⟩] } : ProverCoinCounts).word Fz ==
  some "a coin that a part spends is handed to a part in front of it, or to itself as carried"

/-- Three toy simulators: each shows one coin of its own, and reads nothing that it is given but the
positions asked (`zS₀`). -/
def zS₀ : Sim UInt64 :=
  { addr := zO, takes := ⟨1, 0⟩
    tell := fun _ _ _ asks c => some [⟨[], (asks.headD []).map fun ps => ps.map fun p =>
      (p, [ofF (c.f ⟨0, by decide⟩)])⟩] }
def zS₁ : Sim UInt64 :=
  { addr := zP, takes := ⟨1, 0⟩
    tell := fun _ _ _ _ c => some [⟨[.answer (ofF (c.f ⟨0, by decide⟩), 0, 0)], []⟩] }
def zS₂ : Sim Nat :=
  { addr := sAsk, takes := ⟨1, 0⟩
    tell := fun _ _ _ _ c => some [⟨[.e (ofF (c.f ⟨0, by decide⟩), 0, 0)], []⟩] }

def zSide : Side St Nat Empty L₀ Nat UInt64 :=
  { block := look [(3, 1)] true (), row := [(zOwn, zS₀), (zSpend, zS₁)] }
def zSide₂ : Side St Nat L L Nat Nat := { block := ask (), row := [(zCarry, zS₂)] }
def zU₀ : Member Empty L₀ Nat UInt64 := ⟨0, lookRounds.take 1, zOwn, zS₀⟩
def zU₁ : Member Empty L₀ Nat UInt64 := ⟨1, lookRounds.drop 1, zSpend, zS₁⟩
def zU₂ : Member L L Nat Nat := ⟨0, (ask ()).rounds.zip (ask ()).oracles, zCarry, zS₂⟩

/-- One coin of the base field. -/
def coin₁ (x : UInt64) : Cs ⟨1, 0⟩ := mk ⟨1, 0⟩ (fun _ => x) fun _ => 0
/-- The owner's two coins. -/
def coin₂ (t u : UInt64) : Cs ⟨2, 0⟩ := mk ⟨2, 0⟩ (fun i => if i == 0 then t else u) fun _ => 0
/-- The state of the second chain's run before the carrier, as far as the carrier reads it. The
field `opened` is `some []`: what `Before.opened` gives at `none₀`, beside which this state is set,
so that the pair meets the premise of `Good.exact` on the field (Honest/Side.lean). It is no run's
own value: in a run of `runC` the earlier chains' columns stand there. -/
def midZ : Mid L Nat := ⟨⟨wAt 2145, [], 0⟩, [], [], some []⟩

-- its field is what `none₀` holds for the reads of declared rounds, at no round
#guard midZ.opened == none₀.opened (readsBefore [] none₀)

#guard zSide.fits && zSide₂.fits
-- the two sides' prover's sides are those that this list's prover plays
#guard sameOutcome (outcome Fz Bz { Pz with shared := [zSide.half], second := [sendH, zSide₂.half] }
  w₀ 7 2145 (coinsZ 2 3 4) ρ) (outcome Fz Bz Pz w₀ 7 2145 (coinsZ 2 3 4) ρ)
-- evaluations at fixed coins, no lemma.
-- the owner, at the positions that this list's own run reads: at (t, u) = (2, 3) and at (4, 2) it
-- shows the same column; at (2, 2) another. Its simulator, at the coin 108, outputs that column
#guard zSide.shows .shared zU₀ (coin₂ 2 3, (), ()) mid₀ [dE 5] [[[4]]] ==
  zSide.shows .shared zU₀ (coin₂ 4 2, (), ()) mid₀ [dE 5] [[[4]]]
#guard zSide.shows .shared zU₀ (coin₂ 2 3, (), ()) mid₀ [dE 5] [[[4]]] !=
  zSide.shows .shared zU₀ (coin₂ 2 2, (), ()) mid₀ [dE 5] [[[4]]]
#guard zU₀.tells .shared (coin₁ 108) ⟨w₀, 7, 0⟩ none₀ [dE 5] [[[4]]] ==
  zSide.shows .shared zU₀ (coin₂ 2 3, (), ()) mid₀ [dE 5] [[[4]]]
-- the spender: what it shows changes with the block that it spends; its simulator, at the coin 12,
-- outputs what it shows at u = 3; the state has the field that this `front` holds at the `pre` of
-- the place of `look` in `Fz` (the first line pins its value)
#guard (mid₁At (preOf 1 0 [] Fz.shared.blocksInOrder pLook)
    ⟨[(1, ⟨[], [[(4, [108])]]⟩, dE 5)], []⟩).opened == some []
#guard zU₁.tells .shared (coin₁ 12) ⟨w₀, 7, 0⟩ ⟨[(1, ⟨[], [[(4, [108])]]⟩, dE 5)], []⟩ [dP 12] [[]]
    ==
  zSide.shows .shared zU₁ (Cs.empty, (coin₁ 3, ()), ())
    (mid₁At (preOf 1 0 [] Fz.shared.blocksInOrder pLook) ⟨[(1, ⟨[], [[(4, [108])]]⟩, dE 5)], []⟩) [dP 12]
    [[]]
#guard zSide.shows .shared zU₁ (Cs.empty, (coin₁ 3, ()), ()) mid₁ [dP 12] [[]] !=
  zSide.shows .shared zU₁ (Cs.empty, (coin₁ 4, ()), ()) mid₁ [dP 12] [[]]
-- the carrier: at two pairs of carried blocks, each with a coin of its own chosen to fit, it shows
-- the same; its simulator, which is given neither block, outputs that at the coin 30
#guard zSide₂.shows .own zU₂ (coin₁ 4, (), (coin₁ 3, coin₁ 2, ())) midZ [d0] [[]] ==
  zSide₂.shows .own zU₂ (coin₁ 14, (), (coin₁ 1, coin₁ 1, ())) midZ [d0] [[]]
#guard zU₂.tells .own (coin₁ 30) (wAt 2145) none₀ [d0] [[]] ==
  zSide₂.shows .own zU₂ (coin₁ 4, (), (coin₁ 3, coin₁ 2, ())) midZ [d0] [[]]

/-! ## What a statement about lists of parts would take as its hypotheses -/

/-! ### The one silent set -/

-- computed from the stops alone, it says what `stopOf` says at coins: both kinds of stop; no stop
#guard silentAt F P w₀ 7 2137 ρ₁₃ == some .bad && stopOf F B P w₀ 7 2137 zero ρ₁₃ == some .bad
#guard silentAt F P w₀ 7 2141 ρ == some .hid && stopOf F B P w₀ 7 2141 zero ρ == some .hid
#guard silentAt F P w₀ 7 2137 ρ == none && stopOf F B P w₀ 7 2137 zero ρ == none
-- a stop after a part's last challenge; a stop of the list of two, each part on its own challenge
#guard silentAt F P w₀ 7 2137 { ρ with shared := [dE 5, dP 13, dP 3] } == some .bad
#guard silentAt F P₂ w₀ 7 2137 ρ₁₃ == some .bad
#guard silentAt F P₂ w₀ 7 2137 { ρ with shared := [dE 5, dP 13, dP 3] } == some .bad
-- where a fault comes first `stopOf` returns `unfit` and `hidAt` false; the silent set still says
-- `hid`: at the instance whose trace ends in 5, with a prover's side that asks a coin beyond its
-- count
#guard stopOf F B { P with shared := [lookAt ⟨2, 1⟩ 2] } w₀ 7 2141 zero ρ == some .unfit
#guard !hidAt F B { P with shared := [lookAt ⟨2, 1⟩ 2] } w₀ 7 2141 zero ρ
#guard silentAt F { P with shared := [lookAt ⟨2, 1⟩ 2] } w₀ 7 2141 ρ == some .hid

-- the second chain's stops are given the first and the second chain's challenges alone, here as in
-- `play`: a part that stops unless eight come before it does not stop; unless eleven: it does
#guard silentAt F { P with second := [sendH, askAt false (some 8)] } w₀ 7 2137 ρ == none
#guard silentAt F { P with second := [sendH, askAt false (some 11)] } w₀ 7 2137 ρ == some .bad

/-! ### The example's lists as one value of `Sides` -/

/-- A simulator that outputs `none`: for a part with which this file pairs none. -/
def nilS {Pb : Type} (a : Addr) : Sim Pb :=
  { addr := a, takes := ⟨0, 0⟩, tell := fun _ _ _ _ _ => none }

/-- A list at a place, with parameters that ask nothing. -/
def lett {S Cl V W Pb : Type} (a : Place) (row : List (Part V W Nat × Sim Pb)) :
    Lettered B S Cl V W Nat Pb :=
  ⟨a, row, fun _ _ _ _ => True, fun _ _ _ _ => True, fun _ _ _ _ => True, fun _ _ _ => True⟩

/-- The example's four prover's sides, as lists at their places. -/
def tG : Sides F B Wit₀ UInt64 UInt64 Trace Nat Nat :=
  { first := [lett pHear (hearH.parts.map fun p => (p, nilS sHear))]
    shared := [lett pLook [(lookPart ⟨2, 1⟩, lookS)]]
    second := [lett pSend [(sendPart, nilS sSend)], lett pAsk [(askPart false none, askS)]] }

-- every list is at a place of its chain; one that is at none
#guard tG.seated
#guard !({ tG with first := [lett ⟨1, none, 77, .frame⟩ []] } :
  Sides F B Wit₀ UInt64 UInt64 Trace Nat Nat).seated
-- a list of the shared chain's place, put in the first chain's list: at no place there
#guard !({ tG with first := [lett pLook []] } : Sides F B Wit₀ UInt64 UInt64 Trace Nat Nat).seated
-- the side's sub-protocol is the description's own sub-protocol at the place
#guard (tG.shared.head?.bind fun L => L.side F.shared.blocksInOrder).map (·.block.name) == some "look"
-- the prover whose sides are these lists, over a prover without a prover's side, has the outcome of
-- the example's prover
#guard sameOutcome (outcome F B (tG.prover P₀) w₀ 7 2137 (coins 9 2 5 3 4) ρ)
  (outcome F B P w₀ 7 2137 (coins 9 2 5 3 4) ρ)
#guard (outcome F B (tG.prover P₀) w₀ 7 2137 (coins 9 2 5 3 4) ρ).isSome
#guard !sameOutcome (outcome F B P₀ w₀ 7 2137 (coins 9 2 5 3 4) ρ)
  (outcome F B P w₀ 7 2137 (coins 9 2 5 3 4) ρ)

/-! ### A run's own values at an address -/

-- `Owed` takes the state from `midAtW` and `midSharedAtW` (Honest/MidW.lean), which no line here
-- evaluates; these lines are on `midAt` and `midSharedAt`.

/-- Of the state of a run: what was passed on; how many challenges were heard; how many the stops
may read; how many rounds were shown. -/
def four {W : Type} (m : Mid W Nat) : Nat × Nat × Nat × Nat :=
  (m.st.own, m.st.heard.length, m.loc.length, m.seen.length)

-- before `ask`: 42 + 7, eleven heard, eight for the stops, eleven shown: as `mid₄₉` has it by
-- hand
#guard (midAt F B P w₀ 7 2137 zero ρ sAsk).toOption.map four == some (four mid₄₉)
-- before `hear`: the start; between the two parts of `look`: 7 passed on, one round
#guard (midAt F B P w₀ 7 2137 zero ρ sHear).toOption.map four == some (0, 0, 0, 0)
#guard (midSharedAt F Bp P₂ w₀ 7 2137 (coinsP 0 0 0 0 0) ρ ⟨pLook, 1⟩).toOption.map four ==
  some (four mid₁)
#guard four mid₁ == (7, 1, 1, 1)
-- `four` does not read the field `opened`: both functions return `none` there, as `mid₄₉` and
-- `mid₁` have it by hand
#guard (midAt F B P w₀ 7 2137 zero ρ sAsk).toOption.map (·.opened.isNone) == some true
#guard (midSharedAt F Bp P₂ w₀ 7 2137 (coinsP 0 0 0 0 0) ρ ⟨pLook, 1⟩).toOption.map
    (·.opened.isNone) == some true
#guard mid₄₉.opened.isNone && mid₁.opened.isNone
-- the part, played alone from what `midSharedAt` returns, shows what the run shows at its
-- address
#guard ((midSharedAt F Bp P₂ w₀ 7 2139 (coinsP 0 2 2 3 0) ρ ⟨pLook, 1⟩).toOption.bind fun m =>
    lookSide₂.shows .shared lookU₁ (mk ⟨0, 1⟩ (fun _ => 0) fun _ => 3, (), ()) m [dP 12] [[]]) ==
  (run F Bp P₂ w₀ 7 2139 (coinsP 0 2 2 3 0) ρ none).toOption.map (·.shownAt ⟨pLook, 1⟩)
#guard (run F Bp P₂ w₀ 7 2139 (coinsP 0 2 2 3 0) ρ none).toOption.isSome
-- an address of another chain, and one at which there is no round: an error
#guard (midAt F B P w₀ 7 2137 zero ρ sLook).toOption.isNone
#guard (midSharedAt F B P w₀ 7 2137 zero ρ sAsk).toOption.isNone
#guard (midAt F B P w₀ 7 2137 zero ρ ⟨pAsk, 1⟩).toOption.isNone
-- what `ask` carries, of a run's coins: the second coin of `look`
#guard ((carriedAt B (coins 9 2 5 3 4) 2 sAsk (askPart false none)).toOption.bind fun c =>
    (c.1.fAt 0).toOption.map ofF) == some 5

/-! ### Two toy examples that fail these hypotheses

Whether they meet the fields of `Good` no line here checks: these lines are on the failing alone; of
the second it is read, not tested: see there. -/

/-- A bound that reads challenges. The prover's side for `look`, without a stop: the table; then the
answer by itself if the first challenge was the element 13, else the answer plus the part's coin. -/
def part₁₃ : Part Empty L₀ Nat :=
  { takes := ⟨0, 1⟩, spends := [], carries := []
    bad := fun _ _ => none, hid := fun v _ _ => nomatch v
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [
      ⟨fun _ _ t => .ok ⟨[], [⟨3, 1, fun p _ => toF (t.input.w₀.a p)⟩]⟩, fun t => t.own⟩,
      ⟨fun c _ t => (c.1.eAt 0).map fun k =>
          ⟨[.answer (if t.heard.head? == some (dE 13) then ⟨toF t.input.w₀.ans, toF 0, toF 0⟩
            else ⟨toF t.input.w₀.ans + k.c0, k.c1, k.c2⟩)], []⟩,
        fun t => t.own⟩] }

/-- The bound under which that part's condition asks nothing at 13: as a test. -/
def bud₁₃ (ds : List Fmt.Drawn) : Bool := ds.head? != some (dE 13)

/-- The example's prover with that part, at a book to fit. -/
def PL : Prover Wit₀ UInt64 Nat UInt64 Trace Nat Nat :=
  { P with first := [], shared := [⟨pLook, [part₁₃]⟩], second := [sendH, askTyped [] []] }
abbrev BL : ProverCoinCounts :=
  { first := [], shared := [(sLook, ⟨0, 1⟩)], second := [(sSend, ⟨1, 0⟩)], ahead := []
    cuts := cuts₁ }
def coinsL (e : UInt64) : Coins BL :=
  ⟨(), (mk ⟨0, 1⟩ (fun _ => 0) fun _ => e, ()), (mk ⟨1, 0⟩ (fun _ => 0) fun _ => 0, ())⟩

-- at the list with 13: the challenges are such as the rounds can draw; the list is outside the
-- silent set; the run goes through; and at two coins it shows one answer: the index's own
#guard BL.word F == none && ρ₁₃.due F && silentAt F PL w₀ 7 2137 ρ₁₃ == none
#guard ((run F BL PL w₀ 7 2137 (coinsL 3) ρ₁₃ none).toOption.map (·.shownAt sLook)) ==
  ((run F BL PL w₀ 7 2137 (coinsL 4) ρ₁₃ none).toOption.map (·.shownAt sLook))
#guard (run F BL PL w₀ 7 2137 (coinsL 3) ρ₁₃ none).toOption.isSome
-- there the bound, at the run's own challenges, returns false: so `Owed.owed`, which needs it as a
-- conclusion at every such list, fails at this bound (`Owed` reads `runC`'s run: that its
-- challenges there are these is read, not tested)
#guard ((run F BL PL w₀ 7 2137 (coinsL 3) ρ₁₃ none).toOption.map fun r =>
    bud₁₃ (r.drawnAt sLook)) == some false
-- at the example's own list it returns true, and two coins show two answers
#guard ((run F BL PL w₀ 7 2137 (coinsL 3) ρ none).toOption.map fun r =>
    bud₁₃ (r.drawnAt sLook)) == some true
#guard ((run F BL PL w₀ 7 2137 (coinsL 3) ρ none).toOption.map (·.shownAt sLook)) !=
  ((run F BL PL w₀ 7 2137 (coinsL 4) ρ none).toOption.map (·.shownAt sLook))

/-- A condition at the entry that ties the index to the instance: "the instance is the answer": as a
test. -/
def tieOn (m : Mid L Nat) : Bool := m.st.input.x == m.st.input.w₀.ans.toNat

-- at what `midAt` returns at the example's own run it returns false. It reads the state's input
-- alone. `Owed.owed` (Honest/Owed.lean) asks a condition at the entry at what `midAtW` returns
-- (Honest/MidW.lean), which no line of this file evaluates. That `Owed.owed` fails at this
-- condition, unless the relation on inputs, which the side's author does not supply, holds such
-- inputs alone, rests on reading that `midAtW`'s state has the same input and that the part is
-- called. It is not tested here
#guard (midAt F B P w₀ 7 2137 zero ρ sAsk).toOption.map tieOn == some false
#guard silentAt F P w₀ 7 2137 ρ == none && (run F B P w₀ 7 2137 zero ρ none).toOption.isSome

/-! ## The shapes' test by itself -/

#guard Sending.fits ⟨[], [⟨3, 1, fun _ _ => toF 0⟩]⟩
  { entry := { name := "CS", msg := 32, roots := 1 } } [orc (3, 1) true]
#guard !Sending.fits ⟨[], [⟨2, 1, fun _ _ => toF 0⟩]⟩
  { entry := { name := "CS", msg := 32, roots := 1 } } [orc (3, 1) true]

end ProofFile.Honest.Toy

#print axioms ProofFile.Honest.Toy.Wit₀
#print axioms ProofFile.Honest.Toy.Trace
#print axioms ProofFile.Honest.Toy.w₀
#print axioms ProofFile.Honest.Toy.L
#print axioms ProofFile.Honest.Toy.L₀
#print axioms ProofFile.Honest.Toy.pHear
#print axioms ProofFile.Honest.Toy.pLook
#print axioms ProofFile.Honest.Toy.pSend
#print axioms ProofFile.Honest.Toy.pAsk
#print axioms ProofFile.Honest.Toy.sHear
#print axioms ProofFile.Honest.Toy.sLook
#print axioms ProofFile.Honest.Toy.sSend
#print axioms ProofFile.Honest.Toy.sAsk
#print axioms ProofFile.Honest.Toy.dE
#print axioms ProofFile.Honest.Toy.dP
#print axioms ProofFile.Honest.Toy.d0
#print axioms ProofFile.Honest.Toy.toAsk₁
#print axioms ProofFile.Honest.Toy.toAsk₂
#print axioms ProofFile.Honest.Toy.toAsk₃
#print axioms ProofFile.Honest.Toy.nHear
#print axioms ProofFile.Honest.Toy.nLook
#print axioms ProofFile.Honest.Toy.nSend
#print axioms ProofFile.Honest.Toy.cuts₁
#print axioms ProofFile.Honest.Toy.cuts₂
#print axioms ProofFile.Honest.Toy.B
#print axioms ProofFile.Honest.Toy.mk
#print axioms ProofFile.Honest.Toy.coins
#print axioms ProofFile.Honest.Toy.zero
#print axioms ProofFile.Honest.Toy.quiet
#print axioms ProofFile.Honest.Toy.hearH
#print axioms ProofFile.Honest.Toy.lookPart
#print axioms ProofFile.Honest.Toy.lookAt
#print axioms ProofFile.Honest.Toy.lookH
#print axioms ProofFile.Honest.Toy.sendPart
#print axioms ProofFile.Honest.Toy.sendH
#print axioms ProofFile.Honest.Toy.askPart
#print axioms ProofFile.Honest.Toy.askAt
#print axioms ProofFile.Honest.Toy.askH
#print axioms ProofFile.Honest.Toy.askTyped
#print axioms ProofFile.Honest.Toy.P
#print axioms ProofFile.Honest.Toy.P₀
#print axioms ProofFile.Honest.Toy.ρ
#print axioms ProofFile.Honest.Toy.U
#print axioms ProofFile.Honest.Toy.U₅
#print axioms ProofFile.Honest.Toy.vA
#print axioms ProofFile.Honest.Toy.shows
#print axioms ProofFile.Honest.Toy.line
#print axioms ProofFile.Honest.Toy.at_
#print axioms ProofFile.Honest.Toy.lookM
#print axioms ProofFile.Honest.Toy.B₂
#print axioms ProofFile.Honest.Toy.ρ₁₃
#print axioms ProofFile.Honest.Toy.firstCoin
#print axioms ProofFile.Honest.Toy.lookSend
#print axioms ProofFile.Honest.Toy.lookAns
#print axioms ProofFile.Honest.Toy.lookTwo
#print axioms ProofFile.Honest.Toy.lookOne
#print axioms ProofFile.Honest.Toy.Bp
#print axioms ProofFile.Honest.Toy.coinsP
#print axioms ProofFile.Honest.Toy.P₂
#print axioms ProofFile.Honest.Toy.P₁
#print axioms ProofFile.Honest.Toy.inLook
#print axioms ProofFile.Honest.Toy.Bq
#print axioms ProofFile.Honest.Toy.coinsQ
#print axioms ProofFile.Honest.Toy.PQ
#print axioms ProofFile.Honest.Toy.Br
#print axioms ProofFile.Honest.Toy.sFront
#print axioms ProofFile.Honest.Toy.cutA
#print axioms ProofFile.Honest.Toy.cutB
#print axioms ProofFile.Honest.Toy.Bc
#print axioms ProofFile.Honest.Toy.Bj
#print axioms ProofFile.Honest.Toy.coinsC
#print axioms ProofFile.Honest.Toy.coinsJ
#print axioms ProofFile.Honest.Toy.PC
#print axioms ProofFile.Honest.Toy.vC
#print axioms ProofFile.Honest.Toy.tick
#print axioms ProofFile.Honest.Toy.seat
#print axioms ProofFile.Honest.Toy.hearTwo
#print axioms ProofFile.Honest.Toy.Bh
#print axioms ProofFile.Honest.Toy.zeroH
#print axioms ProofFile.Honest.Toy.runAt
#print axioms ProofFile.Honest.Toy.stOf
#print axioms ProofFile.Honest.Toy.bf
#print axioms ProofFile.Honest.Toy.lookS
#print axioms ProofFile.Honest.Toy.lookSide
#print axioms ProofFile.Honest.Toy.none₀
#print axioms ProofFile.Honest.Toy.lookRounds
#print axioms ProofFile.Honest.Toy.lookU
#print axioms ProofFile.Honest.Toy.mid₀
#print axioms ProofFile.Honest.Toy.sPeek
#print axioms ProofFile.Honest.Toy.lookS₀
#print axioms ProofFile.Honest.Toy.lookS₁
#print axioms ProofFile.Honest.Toy.lookSide₂
#print axioms ProofFile.Honest.Toy.lookU₀
#print axioms ProofFile.Honest.Toy.lookU₁
#print axioms ProofFile.Honest.Toy.mid₁
#print axioms ProofFile.Honest.Toy.mid₁At
#print axioms ProofFile.Honest.Toy.preLook
#print axioms ProofFile.Honest.Toy.runP
#print axioms ProofFile.Honest.Toy.askS
#print axioms ProofFile.Honest.Toy.askSide
#print axioms ProofFile.Honest.Toy.askU
#print axioms ProofFile.Honest.Toy.wAt
#print axioms ProofFile.Honest.Toy.askCoins
#print axioms ProofFile.Honest.Toy.mid₄₉
#print axioms ProofFile.Honest.Toy.answerIn
#print axioms ProofFile.Honest.Toy.echoPart
#print axioms ProofFile.Honest.Toy.echoS
#print axioms ProofFile.Honest.Toy.echoSide
#print axioms ProofFile.Honest.Toy.echoU
#print axioms ProofFile.Honest.Toy.frontA
#print axioms ProofFile.Honest.Toy.preAsk
#print axioms ProofFile.Honest.Toy.zOwn
#print axioms ProofFile.Honest.Toy.zSpend
#print axioms ProofFile.Honest.Toy.zCarry
#print axioms ProofFile.Honest.Toy.peekOwn
#print axioms ProofFile.Honest.Toy.Fz
#print axioms ProofFile.Honest.Toy.zO
#print axioms ProofFile.Honest.Toy.zP
#print axioms ProofFile.Honest.Toy.Bz
#print axioms ProofFile.Honest.Toy.coinsZ
#print axioms ProofFile.Honest.Toy.Pz
#print axioms ProofFile.Honest.Toy.runZ
#print axioms ProofFile.Honest.Toy.zS₀
#print axioms ProofFile.Honest.Toy.zS₁
#print axioms ProofFile.Honest.Toy.zS₂
#print axioms ProofFile.Honest.Toy.zSide
#print axioms ProofFile.Honest.Toy.zSide₂
#print axioms ProofFile.Honest.Toy.zU₀
#print axioms ProofFile.Honest.Toy.zU₁
#print axioms ProofFile.Honest.Toy.zU₂
#print axioms ProofFile.Honest.Toy.coin₁
#print axioms ProofFile.Honest.Toy.coin₂
#print axioms ProofFile.Honest.Toy.midZ
#print axioms ProofFile.Honest.Toy.nilS
#print axioms ProofFile.Honest.Toy.lett
#print axioms ProofFile.Honest.Toy.tG
#print axioms ProofFile.Honest.Toy.four
#print axioms ProofFile.Honest.Toy.part₁₃
#print axioms ProofFile.Honest.Toy.bud₁₃
#print axioms ProofFile.Honest.Toy.PL
#print axioms ProofFile.Honest.Toy.BL
#print axioms ProofFile.Honest.Toy.coinsL
#print axioms ProofFile.Honest.Toy.tieOn
