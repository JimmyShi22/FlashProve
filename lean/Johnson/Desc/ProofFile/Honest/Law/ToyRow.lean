-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/ToyRow.lean: a toy example: five parts at a toy description of its
own, with parameters for `Good` (Honest/Side.lean). Definitions and `#guard` lines, as in
Honest/FrameToy.lean, on which it builds. No theorem is stated here: the theorems about these
objects are in Honest/Law/ToyExact.lean and Honest/Law/ToyGood.lean.

The lines that begin with `#guard` are tests, checked by evaluation: Lean's evaluator runs each of
them when the file is compiled, and the build fails if one is false. The kernel does not check them,
and they prove nothing.

The parts. Three of the five parts are those of Honest/FrameToy.lean: the owner `zOwn`, the spender
`zSpend`, the carrier `zCarry`. Two are new.
  `ySend`   a second owner, at the round of `send`: one coin v; its table's word at every position
     is the trace's word plus v
  `yTell`   at a sub-protocol of two rounds, `tellB`: it carries v; its first round sends nothing
     and draws a position, at which the table of `ySend` is read; its second round says that table's
     word at that position, which it computes from the trace and v
  `yS₃`   its simulator reads what comes before: it looks the column up in `front`, at the position
     that the part's own first challenge draws, and says its word
The decision of `tellB` compares the word that is said with the column that is read. `askQ` is
`BlockToy.ask` without its tests (among them the one on the running total, which changes with a
column that holds coins). `storeY` is `BlockToy.table` with a decision that accepts any column. The
description `Fy` has no sub-protocol that rejects the example's own run at any list that its rounds
can draw: that is meant; the lines try it at 24 lists.

  1  `ySend`, `posOf`, `yTell`, `sameWord`, `tellB`, `askQ`, `storeY`, `Fy`, `By`, `coinsY`, `Py`,
     `ρy`   the parts, the description, the book, the prover, the challenges
  2  `yS₂`, `yS₃`, `ySide₂`, `ySide₃`, `ySide₄`   the simulators and the sides
  3  `onePos`, `onTell`, `coinAt`, `hasTree`, and the parameters   what is supplied for A, B, On and
     `bud`
  4  `yLook`, `ySendL`, `yTellL`, `yCarryL`, `Gy`, `RelY`   the lists of parts with their
     parameters, as one value of `Sides` (Honest/Rule.lean); the inputs
  5  the `#guard` lines

What the lines check. The description passes its tests on the plan, the book its eleven tests, and
the description accepts at each of the 24 lists of challenges that are tried: 16 + 8, of which one
(p = 12, q = 6) is in both rows, and one more (p = 13, q = 7) at another word of `Rc`, another
request and other coins. At each of the 16 positions that the second round of `look` can draw, and
at each of the 8 that the first round of `tellB` can draw: the list is one that the rounds can draw,
it is outside the silent set, the run goes through, and the parameters On and `bud`, as tests,
return true at that run's own values (`owedTest`). (The lines at changed objects are in
Honest/Law/ToyBadLines.lean, which is not in the sealed library and which its build does not check.)
Evaluations at fixed coins and at the 23 lists of the two rows: no lemma.

Limits.
  * A toy example: toy prover's sides, none of a kind of the protocol.
  * The lines try what the fields `runs` and `owed` of `Owed` ask, with `run` at `Py` in the place
    of `runC` at `Gy.prover` and `midAt` in the place of `midAtW`, at 23 lists and one list of
    coins, not at all lists and all coins.
  * No part of this file reads the field `opened`, and no line evaluates a state whose field holds a
    column: at `sTell`, where the walk's own state holds the earlier chains' columns (read off
    Honest/Walk.lean, not tested here), `midAt` hands `none`. `run` and `midAt` hand no columns
    (`none`: read off Honest/Frame.lean, not tested here). `midY`, which is set beside a simulator's
    output at `none₀`, has `some []`, so that that pair meets the premise of `Good.exact` on the
    field (at `none₀` no read is made, whatever rounds are declared: by reading; two lines test it,
    at no round and at the `pre` that `Owed.good` lays before `pTell`); its pair with `frontY` meets
    that premise at that `pre` too (as at every `pre`, by reading: its one challenge draws no
    position, and it lists no round of the earlier chains; at the run's own `front` that `pre`
    brings reads: a line tests it), and not the one on `seen` (a line tests each); at
    `{ midY with seen := (frontY 2 11).seen }` both are met, and a line sets what the part shows
    there beside what the simulator outputs at `frontY`.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.FrameToy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Toy
open VerifiableInference.Desc (Place Block FileDescription need)
open VerifiableInference.Desc.BlockToy (St look send₃ ask table tree₃ drawT sealB frontQ endQ)
open OnBytes.Slice (toF toE ofF ofE)

/-! ## 1 The parts, the description, the book, the prover -/

/-- The second owner, at the round of `send`. One coin, v. The table's word at every position is the
trace's plus v; one position is read: whichever the first round of `tellB` draws. -/
def ySend : Part L L Nat :=
  { takes := ⟨1, 0⟩, spends := [], carries := []
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [⟨fun c _ s => (c.1.fAt 0).map fun v =>
        ⟨[], [⟨2, 1, fun p _ => toF (s.input.trace.b p) + v⟩]⟩,
      fun s => s.own⟩] }

/-- The position that a challenge draws, in the range of the table of `send`; 0 if it draws none. -/
def posOf (d : Fmt.Drawn) : Nat := d.poss.headD 0 % 2 ^ 2

/-- The part `yTell`. No coin of its own; it carries v. Its first round sends nothing and draws a
position. Its second round says the word of the table of `ySend` at that position: the trace's word
there plus v. -/
def yTell : Part L L Nat :=
  { takes := ⟨0, 0⟩, spends := [], carries := [("v to the teller", ⟨1, 0⟩)]
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [
      ⟨fun _ _ _ => .ok ⟨[], []⟩, fun s => s.own⟩,
      ⟨fun c _ s => (c.2.2.1.fAt 0).map fun v =>
          ⟨[.e ⟨toF (s.input.trace.b (posOf (s.heard.getLast?.getD d0))) + v, toF 0, toF 0⟩], []⟩,
        fun s => s.own⟩] }

def pTell : Place := ⟨3, some 0, 5, .K12⟩
def sTell : Addr := ⟨pTell, 0⟩

/-- One group of one column of one word w; a round without an item, and a round whose one item is
the element (w, 0, 0): an executable test. -/
def sameWord : List (List (Nat × List UInt64)) → List (List Fmt.ItemValue) → Bool
  | [[(_, [w])]], [[], [.e y]] => y == (w, 0, 0)
  | _, _ => false

/-- The sub-protocol of `yTell`: a round that draws one position below 8 and opens the second
chain's own tree there; a round that sends one element. It asks that the element is the column's one
word. -/
def tellB : Block St Nat :=
  { name := "tell", place := pTell, planOk := true
    rounds := [{ entry := drawT, opens := [(tree₃, .own 0)] },
      { entry := { name := "CS", msg := 24 } }]
    oracles := [[], []]
    before := [(3, 0)]
    decide := fun s rs gs =>
      (need "tell.the-word" (sameWord gs (rs.map (·.vals)))).map fun _ => s
    claims := [], after := [] }

/-- `BlockToy.ask` without its two tests. -/
def askQ : Block St Nat := { ask () with decide := fun s _ _ => .ok s }

/-- One group of one column of two words. -/
def oneOfTwo : List (List (Nat × List UInt64)) → Bool
  | [[(_, [_, _])]] => true
  | _ => false

/-- `BlockToy.table`, which draws a position and reads a part of a stored table there, with another
decision: it accepts any one column of two words. There is no prover's side at it. -/
def storeY : Block St Nat :=
  { table with
    name := "store"
    decide := fun s _ gs => (need "store.one-column-of-two-words" (oneOfTwo gs)).map fun _ => s }

/-- **The example's own description.** First chain: its front, the sealing round. Shared chain: its
front, `look`, `storeY`. Second chain: its front, `send`, `tellB`, `askQ`, its end. The second
chain's start and the last test ask nothing. -/
def Fy : FileDescription Nat where
  S₁ := St
  S₂ := St
  S₃ := St
  Cl := Nat
  plans := (sealB.rounds, (look [(3, 1)] true ()).rounds ++ storeY.rounds,
    send₃.rounds ++ tellB.rounds ++ askQ.rounds)
  tableDepth := 3
  wanted := []
  owed := []
  fileOk := true
  okStart := fun _ => true
  XiPub := Unit
  pub := fun _ => ()
  start₁ := fun _ => ⟨0, none, 0⟩
  start₂ := fun _ => ⟨0, none, 0⟩
  start₃ := fun _ _ _ => .ok ⟨0, none, 0⟩
  first := ⟨frontQ 1, [], [], [], sealB⟩
  shared := ⟨frontQ 2, [look [(3, 1)] true ()], [], [], storeY⟩
  second := ⟨frontQ 3, [send₃, tellB, askQ], [], [], endQ⟩
  fin := fun _ _ _ _ => true

/-- The example's book: the `Bz` of Honest/FrameToy.lean with one entry more, and its own cut. -/
abbrev By : ProverCoinCounts :=
  { first := [], shared := [(zO, ⟨2, 0⟩)], second := [(sSend, ⟨1, 0⟩), (sAsk, ⟨1, 0⟩)]
    ahead := [⟨"u to the spender", zO, ⟨1, 0⟩, ⟨1, 0⟩, zP, true⟩,
      ⟨"u to the carrier", zO, ⟨1, 0⟩, ⟨1, 0⟩, sAsk, false⟩,
      ⟨"t to the carrier", zO, ⟨0, 0⟩, ⟨1, 0⟩, sAsk, false⟩,
      ⟨"v to the teller", sSend, ⟨0, 0⟩, ⟨1, 0⟩, sTell, false⟩]
    cuts := [(pLook, [1, 1]), (pSend, [1]), (pTell, [2]), (pAsk, [1])] }

/-- A run's coins: the first owner's t and u; the second owner's v; the carrier's r. -/
def coinsY (t u v r : UInt64) : Coins By := ⟨(), (coin₂ t u, ()), (coin₁ v, coin₁ r, ())⟩

def Py : Prover Wit₀ UInt64 Nat UInt64 Trace Nat Nat :=
  { P with first := [], shared := [⟨pLook, [zOwn, zSpend]⟩]
           second := [⟨pSend, [ySend]⟩, ⟨pTell, [yTell]⟩, ⟨pAsk, [zCarry]⟩] }

/-- The challenges at which the second round of `look` draws p and the first round of `tellB` draws
q. -/
def ρy (p q : Nat) : Draws :=
  ⟨[d0], [dE 5, dP p, dP 3], [d0, dP q, d0, d0]⟩

def runY (x : Nat) (c : Coins By) (ρ' : Draws) : Option Run :=
  (run Fy By Py w₀ 7 x c ρ' none).toOption

/-! ## 2 The simulators and the sides -/

/-- Paired with `ySend`: its one coin, the same at each position that is asked; it reads nothing
else. -/
def yS₂ : Sim Nat :=
  { addr := sSend, takes := ⟨1, 0⟩
    tell := fun _ _ _ asks c => some [⟨[], (asks.headD []).map fun ps => ps.map fun p =>
      (p, [ofF (c.f ⟨0, by decide⟩)])⟩] }

/-- Paired with `yTell`: no coin. It reads `front`: the columns that are there of the second chain's
first own tree; among them the one at the position that the part's own first challenge draws; it
says that column's first word. `none` where `front` lists no such tree or no such column. -/
def yS₃ : Sim Nat :=
  { addr := sTell, takes := ⟨0, 0⟩
    tell := fun _ front ds _ _ =>
      (front.treeCols 2 0).bind fun cols =>
        (cols.find? fun c => c.1 == posOf (ds.headD d0)).map fun c =>
          [⟨[], []⟩, ⟨[.e (c.2.headD 0, 0, 0)], []⟩] }

def ySide₂ : Side St Nat L L Nat Nat := { block := send₃, row := [(ySend, yS₂)] }
def ySide₃ : Side St Nat L L Nat Nat := { block := tellB, row := [(yTell, yS₃)] }
def ySide₄ : Side St Nat L L Nat Nat := { block := askQ, row := [(zCarry, zS₂)] }

/-- Their `Member`s, written out. -/
def yU₂ : Member L L Nat Nat := ⟨0, send₃.rounds.zip send₃.oracles, ySend, yS₂⟩
def yU₃ : Member L L Nat Nat := ⟨0, tellB.rounds.zip tellB.oracles, yTell, yS₃⟩
def yU₄ : Member L L Nat Nat := ⟨0, askQ.rounds.zip askQ.oracles, zCarry, zS₂⟩

/-! ## 3 The parameters -/

/-- **One round, one table, one position**: an executable test. -/
def onePos : List (List (List Nat)) → Bool
  | [[[_]]] => true
  | _ => false

/-- **`front` lists the second chain's first own tree, and each column that it lists of it is the
one word b p + v at its position p**: an executable test. -/
def onTell (v : Cb.Gl.F) (b : Nat → UInt64) (front : Before) : Bool :=
  match front.treeCols 2 0 with
  | some cols => cols.all fun c => c.2 == [ofF (toF (b c.1) + v)]
  | none => false

/-- Coin number i of the base field among the coins that chain number ch may be given at an address,
from a run's coins; 0 where there is none. -/
def coinAt {Bk : ProverCoinCounts} (k : Coins Bk) (ch : Nat) (a : Addr) (i : Nat) : Cb.Gl.F :=
  ((k.look ch a).2.fAt i).toOption.getD (toF 0)

/-- The chain's own tree number n is available, was sent from the place a, has symbols of one word,
and its word at every position p is f p. -/
def hasTree (E : Env) (n : Nat) (a : Place) (f : Nat → Cb.Gl.F) : Prop :=
  ∃ T : Table, E.tree (.own n) = some (a, T) ∧ T.words = 1 ∧ ∀ p i, T.sym p i = f p

section
variable {Bk : ProverCoinCounts}

/-- Before a place that sends its chain's first tree: the chain has sent no tree. -/
def noTree {W : Type} : Coins Bk → St → Mid W Nat → Env → Prop := fun _ _ _ E => E.sent = 0

/-- After `look`: the shared chain has sent one tree; its word at p is the index's plus t plus 2 u,
from this run's coins. -/
def lookSent : Coins Bk → St → Mid L₀ Nat → Env → Prop := fun k _ m E =>
  E.sent = 1 ∧ hasTree E 0 pLook fun p =>
    toF (m.st.input.w₀.a p) + coinAt k 1 zO 0 + coinAt k 1 zO 1 + coinAt k 1 zO 1

/-- After `send`: the second chain has sent one tree; its word at p is the trace's plus v, from this
run's coins. -/
def sendSent : Coins Bk → St → Mid L Nat → Env → Prop := fun k _ m E =>
  E.sent = 1 ∧ hasTree E 0 pSend fun p => toF (m.st.input.trace.b p) + coinAt k 2 sSend 0

/-- A condition that asks nothing. -/
def anyAt {W : Type} : Coins Bk → St → Mid W Nat → Env → Prop := fun _ _ _ _ => True

end

/-- A condition at a part's entry that asks nothing. -/
def onAny {V W Pb : Type} :
    (u : Member V W Nat Pb) → CsAll u.part.carries → Mid W Nat → Before → Prop :=
  fun _ _ _ _ => True

/-- The condition of `yTell` at its entry: `onTell` at the first coin of the first block that the
part carries, at the trace's table, and at `front`. -/
def onTeller : (u : Member L L Nat Nat) → CsAll u.part.carries → Mid L Nat → Before → Prop :=
  fun u ca m front => onTell (firstCoin u.part.carries ca) m.st.input.trace.b front = true

/-- The bound of a list whose part number 0 sends one table: that table is read at one position. Of
the other parts, which send none, nothing is asked. -/
def budOne : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop :=
  fun j _ asks => j = 0 → onePos asks = true

/-- The bound of a list that sends no table: nothing is asked. -/
def budAny : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop := fun _ _ _ => True

/-! ## 4 The lists of parts with their parameters -/

def yLook : Lettered By St Nat Empty L₀ Nat UInt64 :=
  ⟨pLook, zSide.row, noTree, lookSent, onAny, budOne⟩
def ySendL : Lettered By St Nat L L Nat Nat := ⟨pSend, ySide₂.row, noTree, sendSent, onAny, budOne⟩
def yTellL : Lettered By St Nat L L Nat Nat :=
  ⟨pTell, ySide₃.row, sendSent, sendSent, onTeller, budAny⟩
def yCarryL : Lettered By St Nat L L Nat Nat := ⟨pAsk, ySide₄.row, anyAt, anyAt, onAny, budAny⟩

/-- The five parts' four lists, as one value of `Sides`. -/
def Gy : Sides Fy By Wit₀ UInt64 UInt64 Trace Nat Nat :=
  { first := [], shared := [yLook], second := [ySendL, yTellL, yCarryL] }

/-- The inputs: what all requests share is in range, and the request has a trace: all inputs at
which the example's prover does not return an error because of the input. -/
def RelY : Wit₀ → UInt64 → Nat → Prop := fun w _ x => w.ans ≠ 0 ∧ x ≠ 0

/-! ## 5 The `#guard` lines -/

-- the description's tests on the plan; the book's eleven
#guard Fy.planOk
#guard By.word Fy == none
#guard Fy.placesOk
#guard Fy.lastChainFirstTreeNumber == 1
-- the description accepts at each of the 16 + 8 lists, and at another word of `Rc` and other
-- coins
#guard (List.range 16).all fun p =>
  say Fy By Py w₀ 7 2145 (coinsY 2 3 5 4) (ρy p 6) none == "yes"
#guard (List.range 8).all fun q =>
  say Fy By Py w₀ 7 2145 (coinsY 2 3 5 4) (ρy 12 q) none == "yes"
#guard say Fy By Py w₀ 8 5 (coinsY 1 1 1 1) (ρy 13 7) none == "yes"
-- what the five show: 100 + 2 + 6 · 9 + 3 · 6 + 5 at the position 2 · nothing, then that word · 9 +
-- 4 + 9 + 8
#guard (runY 2145 (coinsY 2 3 5 4) (ρy 12 6)).map (fun r =>
    (r.shownAt zO, r.shownAt zP, r.shownAt sSend, r.shownAt sTell, r.shownAt sAsk)) ==
  some ([⟨[], [[(4, [108])]]⟩], [⟨[.answer (12, 0, 0)], []⟩], [⟨[], [[(2, [11])]]⟩],
    [⟨[], []⟩, ⟨[.e (11, 0, 0)], []⟩], [⟨[.e (30, 0, 0)], []⟩])
-- the sides fit
#guard zSide.fits && ySide₂.fits && ySide₃.fits && ySide₄.fits
#guard (ySide₃.members.map fun u => (u.number, u.rounds.length, u.part.takes, u.sim.takes)) ==
  [(0, 2, ⟨0, 0⟩, ⟨0, 0⟩)]
-- every list is at a place of its chain; the prover whose sides are the lists has `Py`'s outcome
#guard Gy.seated
#guard sameOutcome (outcome Fy By (Gy.prover P₀) w₀ 7 2145 (coinsY 2 3 5 4) (ρy 12 6))
  (outcome Fy By Py w₀ 7 2145 (coinsY 2 3 5 4) (ρy 12 6))
#guard (outcome Fy By Py w₀ 7 2145 (coinsY 2 3 5 4) (ρy 12 6)).isSome
-- which entries `Good.fresh` reads: of the first owner for the spender; of the second owner for
-- `yTell`, which spends nothing
#guard (By.spentBy zO zP).map (·.name) == ["u to the spender"]
#guard (By.knownBy (orderOf Fy) zO zP).map (·.name) == []
#guard (By.spentBy sSend sTell).map (·.name) == []
#guard (By.knownBy (orderOf Fy) sSend sTell).map (·.name) == ["v to the teller"]

/-- What a simulator paired with the part at a is given of a run, with the stored columns that the
run reads. -/
def bfY (r : Run) (a : Addr) : Before :=
  r.beforeAt (storedShown (Py.storedWords w₀ 7) r.storedAsked) a

/-- **The parameters On and `bud`, as tests, at one run's own values**: the run goes through; each
owner's table is read at one position; the condition of `yTell` at its entry holds of the block that
the book gives it, of the state that `midAt` returns, and of the run's own `beforeAt`; and that
`front` holds a column for every read of the rounds of `yTell`. (`onAny` and `budAny` ask nothing.)
`Owed.owed` takes the state from `midAtW` (Honest/MidW.lean), which no line here evaluates; of the
state `onTell` is handed the input's trace alone. -/
def owedTest (x : Nat) (k : Coins By) (ρ' : Draws) : Bool :=
  match runY x k ρ', (midAt Fy By Py w₀ 7 x k ρ' sTell).toOption,
      (carriedAt By k 2 sTell yTell).toOption with
  | some r, some m, some ca =>
    onePos (r.askedAt zO) && onePos (r.askedAt sSend) &&
      onTell (firstCoin yTell.carries ca) m.st.input.trace.b (bfY r sTell) &&
      (bfY r sTell).holds 2 Fy.lastChainFirstTreeNumber tellB.rounds (r.drawnAt sTell)
  | _, _, _ => false

-- at each of the 16 positions that the second round of `look` can draw, and at each of the 8 that
-- the first round of `tellB` can draw: a list that the rounds can draw, outside the silent set: the
-- run goes through and the parameters return true
#guard (List.range 16).all fun p =>
  (ρy p 6).due Fy && silentAt Fy Py w₀ 7 2145 (ρy p 6) == none &&
    owedTest 2145 (coinsY 2 3 5 4) (ρy p 6)
#guard (List.range 8).all fun q =>
  (ρy 12 q).due Fy && silentAt Fy Py w₀ 7 2145 (ρy 12 q) == none &&
    owedTest 2145 (coinsY 2 3 5 4) (ρy 12 q)
-- the positions beyond are none that the rounds can draw
#guard !(ρy 16 6).due Fy && !(ρy 12 8).due Fy
-- at the list that draws 13
#guard (runY 2145 (coinsY 2 3 5 4) (ρy 13 6)).map (·.askedAt zO) == some [[[5]]]
-- two positions, no position, two tables, two rounds
#guard onePos [[[5]]] && !onePos [[[4, 5]]] && !onePos [[[]]] && !onePos [[[4], [4]]] &&
  !onePos [[[4]], [[4]]] && !onePos []
-- the condition of `yTell`: at another coin than the run's; at a front without the tree; at a front
-- whose column holds another word
#guard (runY 2145 (coinsY 2 3 5 4) (ρy 12 6)).map (fun r =>
    (onTell (toF 5) (wAt 2145).trace.b (bfY r sTell),
      onTell (toF 6) (wAt 2145).trace.b (bfY r sTell)))
  == some (true, false)
#guard !onTell (toF 5) (wAt 2145).trace.b none₀
#guard onTell (toF 5) (wAt 2145).trace.b ⟨[(2, ⟨[], [[(2, [11])]]⟩, d0)], []⟩ &&
  !onTell (toF 5) (wAt 2145).trace.b ⟨[(2, ⟨[], [[(2, [12])]]⟩, d0)], []⟩

/-! ### `yTell` and its simulator, at fixed coins -/

/-- What comes before `yTell`, as far as its simulator reads it: the round of `send` with one
column. -/
def frontY (p : Nat) (w : UInt64) : Before := ⟨[(2, ⟨[], [[(p, [w])]]⟩, d0)], []⟩
/-- The state of the run before `yTell`, as far as `yTell` reads it. The field `opened` is
`some []`: what `Before.opened` gives at `none₀`, beside which this state is set in the last lines,
so that that pair meets the premise of `Good.exact` on the field (Honest/Side.lean). It is set
beside `frontY` too: that pair meets the premise on the field (`d0` draws no position) and not the
one on `seen`. It is no run's own value: in a run of `runC` the earlier chains' columns stand there.
-/
def midY : Mid L Nat := ⟨⟨wAt 2145, [], 0⟩, [], [], some []⟩

-- its field is what `none₀` holds for the reads of declared rounds: at no round; and at the `pre`
-- that `Owed.good` lays before `pTell` (`preOf`, Honest/Rule.lean; the two entries of `earlierOf`,
-- Honest/Owed.lean, written out), where it is what `frontY` holds too (`d0` draws no position)
#guard midY.opened == none₀.opened (readsBefore [] none₀)
#guard
  let pre := preOf 2 Fy.lastChainFirstTreeNumber [(0, 0, Fy.roundsDeclaredByBlocks.1), (1, 0, Fy.roundsDeclaredByBlocks.2.1)] Fy.second.blocksInOrder pTell
  midY.opened == none₀.opened (readsBefore pre none₀) &&
    midY.opened == (frontY 2 11).opened (readsBefore pre (frontY 2 11))
-- at the run's own `front` before `yTell` that `pre` does bring reads: the front holds a column for
-- each, and they are not `midY`'s field: `midY` has no run's own value
#guard ((runY 2145 (coinsY 2 3 5 4) (ρy 12 6)).map fun r =>
    let pre := preOf 2 Fy.lastChainFirstTreeNumber [(0, 0, Fy.roundsDeclaredByBlocks.1), (1, 0, Fy.roundsDeclaredByBlocks.2.1)] Fy.second.blocksInOrder pTell
    let o := (bfY r sTell).opened (readsBefore pre (bfY r sTell))
    o.isSome && o != midY.opened) == some true
-- the rounds shown: none in the state, one in `frontY`
#guard midY.seen.length == 0 && (frontY 2 11).seen.length == 1

-- the part, played alone, and its simulator, at `frontY 2 11`: of the run's front the round of
-- `send` alone: the same
#guard ySide₃.shows .own yU₃ (Cs.empty, (), (coin₁ 5, ())) midY [dP 6, d0] [[], []] ==
  some [⟨[], []⟩, ⟨[.e (11, 0, 0)], []⟩]
#guard yU₃.tells .own Cs.empty (wAt 2145) (frontY 2 11) [dP 6, d0] [[], []] ==
  some [⟨[], []⟩, ⟨[.e (11, 0, 0)], []⟩]
-- the same two at a state that has seen that front's rounds: this pair meets `m.seen = front.seen`
-- too (the five others: On: the line with `onTell (toF 5)` at this front; `drawsFit`: within `due`
-- at q = 6; `bud`: `budAny`; `holds`: a line below; the stops: constantly `none`) (`yTell` reads no
-- `Seen`: by reading the left side is the one above)
#guard ySide₃.shows .own yU₃ (Cs.empty, (), (coin₁ 5, ())) { midY with seen := (frontY 2 11).seen }
    [dP 6, d0] [[], []] ==
  yU₃.tells .own Cs.empty (wAt 2145) (frontY 2 11) [dP 6, d0] [[], []]
-- the simulator reads `front`: at another word there it says another word; at a front that lists
-- another position than the one drawn, `none`, and `Before.holds` returns false at that pair
#guard yU₃.tells .own Cs.empty (wAt 2145) (frontY 2 12) [dP 6, d0] [[], []] ==
  some [⟨[], []⟩, ⟨[.e (12, 0, 0)], []⟩]
#guard yU₃.tells .own Cs.empty (wAt 2145) (frontY 3 5) [dP 6, d0] [[], []] == none
#guard (frontY 2 11).holds 2 Fy.lastChainFirstTreeNumber tellB.rounds [dP 6, d0] &&
  !(frontY 3 5).holds 2 Fy.lastChainFirstTreeNumber tellB.rounds [dP 6, d0]
-- the owner shows two words at two coins
#guard ySide₂.shows .own yU₂ (coin₁ 5, (), ()) midY [d0] [[[2]]] !=
  ySide₂.shows .own yU₂ (coin₁ 6, (), ()) midY [d0] [[[2]]]
-- at two positions the owner shows two words (11 and 5, at the coin 5) whose difference no coin
-- changes (by the body of `ySend`: one coin at every position; no line of this file evaluates
-- that), and its simulator one word twice (11, at the coin 11)
#guard ySide₂.shows .own yU₂ (coin₁ 5, (), ()) midY [d0] [[[2, 3]]] ==
  some [⟨[], [[(2, [11]), (3, [5])]]⟩]
#guard yU₂.tells .own (coin₁ 11) (wAt 2145) none₀ [d0] [[[2, 3]]] ==
  some [⟨[], [[(2, [11]), (3, [11])]]⟩]

end ProofFile.Honest.Toy

#print axioms ProofFile.Honest.Toy.ySend
#print axioms ProofFile.Honest.Toy.posOf
#print axioms ProofFile.Honest.Toy.yTell
#print axioms ProofFile.Honest.Toy.pTell
#print axioms ProofFile.Honest.Toy.sTell
#print axioms ProofFile.Honest.Toy.sameWord
#print axioms ProofFile.Honest.Toy.tellB
#print axioms ProofFile.Honest.Toy.askQ
#print axioms ProofFile.Honest.Toy.oneOfTwo
#print axioms ProofFile.Honest.Toy.storeY
#print axioms ProofFile.Honest.Toy.Fy
#print axioms ProofFile.Honest.Toy.By
#print axioms ProofFile.Honest.Toy.coinsY
#print axioms ProofFile.Honest.Toy.Py
#print axioms ProofFile.Honest.Toy.ρy
#print axioms ProofFile.Honest.Toy.runY
#print axioms ProofFile.Honest.Toy.yS₂
#print axioms ProofFile.Honest.Toy.yS₃
#print axioms ProofFile.Honest.Toy.ySide₂
#print axioms ProofFile.Honest.Toy.ySide₃
#print axioms ProofFile.Honest.Toy.ySide₄
#print axioms ProofFile.Honest.Toy.yU₂
#print axioms ProofFile.Honest.Toy.yU₃
#print axioms ProofFile.Honest.Toy.yU₄
#print axioms ProofFile.Honest.Toy.onePos
#print axioms ProofFile.Honest.Toy.onTell
#print axioms ProofFile.Honest.Toy.coinAt
#print axioms ProofFile.Honest.Toy.hasTree
#print axioms ProofFile.Honest.Toy.noTree
#print axioms ProofFile.Honest.Toy.lookSent
#print axioms ProofFile.Honest.Toy.sendSent
#print axioms ProofFile.Honest.Toy.anyAt
#print axioms ProofFile.Honest.Toy.onAny
#print axioms ProofFile.Honest.Toy.onTeller
#print axioms ProofFile.Honest.Toy.budOne
#print axioms ProofFile.Honest.Toy.budAny
#print axioms ProofFile.Honest.Toy.yLook
#print axioms ProofFile.Honest.Toy.ySendL
#print axioms ProofFile.Honest.Toy.yTellL
#print axioms ProofFile.Honest.Toy.yCarryL
#print axioms ProofFile.Honest.Toy.Gy
#print axioms ProofFile.Honest.Toy.RelY
#print axioms ProofFile.Honest.Toy.bfY
#print axioms ProofFile.Honest.Toy.owedTest
#print axioms ProofFile.Honest.Toy.frontY
#print axioms ProofFile.Honest.Toy.midY
