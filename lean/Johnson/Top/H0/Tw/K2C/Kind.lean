-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H0/Tw/K2C/Kind.lean: the kind «the code switch» as a Kind of Johnson/Desc/Block.lean at
the first chain's carried record S (Johnson/Desc/First/State.lean).
definitions with code; no theorem. Nothing on soundness, on an honest prover or on hiding.
decide returns Except String: EACH REFUSAL UNDER ITS
GUARD's OWN NAME (the names of K2/'s lists) · oracles: each sent tree with its tenants · before: the
trees that round 2 reads.

ROUNDS (two). 1 «SEND seed»: the prover sends `roots` roots: beneath them g, a fresh copy of each
kept matrix, and what the next link sends with its first message; the verifier draws `seeds`
elements, of which the `nonZero` factors
  must not be 0. 2 «LOC»: the prover sends `answers` answers and nothing else; the verifier draws
  `positions` positions below 2 ^ logN, and no element.
READS. In round 2: the chain's own trees that hold the OLD rows (`read`: the tree's number in the
chain, its depth, its width), each at the drawn positions cut down to its depth, each position once.
Nothing of a new message.
FIXED BEFORE THE DRAW. The trees that are read: they were sent, and where sampled answered, in front
of this block. `before` names every tree that the block opens. (The new trees are sent in round 1's
message, in front of its draw; their samples are answered in round 2, in front of the positions:
  Block.lean's `before` speaks of a block's FIRST draw alone, so they cannot be named there.)
DECIDES. [G34] EACH POSITION THAT ROUND 2 DREW LIES BELOW 2 ^ logN (the program's Positions.ofDraws
says of itself «not tested here» (Iop/Ground.lean:504-508): its channel draws below the range by its
make; A VIEW IS DATA: at x₀ + 2 ^ logN the
  columns are those at x₀ and the code is evaluated at another point). THEN THE BODY: K2/'s TEXT
  (Switch · First · Step · Cuts), CALLED BY NAME, IN ITS FORMS WITH WORDS: chainFirstEW |
  headSwitchEW | finishSwitchEW at switchBehind.
  WHAT IS NOT AS IT SHOULD BE, SAID OUTRIGHT: (a) the groups of columns are laid flat again
  under their keys and the body takes and matches them a second time (behind Block.step that second
  matching [G12] refuses only where a drawn position lies beyond the range and a tree as long as the
  range is read) · (b) the book of trees and the count of
  roots are written here, because later places read them out of S; THE TESTS OF THE READING
  (G8 … G14) STAY HERE: BookPlan.allClausesHold's clauses «range» · «alike» | «oneGroup» · «once» read like G11
  · G9 · G10: BY READING; NO THEOREM OF THIS LIBRARY SAYS SO
  · (c) the program's pure functions by name: switchTargetCheck · switchRows ·
  singleRowsOracles | singleRowsSymbols · Positions.ofDraws · Blk.ownList | columnsFit | symbolsOf ·
  listOfT · foldMaskNotice · ReqFrame.atMoment | notices | foldShape.
THE DEBT OF ROWS. [S4] asks State.lean's own S.noneWaits (nothing is owed, or the round closed last
counts no rows), never the pattern none; behind the block nothing is owed (both entries count no
rows).
CLAIMS. None as named runs: the new rows are laid into the statement's group inside decide, as
the program lays them.
TESTS ON THE PLAN ALONE. planOk: [N1] at least one position; [N2] as many sent trees as roots; [N3]
the trees that are read stand in increasing order; [N4] logN ≤ 32 (above it the program's point and
the format's part inside the range).
THE TENANTS' GROUPS ARE TOLD: every sampled tenant of a tree that the switch sends belongs to just
one group, the one that the switch opens: `grp`; the fresh mask, which has no sample, to none. [G35]
TIES THAT WORD
OF THE PLAN TO THE RUN: the number of the group that was in fact opened (the plain ground's
newGroupP hands it out) is `grp`. [G9] STAYS IN decide ALL THE SAME, at the run's own groups.
SENDS. Written in Lean only for the switches of the link proof's proximity test (lean/GAPS.md).
-/
import Johnson.Desc.Block
import Johnson.Desc.First.State
import Johnson.Top.H0.Tw.K2.Cuts
import Johnson.Top.H0.Tw.K2.SendL8

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Kind Place Oracle)

/-- Where the switch stands. -/
inductive At where
  | link | head | finish
  deriving DecidableEq, Repr, Inhabited

/-- **The numbers of a place.** No entry and no declared round: these are made of the numbers
(`rounds`). -/
structure P2 where
  name : String
  place : Place
  stands : At
  /-- the number of the group that the switch opens: the link's number; at the finish the number of
  links -/
  grp : Nat
  /-- the number in the label of the chain's first own tree -/
  firstTree : Nat
  /-- the answers to each out-of-domain sample -/
  samples : Nat
  /-- round 1: bits of work · roots · elements drawn · how many of these must not be 0 -/
  work₁ : Nat
  roots : Nat
  seeds : Nat
  nonZero : Nat
  /-- round 2: bits of work · answers · positions · their range -/
  work₂ : Nat
  answers : Nat
  positions : Nat
  logN : Nat
  /-- for each root of round 1: the oracle message beneath it -/
  sent : List Oracle
  /-- the own trees that round 2 opens: number in the chain, depth, width -/
  read : List (Nat × Nat × Nat)

/-- ROUNDS and READS. -/
def rounds (p : P2) : List Fmt.DeclaredRound :=
  [ { entry := { name := "SEND seed", work := p.work₁, msg := 32 * p.roots, roots := p.roots,
                 drawE := p.seeds, drawNZ := p.nonZero } },
    { entry := { name := "LOC", work := p.work₂, msg := 24 * p.answers, answers := p.answers,
                 poss := p.positions, logN := p.logN }
      opens := p.read.map fun r => (⟨r.2.1, r.2.2, false, p.firstTree + r.1⟩, .own r.1) } ]

/-- The plan's numbers as `Tw.K2.Par9` takes them. -/
def par9 (p : P2) : _root_.Tw.K2.Par9 :=
  match rounds p with
  | [a, b] => ⟨p.firstTree, p.samples, a.entry, b.entry⟩
  | _ => ⟨p.firstTree, p.samples, default, default⟩  -- dead: «rounds» always has two entries

/-- The groups laid flat again, each column under its tree's key (the head's point (a)). -/
def flat (p : P2) (gs : List (List (Nat × List UInt64))) : List _root_.Tw.K2.Col :=
  (p.read.zip gs).flatMap fun x => x.2.map fun c => (x.1.1, c.1, c.2)

/-- True if the list increases strictly. -/
def increasing : List Nat → Bool
  | a :: b :: l => Decidable.decide (a < b) && increasing (b :: l)
  | _ => true

/-- Every column that was handed over is taken, and there is a group for each tree. -/
def allTaken (p : P2) (gs : List (List (Nat × List UInt64))) (left : List _root_.Tw.K2.Col) : Except
    String Unit :=
  if left.isEmpty && gs.length == p.read.length then .ok () else
      .error "B1: not every column that the block was handed is taken"

/-- [G34] Each position that round 2 drew lies below the range. -/
def inRange (p : P2) (rs : List Fmt.RoundView) : Bool :=
  (rs.drop 1).all fun r => r.drawn.poss.all fun x => Decidable.decide (x < 2 ^ p.logN)

/-- [G35] The group that was opened for this switch is the one that the plan tells (the tenants'
«groups» in `sent` name it). -/
def rightGroup (p : P2) (g : Nat) : Except String Unit :=
  if g == p.grp then .ok () else
      .error "G35: the new group's number is not the one that the plan tells"

/-- DECIDES. snd: the sending (sendByL8; a parameter so that a control can lay a lying one). -/
def decideWith (snd : _root_.Tw.K2.SendFn) (p : P2) (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat
           × List UInt64))) : Except String S :=
  let cols := flat p gs
  if !inRange p rs then .error "G34: a drawn position lies beyond the range" else
  match p.stands, s.here with
  | .link, .between => do
    let x ← _root_.Tw.K2.chainFirstEW _root_.Tw.K2.switchBehind (par9 p) snd ⟨s.st, s.book, s.roots,
        s.check, s.noneWaits⟩ rs cols
    allTaken p gs x.2
    rightGroup p x.1.check.frame.group
    pure { s with st := x.1.st, book := x.1.book, roots := x.1.roots, check := x.1.check,
                  rowsOwed := none }
  | .head, .head a => do
    rightGroup p a.fr.group
    let x ← _root_.Tw.K2.headSwitchEW _root_.Tw.K2.switchBehind (par9 p) snd ⟨s.st, s.book, s.roots,
        s.noneWaits⟩ s.check.frame a.fr rs cols
    allTaken p gs x.2.2
    pure { s with st := x.2.1.st, book := x.2.1.book, roots := x.2.1.roots, rowsOwed := none,
                  here := .head { a with kept := x.1.kept, ids := x.1.others } }
  | .finish, .fin a => do
    rightGroup p a.fr.group
    let G ← (a.G.elim (.error "B4: the last group's record is not laid") .ok : Except String _)
    let x ← _root_.Tw.K2.finishSwitchEW _root_.Tw.K2.switchBehind (par9 p) snd ⟨s.st, s.book,
        s.roots, s.noneWaits⟩ a.fr G.target rs cols
    allTaken p gs x.2.2
    pure { s with st := x.2.1.st, book := x.2.1.book, roots := x.2.1.roots, rowsOwed := none,
                  here := .fin { a with sw := x.1 } }
  | _, _ => .error "B2: the record stands at another sort of place than the block"

/-- **THE KIND.** -/
def codeSwitchKind {Cl : Type} : Kind P2 S Cl := fun p =>
  { name := p.name, place := p.place
    planOk :=
        Decidable.decide (0 < p.positions) && p.sent.length == p.roots && increasing (p.read.map
            (·.1)) && Decidable.decide (p.logN ≤ 32)
    rounds := rounds p
    oracles := [p.sent, []]
    before := p.read.map fun r => (p.place.chain, r.1)
    decide := decideWith _root_.Tw.K2.sendByL8 p
    claims := []
    after := [] }

end VerifiableInference.Desc.First.K2
