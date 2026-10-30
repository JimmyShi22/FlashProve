-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/DealOk.lean: a test on the plan: the arithmetic by which the law of the
proximity test (the kind K12) deals written trees to the declared openings, held against the
declared labels.

The arithmetic is that of srcFirst and srcFrom (Johnson/Desc/K12/Law/Written.lean): as many openings
as the stage's fold and switch declare belong to the stage's own tree; behind them comes the tree
that the switch has written. Definitions with code alone and no theorem, so that the test can be
compiled and run.
Why. Were a tree dealt to the wrong opening, the law's verifier would be false at every transcript,
the law would stand, and a statement "a view from bytes is the written view" would be false. This
test can fail without a transcript.
The walk. l is the place's declared rounds, laid with its oracle messages, behind "BAT". At a stage
but the last the fold's cut is take (1 + k), the switch's is drop (1 + k) then take 2, and the walk
goes on at drop (k + 3); at the last stage the cut is all that is left. So stagesFrom cuts
(Johnson/Desc/K12/Frame.lean).
The clauses (j: the stage's number):
  j:fold.none: the fold's cut declares no opening and no stored table.
  j:one (j ≥ 1): the switch's cut (at the last stage the base case's) declares just one opening, and
    no stored table.
  j:label: its label, uncut, is that of the tree that switch j - 1 sends: firstTree + free + own +
    (j - 1); own is the trees sent less the switches (1 where the first fold sends its own mask).
  j:src: its declared source is "own", number free + own + (j - 1).
  j:a, j:W: its declared depth and width are that sent tree's (TestNums.sent).
  0:some: the first switch's cut declares an opening (which: labelsOk, against the record,
    Johnson/Desc/K12/Law/FirstCut.lean).
  end: the walk uses the rounds up.
Main names:
  `dealWalk`, `dealOn`, `dealOk`: the walk, the clauses at given laid rounds, the test.
  `dealLines`: the lines that a run prints, with three controls, each due false: every expected
    label + 1; the openings of the second and the third opening round exchanged; (against the
    record) the book's last two opened trees exchanged, which is no control where one tree is
    opened.
Limits: Evaluated is not proved. No soundness is claimed, and nothing is said on hiding.
dealOk was evaluated at the four proximity tests of both stored proofs and at the proximity test of
the product test's stored tiny proof: true at each, every control false [the prints are not in this
library].

-/
import Johnson.Desc.K12.Law.FirstCut

set_option autoImplicit false
namespace H2K.First
open VerifiableInference.Desc VerifiableInference.Desc.K12

def nOpenB (cut : List Fmt.DeclaredRound) : Nat := (cut.map fun r => r.stored.length +
        r.opens.length).sum

def ownN (p : P12) : Nat := p.nums.sent.length - (p.nums.stages.length - 1)

/-- The clauses on the one opening of the stage j ≥ 1. shift: 0; a tooth lays 1. -/
def oneL (p : P12) (shift j : Nat) (cut : List Fmt.DeclaredRound) : Clauses :=
  let n := ownN p + (j - 1)
  match cut.flatMap (·.opens) with
  | [o] =>
    [("one", cut.all (·.stored.isEmpty)),
     ("label", o.1.tree == p.nums.firstTree + p.nums.free + n + shift),
     ("src", decide (o.2 = .own (p.nums.free + n))),
     ("a", (p.nums.sent[n]?).any (·.1 == o.1.a)), ("W", (p.nums.sent[n]?).any (·.2 == o.1.W))]
  | _ => [("one", false)]

def tagJ (j : Nat) (l : Clauses) : Clauses := l.map fun x => (toString j ++ ":" ++ x.1, x.2)

def dealWalk (p : P12) (shift : Nat) : Nat → Fmt.M1.Stage → List Fmt.M1.Stage → Laid → Clauses
  | j, _, [], l =>
    tagJ j (if j == 0 then [("a test of one stage", false)] else oneL p shift j (l.map (·.1))) ++
      [("end", l.length == 2)]
  | j, cur, nxt :: rest, l =>
    let cf := (l.take (1 + cur.k)).map (·.1)
    let cs := ((l.drop (1 + cur.k)).take 2).map (·.1)
    tagJ j ([("fold.none", nOpenB cf == 0)] ++
      (if j == 0 then [("some", !(cs.flatMap (·.opens)).isEmpty && cs.all (·.stored.isEmpty))]
       else oneL p shift j cs)) ++ dealWalk p shift (j + 1) nxt rest (l.drop (cur.k + 3))

def laidB (p : P12) : Laid := (((H2U.roundsOfNums p.nums).getD []).zip p.oracles).drop 1

def dealOn (p : P12) (shift : Nat) (l : Laid) : Clauses :=
  match p.nums.stages with
  | a :: rest => dealWalk p shift 0 a rest l
  | [] => [("no stage", false)]

/-- The test: every clause says yes at the place's own laid rounds. -/
def dealOk (p : P12) : Bool := ok (dealOn p 0 (laidB p))

def noOf (l : Clauses) : List String := (l.filter (!·.2)).map (·.1)

/-- The openings of the second and the third round that open a tree, exchanged. -/
def swapped (l : Laid) : Laid :=
  let idx := (l.zipIdx.filter fun x => !x.1.1.opens.isEmpty).map (·.2)
  match idx with
  | _ :: i :: k :: _ =>
    let oi := ((l[i]?).map (·.1.opens)).getD []
    let ok' := ((l[k]?).map (·.1.opens)).getD []
    l.zipIdx.map fun x =>
      if x.2 == i then ({ x.1.1 with opens := ok' }, x.1.2)
      else if x.2 == k then ({ x.1.1 with opens := oi }, x.1.2) else x.1
  | _ => l

def swapLast {α : Type} (l : List α) : List α :=
  match l.reverse with
  | a :: b :: r => (b :: a :: r).reverse
  | _ => l

/-- The lines for a sheet. tG: the record behind the batching (for the third tooth alone). -/
def dealLines (tagS : String) (p : P12) (tG : T12) : List String :=
  let l := laidB p
  let third : String := match p.nums.stages, tG.pass with
    | a :: _, .claim _ L =>
      match gpOf p tG a L with
      | some D =>
        if D.ts.length < 2 then "no tooth: one tree is opened"
        else s!"{D.opens.map (·.1.tree) == (swapLast D.ts).map (numAt D.book)}"
      | none => "no plain data"
    | _, _ => "no stage, or no claim"
  [s!"{tagS}.DEAL\tdealOk {dealOk p}\tclauses {(dealOn p 0 l).length}\trefusing: {noOf (dealOn p 0
      l)}\town {ownN p} · free {p.nums.free} · firstTree {p.nums.firstTree} · the opening rounds' \
      labels, in turn: {(l.filter fun x => !x.1.opens.isEmpty).map fun x =>
      x.1.opens.map (·.1.tree)} · sent (a, W): {p.nums.sent}",
   s!"{tagS}.DEAL.control\tevery expected label + 1\t{ok (dealOn p 1 l)}\trefusing {(noOf (dealOn p
       1 l)).length}: {(noOf (dealOn p 1 l)).take 3}",
   s!"{tagS}.DEAL.control\tthe second and the third opening round's openings exchanged\t{ok (dealOn
       p 0 (swapped l))}\trefusing {(noOf (dealOn p 0 (swapped l))).length}: {(noOf (dealOn p 0
       (swapped l))).take 3}",
   s!"{tagS}.DEAL.control\tthe book's last two opened trees exchanged (stage 0, against the \
       record)\t{third}"]

end H2K.First
