-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/TieOk.lean: a test on the plan: the written round "SEND seed" of each switch of
the proximity test (the kind K12) sends just the tree that the next stage's one opening declares.

Johnson/Desc/K12/Law/DealOk.lean holds the law's arithmetic of dealing against the declared labels.
The law's chain goes over written rounds (writtenOf, Johnson/Desc/K12/Law/PubOk.lean: each declared
round that sends a root gets the next of the place's shapes). This test ties the two. Definitions
with code alone and no theorem, so that the test can be compiled and run.
The walk. The declared rounds behind "BAT" (l) and the written rounds behind "BAT" (w) go side by
side, as stagesFrom (Johnson/Desc/K12/Frame.lean) and chainFrom (Johnson/Desc/K12/Law/ChainOf.lean)
cut them: at a stage but the last the round "SEND seed" is w[1 + kk]; the walk goes on at l.drop (k
+ 3) and w.drop (kk + 3), with kk := h + (k - h).
The clauses:
  bat.none: "BAT" declares no opening and no stored table.
  len: there are as many written rounds as declared rounds.
  j:tie: the tree of stage j's "SEND seed", as written, is the shape (depth, width, not stored,
    label) that stage j + 1's one opening declares.
Main names:
  `cutN`, `tieWalk`, `tieOn`, `writtenB`, `tieOk`: the next stage's cut, the walk, the clauses, the
    written rounds behind "BAT", the test.
  `tieLines`: the lines that a run prints, with two controls, each due false: the written trees'
    labels + 1; the written trees handed out in the reverse order.
Limits: Evaluated is not proved. No soundness is claimed, and nothing is said on hiding.
It has no clause for the tree that the first fold's own first round writes where that fold sends its
own mask: Johnson/Desc/K12/Law/OwnTie.lean.
tieOk was evaluated at the four proximity tests of both stored proofs and at the proximity test of
the product test's stored tiny proof: true at each, every control false [the prints are not in this
library].

-/
import Johnson.Desc.K12.Law.PubOk
import Johnson.Desc.K12.Law.DealOk

set_option autoImplicit false
namespace H2K.First
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (WR writtenOf)

/-- What the stage nxt (with rest behind it) opens, of the rounds l that are left to it: the
switch's cut; at the last stage all. -/
def cutN (nxt : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid) : List Fmt.DeclaredRound :=
  if rest.isEmpty then l.map (·.1) else ((l.drop (1 + nxt.k)).take 2).map (·.1)

def tieWalk : Nat → Fmt.M1.Stage → List Fmt.M1.Stage → Laid → List WR → Clauses
  | _, _, [], _, _ => []
  | j, cur, nxt :: rest, l, w =>
    (toString j ++ ":tie",
      match w[1 + H2K.Pub.kk cur]?, (cutN nxt rest (l.drop (cur.k + 3))).flatMap (·.opens) with
      | some dS, [o] => decide (dS.tree = some o.1)
      | _, _ => false) ::
    tieWalk (j + 1) nxt rest (l.drop (cur.k + 3)) (w.drop (H2K.Pub.kk cur + 3))

def tieOn (p : P12) (w : List WR) : Clauses :=
  match p.nums.stages with
  | a :: rest =>
    [("bat.none", nOpenB (((((H2U.roundsOfNums p.nums).getD []).zip p.oracles).take 1).map (·.1)) ==
        0),
     ("len", w.length == (laidB p).length)] ++ tieWalk 0 a rest (laidB p) w
  | [] => [("no stage", false)]

def writtenB (p : P12) : List WR := ((writtenOf p.nums).getD []).drop 1

/-- The test: the written rounds are there, and every clause says yes. -/
def tieOk (p : P12) : Bool := (writtenOf p.nums).isSome && ok (tieOn p (writtenB p))

def relabel (w : List WR) : List WR :=
  w.map fun d => { d with tree := d.tree.map fun s => { s with tree := s.tree + 1 } }

def reversedTrees (w : List WR) : List WR :=
  let ts := (w.filterMap (·.tree)).reverse
  (w.foldl (fun (acc : List WR × List Fmt.Shape) d =>
    match d.tree, acc.2 with
    | some _, s :: r => ({ d with tree := some s } :: acc.1, r)
    | _, _ => (d :: acc.1, acc.2)) ([], ts)).1.reverse

def tieLines (tagS : String) (p : P12) : List String :=
  let w := writtenB p
  [s!"{tagS}.TIE\ttieOk {tieOk p}\tclauses {(tieOn p w).length}\trefusing: {noOf (tieOn p w)}\tthe \
      written trees behind BAT, in turn (a, W, label): {(w.filterMap (·.tree)).map fun s => (s.a,
      s.W, s.tree)}",
   s!"{tagS}.TIE.control\tthe written trees' labels + 1\t{ok (tieOn p (relabel w))}\trefusing {(noOf
       (tieOn p (relabel w))).length}: {(noOf (tieOn p (relabel w))).take 3}",
   s!"{tagS}.TIE.control\tthe written trees handed out in the reverse order\t{ok (tieOn p
       (reversedTrees w))}\trefusing {(noOf (tieOn p (reversedTrees w))).length}: {(noOf (tieOn p
       (reversedTrees w))).take 3}"]

end H2K.First
