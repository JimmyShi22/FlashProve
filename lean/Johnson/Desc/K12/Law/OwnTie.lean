-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/OwnTie.lean: a test on the plan: the one written tree of the proximity test
(the kind K12) that is opened at stage 0, the first fold's own mask's.

tieWalk (Johnson/Desc/K12/Law/TieOk.lean) ties each "SEND seed" to the next stage's one opening. The
tree that "FOLD epsilon" itself writes, where the first fold sends its own mask, is opened by the
first switch; this test ties it. Definitions with code alone and no theorem, so that the test can be
compiled and run.
The clauses. Where the place's fold sends its own mask: 0:own: the tree of the first written round
behind "BAT", as written, is the shape that the first switch's last opening declares; 0:own.src:
that opening's declared source is "own", number free. Elsewhere: 0:none: that round writes no tree.
Main names:
  `ownTieOn`, `ownTieOk`: the clauses, the test.
  `ownTieLines`: the lines that a run prints, with one control, due false: the first written round's
    tree struck where there is one, laid where there is none.
Limits: Evaluated is not proved. No soundness is claimed, and nothing is said on hiding.
ownTieOk was evaluated at the four proximity tests of both stored proofs and at the proximity test
of the product test's stored tiny proof: true at each, the control false [the prints are not in this
library].

-/
import Johnson.Desc.K12.Law.TieOk

set_option autoImplicit false
namespace H2K.First
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (WR writtenOf)

def ownTieOn (p : P12) (w : List WR) : Clauses :=
  match p.nums.stages with
  | a :: _ =>
    if p.nums.ownMask then
      match w[0]?, (opensOf p a.k).getLast? with
      | some dE, some o =>
        [("0:own", decide (dE.tree = some o.1)), ("0:own.src", decide (o.2 = .own p.nums.free))]
      | _, _ => [("0:own", false)]
    else [("0:none", (w[0]?).any (·.tree.isNone))]
  | [] => [("no stage", false)]

/-- The test: every clause says yes. -/
def ownTieOk (p : P12) : Bool := ok (ownTieOn p (writtenB p))

def flipFirst (w : List WR) : List WR :=
  match w with
  | d :: r => { d with tree := if d.tree.isSome then none else some ⟨0, 0, false, 0⟩ } :: r
  | [] => []

def ownTieLines (tagS : String) (p : P12) : List String :=
  let w := writtenB p
  [s!"{tagS}.OWN\townTieOk {ownTieOk p}\tclauses {(ownTieOn p w).map (·.1)}\trefusing: {noOf
      (ownTieOn p w)}\townMask {p.nums.ownMask} · the first written round's tree (a, W, label): \
      {((w[0]?).bind (·.tree)).map fun s => (s.a, s.W, s.tree)}",
   s!"{tagS}.OWN.control\tthe first written round's tree struck, or laid\t{ok (ownTieOn p (flipFirst
       w))}\trefusing: {noOf (ownTieOn p (flipFirst w))}"]

end H2K.First
