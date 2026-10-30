-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/ReadsTab.lean: the public test on queried positions of ReadsTest.lean, computed
from two short tables instead of a description's whole lists of rounds. Definitions only.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has.
  opensTab c ds        of the declared rounds ds of the chain number c: one pair for each opening of
                       a tree in a round: the opening's source (the chain that sent the tree, and
                       the tree's number there), and how many positions the round samples.
  readsTab D           the like over three chains' lists of declared rounds.
  drawnTab T n         the sum of the positions over the pairs of T whose source is the first
                       chain's tree number n.
  treesAt C p          of the rows that cutOf makes of a list of sub-protocols
                       (Johnson/Desc/Ok/PlanWritten/CutTest.lean): how many trees the rows in front
                       of the first row at the place p tell.
  readsWithinT T P n₀  the definition of readsWithinB (ReadsTest.lean) with drawnTab T in the place
                       of drawnFor F.

How it fits. At the full size a proof file's description declares many rounds, and its rounds open
trees 100 times (tabW_length, ReadsAtWritten.lean). ReadsTabLaws.lean beside this file proves that
the test on the two tables is the test of ReadsTest.lean. ReadsAtWritten.lean evaluates it at the
library's written full-size values. Statements on public data: no distribution is named. Meant as
steps toward index privacy (Johnson/WholeKey/Statement.lean); nothing in this folder derives index
privacy from them. Not one of the release's goal statements.

Limits. All limits of ReadsTest.lean; among them: the test accepts at a message that lies in no
tree, and wherever the trees cannot be laid. treesAt counts all rows where no row is at the place p.
-/
import Johnson.SendSim.Seat.ReadsTest
import Johnson.Desc.Ok.PlanWritten.CutTest

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc OnBytes.SendSim.At
open Johnson.Prover.Send (shapeAt)

/-- One chain's openings: each with its source and the positions that its round samples. -/
def opensTab (c : Nat) (ds : List Fmt.DeclaredRound) : List ((Nat × Nat) × Nat) :=
  ds.flatMap fun d => d.opens.map fun o => (srcOf c o.2, d.entry.poss)

/-- The three chains' openings. -/
def readsTab (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound) :
    List ((Nat × Nat) × Nat) :=
  opensTab 0 D.1 ++ opensTab 1 D.2.1 ++ opensTab 2 D.2.2

/-- The positions that are sampled for the first chain's tree number n. -/
def drawnTab (T : List ((Nat × Nat) × Nat)) (n : Nat) : Nat :=
  ((T.filter fun x => x.1 == (0, n)).map (·.2)).sum

/-- How many trees the rows in front of the first row at the place p tell. -/
def treesAt
    (C : List (String × Place × Nat × Nat × List (Nat × List VerifiableInference.Desc.Oracle) ×
      List (Nat × Nat))) (p : Place) : Nat :=
  ((C.takeWhile fun r => r.2.1 != p).map fun r => (r.2.2.2.2.1.map (·.2.length)).sum).sum

/-- The test on queried positions, on a table of openings. -/
def readsWithinT (T : List ((Nat × Nat) × Nat)) (P : K1.Par) (n₀ : Nat) : Bool :=
  (List.range P.sent.size).all fun k =>
    match ((Own.treesMade P.codes P.sent).getD {}).tree[k]? with
    | none => true
    | some τ =>
      ((shapeAt P k).mainRows == 0 ||
          decide (drawnTab T (n₀ + τ) ≤ (P.codes.base.getD (shapeAt P k).code default).r)) &&
        ((shapeAt P k).maskRows == 0 ||
          decide (drawnTab T (n₀ + τ) ≤ (P.codes.mask.getD (shapeAt P k).maskCode default).r))

end OnBytes.SendSim.Seat
