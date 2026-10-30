-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/ReadsTestAt.lean: the public test on queried positions of ReadsTest.lean, with
the number of the chain that sends the trees as a parameter.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. Definitions with code, and three equations by definition.
  opensInAt ch c n ds   how many positions the rounds ds of the chain number c sample for the tree
                        number n that the chain number ch sends.
  drawnForAt F ch n     the like over the description's three chains.
  readsWithinAtB F ch P n₀   the test. For each message of the sending with the public numbers P,
                        whose first tree has the number n₀ in the chain number ch: the positions
                        sampled for its tree are at most as many as the random symbols that its
                        code appends to a row (the field r), for the main rows' code and for the
                        mask rows' code.
  opensInAt_zero, drawnForAt_zero, readsWithinAtB_zero   at ch = 0 the three are opensIn, drawnFor
                        and readsWithinB of ReadsTest.lean.

How it fits. ReadsTest.lean has the first chain's number 0 written in. A sending of the kind K1 on
another chain needs the same test at that chain's number. ReadsCountAt.lean beside this file proves
that the test implies the bound on queried positions (budAt). This file imports ReadsTest.lean
alone, which holds definitions and no proof, so that a test program can load it without the proofs.

Limits. All limits of ReadsTest.lean but the one on the first chain; among them: the test accepts at
a message that lies in no tree, and wherever the trees cannot be laid (Own.treesMade returns
nothing). It has been run at no public files.
-/
import Johnson.SendSim.Seat.ReadsTest

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc OnBytes.SendSim.At
open Johnson.Prover.Send (shapeAt)

variable {Xi : Type}

/-- The positions that the rounds of the chain number c sample for the tree number n of the chain
number ch. -/
def opensInAt (ch c n : Nat) (ds : List Fmt.DeclaredRound) : Nat :=
  (ds.map fun d => (d.opens.filter fun o => srcOf c o.2 == (ch, n)).length * d.entry.poss).sum

/-- The like over the three chains. -/
def drawnForAt (F : FileDescription Xi) (ch n : Nat) : Nat :=
  opensInAt ch 0 n F.roundsDeclaredByBlocks.1 + opensInAt ch 1 n F.roundsDeclaredByBlocks.2.1 + opensInAt ch 2 n F.roundsDeclaredByBlocks.2.2

/-- The test on queried positions, at a sending of the chain number ch. -/
def readsWithinAtB (F : FileDescription Xi) (ch : Nat) (P : K1.Par) (n₀ : Nat) : Bool :=
  (List.range P.sent.size).all fun k =>
    match ((Own.treesMade P.codes P.sent).getD {}).tree[k]? with
    | none => true
    | some τ =>
      ((shapeAt P k).mainRows == 0 ||
          decide (drawnForAt F ch (n₀ + τ) ≤ (P.codes.base.getD (shapeAt P k).code default).r)) &&
        ((shapeAt P k).maskRows == 0 ||
          decide (drawnForAt F ch (n₀ + τ) ≤
            (P.codes.mask.getD (shapeAt P k).maskCode default).r))

theorem opensInAt_zero (c n : Nat) (ds : List Fmt.DeclaredRound) :
    opensInAt 0 c n ds = opensIn c n ds := rfl

theorem drawnForAt_zero (F : FileDescription Xi) (n : Nat) : drawnForAt F 0 n = drawnFor F n := rfl

theorem readsWithinAtB_zero (F : FileDescription Xi) (P : K1.Par) (n₀ : Nat) :
    readsWithinAtB F 0 P n₀ = readsWithinB F P n₀ := rfl

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.readsWithinAtB_zero
