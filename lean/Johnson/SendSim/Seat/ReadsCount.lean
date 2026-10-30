-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/ReadsCount.lean: two statements on the executable test readsWithinB. At every
due list of challenges, the positions that a description's rounds query of a tree are at most as
many as the test counts; and where the test accepts, the bound ReadsWithin holds.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms"; for drawnFor, readsWithinB and n₀,
ReadsTest.lean; for ReadsWithin and BudClause, Bud.lean. Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. Two named propositions, for every description F. Both are statements only;
proved as readsCount and readsWithinOf in ReadsCountProof.lean. The words in short:
  drawnFor F n        the number of positions that the declared rounds of F's three chains sample
                      for the first chain's tree number n, counted off the description, without
                      challenges.
  n₀                  the number of trees that the first chain sends before the sender, so that the
                      sender's tree τ is the chain's tree number n₀ + τ.
  readsWithinB F P n₀ the test: for each oracle message of P in a tree τ, drawnFor F (n₀ + τ) is at
                      most the number of entries of the main code's tail, if it has main rows, and
                      of the mask code's tail, if it has mask rows.
  ReadsWithin F P n₀  the bound itself, at every due list of challenges: the positions that are
                      queried of tree number n₀ + τ give at most that many distinct positions modulo
                      the code's length. It implies budAt, the bound that is a premise inside exact
                      and fresh, at the positions that are queried of the first chain's trees from
                      number n₀ on, at every due list (budAt_of_reads, BudProof.lean).
The two statements:
  Spec.readsCount     For every due list of challenges (Draws.due: the description's rounds can
                      sample it, and the first chain's last challenge is empty) and every n: the
                      list of positions that are queried of the first chain's tree number n
                      (treeAsks) has at most drawnFor F n entries.
  Spec.readsWithinOf  For all parameters P and every number n₀: if readsWithinB F P n₀ accepts, then
                      ReadsWithin F P n₀ holds.

Limits.
The test requires more than the bound: if it rejects, nothing follows. It also accepts at an oracle
message that is in no tree; ReadsWithin requires nothing of such an oracle message either (see
ReadsTest.lean, Limits).
The test is evaluated at no description in this file. It covers only the first chain's trees.
The statements are on lists and numbers of the description's declared rounds: no input, no coin and
no execution. No list of challenges is in the test. No distribution is named.

How it fits. treeAsks is in Johnson/Desc/ProofFile/Honest/Law/Rule/Bare.lean. With BudProof.lean the
second statement gives BudClause, the clause on queried positions that the framework's rule
(file_owed_rows) requires of the sender's row, if the test accepts at treesTo F pre for every way to
split the first chain's list at the place (budClause_of_test, ReadsCountProof.lean).
-/
import Johnson.SendSim.Seat.Bud
import Johnson.SendSim.Seat.ReadsTest

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc OnBytes.SendSim.At
open Johnson.Prover.Send (shapeAt)

variable {Xi : Type}

/-- States that, at every due list of challenges, the positions queried of the first chain's tree
number n are at most drawnFor F n. Statement only; proved as readsCount in
Johnson/SendSim/Seat/ReadsCountProof.lean. -/
def Spec.readsCount : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (ρ : Draws) (n : Nat), ρ.due F = true →
    (treeAsks F ρ 0 n).length ≤ drawnFor F n

/-- States that ReadsWithin F P n₀ holds if the test readsWithinB F P n₀ accepts. Statement only;
proved as readsWithinOf in Johnson/SendSim/Seat/ReadsCountProof.lean. -/
def Spec.readsWithinOf : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (P : K1.Par) (n₀ : Nat), readsWithinB F P n₀ = true →
    ReadsWithin F P n₀

end OnBytes.SendSim.Seat
