-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/Bud.lean: the clause on queried positions that the framework's rule requires of
the sender's row (BudClause; sendRow, "our row"), and a bound on the positions that a description's
own rounds query (ReadsWithin) which implies it. Definitions only.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. Two named propositions on a description F. A list of challenges ρ is due
(Draws.due) if the description's rounds can sample it and the first chain's last challenge is empty.
  BudClause     At a place a and a job J. For all predicates A and B, every side that our row
                (sendRow a J) has in the first chain's list, every member of it, every way to split
                the list at the side's sub-protocol, and every due list of challenges: the positions
                that the declared rounds query of the sender's trees are within the bound (budAt).
                This is the first chain's clause bud₁ of the rule's premise BudDebts, at our row.
  ReadsWithin   At parameters P and a number n₀, the number of trees that the first chain sends
                before the sender. For every due list of challenges, every oracle message k of P and
                its tree τ: the positions that are queried, in any round of the three chains, of the
                first chain's tree number n₀ + τ give at most r distinct positions modulo the length
                of the main code, if k has main rows, where r is the number of entries of that
                code's tail; and the same for the mask code, if k has mask rows.

Limits.
Nothing is proved in this file. That ReadsWithin implies BudClause is proved in BudProof.lean. That
an executable test on the description implies ReadsWithin is proved in ReadsCountProof.lean. Where
each premise is proved for the release's files: the table of premises in Johnson/SendSim/Defs.lean.
BudClause covers only the first chain: the analogue of the clauses bud₂ and bud₃ of BudDebts, for
the two other chains, is not stated for our row. Places of the kind K1 on other chains exist
(AtDescLots.lean, Limits), and BudClause does not cover them. ReadsCountAt.lean has the bound on
queried positions for any of the three chains.
Both propositions speak of the description, of how the list is split and of the challenges: no
input, no coin and no execution. No distribution is named. Where no list of challenges is due both
hold vacuously; a written list is due at the maker's description where the gate accepts
(due_of_live, DueAtLive.lean).

How it fits. BudDebts is in Johnson/Desc/ProofFile/Honest/Law/OwedRule.lean, sendRow in Row.lean,
budAt in Johnson/SendSim/At/Sim.lean. budAt is a premise inside exact and fresh. budAtLots
(AtDescLots.lean) derives BudClause from the test readsWithinB, for any list of jobs;
LotsTestTie.lean uses that at the jobs of the two lots.
-/
import Johnson.Desc.ProofFile.Honest.Law.OwedRule
import Johnson.SendSim.Seat.Row

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc OnBytes.SendSim.At
open Johnson.Prover.Send (shapeAt)

variable {Xi V W X Pb : Type}

/-- The clause on queried positions for our row at the place a and the job J: at every side of the
row in the first chain's list, every member, every way to split the list at the side's sub-protocol
and every due list of challenges, the positions that the declared rounds query of the sender's trees
are within the bound budAt. A definition; derived from ReadsWithin in
Johnson/SendSim/Seat/BudProof.lean. -/
def BudClause (F : FileDescription Xi) (a : Place) (J : SendJob W X) : Prop :=
  ∀ (Bk : ProverCoinCounts) (A B : Coins Bk → F.S₁ → Mid W X → Env → Prop) (σ : Side F.S₁ F.Cl V W X Pb),
    (⟨a, (sendRow a J).row, A, B, (sendRow a J).On, (sendRow (V := V) (Pb := Pb) a J).bud⟩ :
      Lettered Bk F.S₁ F.Cl V W X Pb).side F.first.blocksInOrder = some σ →
    ∀ u ∈ σ.members, ∀ pre t n, F.first.blocksInOrder = pre ++ σ.block :: t →
    n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws, ρ.due F = true →
    (sendRow (V := V) (Pb := Pb) a J).bud u.number ((ρ.first.drop n).take u.rounds.length)
      (asksFrom (treeAsks F ρ 0) (u.rounds.map (·.2.length))
        (((rowsOfChain F.first.blocksInOrder).take n).map (·.2.length)).sum)

/-- The bound on the positions that the description's own rounds query: for every due list of
challenges and every oracle message k of P in a tree τ, the positions queried of the first chain's
tree number n₀ + τ give at most r distinct positions modulo the code's length, for the main code if
k has main rows and for the mask code if it has mask rows. A definition; derived from the test
readsWithinB in Johnson/SendSim/Seat/ReadsCountProof.lean. -/
def ReadsWithin (F : FileDescription Xi) (P : K1.Par) (n₀ : Nat) : Prop :=
  ∀ ρ : Draws, ρ.due F = true → ∀ k τ, k < P.sent.size →
    ((Own.treesMade P.codes P.sent).getD {}).tree[k]? = some τ →
    ((shapeAt P k).mainRows ≠ 0 →
      ((treeAsks F ρ 0 (n₀ + τ)).map
          (· % 2 ^ (P.codes.base.getD (shapeAt P k).code default).logN)).toFinset.card
        ≤ (P.codes.base.getD (shapeAt P k).code default).r) ∧
    ((shapeAt P k).maskRows ≠ 0 →
      ((treeAsks F ρ 0 (n₀ + τ)).map
          (· % 2 ^ (P.codes.mask.getD (shapeAt P k).maskCode default).logN)).toFinset.card
        ≤ (P.codes.mask.getD (shapeAt P k).maskCode default).r)

end OnBytes.SendSim.Seat
