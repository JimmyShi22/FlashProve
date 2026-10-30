-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the clauses of the condition at a proximity test's second part, by name.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/Clauses.lean: two groups of the clauses of OnFreeTD
(Sim/TreesExactDense.lean), to the letter, each under one name, so that each can be paid by its own
file: what a stand and its front give (FiveAt), and the first opening's columns (TreesAt). Definitions
only. No property of the protocol is claimed.

  FiveAt    le, leS, heardFit, heard, fold
  TreesAt   trees: the words that the front lists of each first tree are the job's own tree's
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesExactDense

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open Johnson.Prover.Link
open ProofFile.Honest ProofFile.Honest.K12

variable {W X : Type}

/-- What a stand and its front give: five clauses of OnFreeTD, to the letter. -/
structure FiveAt (J : TestJob W X) (mem : ℕ → Stretch) (m : Mid W X) (front : Before) : Prop where
  le : firstLen J.p.nums.stages ≤ m.st.heard.length
  leS : firstLen J.p.nums.stages ≤ m.seen.length
  heardFit : drawsFit (((laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
    (m.st.lately (firstLen J.p.nums.stages)) = true
  heard : (lastSeen front (firstLen J.p.nums.stages)).map (·.drawn) =
    m.st.lately (firstLen J.p.nums.stages)
  fold : (lastSeen front (firstLen J.p.nums.stages)).tail =
    aFold (coinsOf J.p.nums.stages (carriedCoins J mem).hide fun _ => 0) 0 J.s₀ 1 (rowsAt J mem m)
      (rowOf (J.recB m.st.input (restFront J m) (heardIn J m 0))) (heardIn J m)

/-- The clause trees of OnFreeTD, to the letter: the attacker's (E2): the trees are the job's, the
first fresh table's rows among what rowsAt holds. -/
def TreesAt (J : TestJob W X) (chain : ℕ) (os : List (Fmt.Shape × Fmt.TreeSource)) (mem : ℕ → Stretch)
    (m : Mid W X) (front : Before) : Prop :=
  (J.trees₀ m.st.input (restFront J m) mem (rowsAt J mem m)).map (·.1) = os.map (·.1.a) ∧
    ∀ (i : ℕ) (o : Fmt.Shape × Fmt.TreeSource) (T : Tree), os[i]? = some o →
      (J.trees₀ m.st.input (restFront J m) mem (rowsAt J mem m))[i]? = some T →
      ∃ cols, front.treeCols (srcOf chain o.2).1 (srcOf chain o.2).2 = some cols ∧
        ∀ q ∈ cols, q.2 = T.2 q.1

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.FiveAt
#print axioms ProofFile.Honest.K12.Sim2.TreesAt
