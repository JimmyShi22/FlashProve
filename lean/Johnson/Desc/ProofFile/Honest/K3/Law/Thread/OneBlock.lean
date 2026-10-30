-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/OneBlock.lean: what the frame's `chainSteps`
(Honest/Frame.lean) has made where it has returned at a list of one sub-protocol at whose place a
half stands. General in the half: no lookup is named. One theorem.

Terms. Honest/K3/GLOSSARY.md: see there frame, half, book and coins, step and sub-protocol.

What is shown.
  `chainSteps_one`: the sub-protocol states a list of oracle messages for each round; the half has
    as many rounds; the book has lent the row its coins; and the steps are the half's own at these.

Hypotheses that remain.
  `hf`: the search at the sub-protocol's place finds the half g.
  `h`: `chainSteps` returns at the list of that one sub-protocol.

Imported. The frame's definitions alone: Honest/Frame.lean.

Users. Honest/K3/Law/Thread/Plays.lean, Honest/K3/Law/Thread/Accepted.lean,
Honest/K3/Law/Thread/AtThread.lean and Honest/K3/Law/Thread/PlaysAnyState.lean call it.

Limits. A lemma on a definition of the frame's.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block)

variable {S Cl V W X : Type}

/-- **Where `chainSteps` has returned at one sub-protocol with a half.** -/
theorem chainSteps_one (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (b : Block S Cl) (hs : List (Placed V W X)) (g : Placed V W X)
    (hf : hs.find? (fun h => h.place == b.place) = some g) (l : List (Step W X))
    (h : chainSteps B rows look v [b] hs = .ok l) :
    b.oracles.length = b.rounds.length ∧ g.rounds = b.rounds.length ∧
      ∃ c, lendRow B rows look b.place g.parts 0 = .ok c ∧ l = g.steps b v c := by
  unfold chainSteps at h
  split at h
  · exact nomatch h
  · rename_i h1
    rw [hf] at h
    simp only at h
    split at h
    · exact nomatch h
    · rename_i h2
      split at h
      · exact nomatch h
      · split at h
        · exact nomatch h
        · split at h
          · exact nomatch h
          · cases hc : lendRow B rows look b.place g.parts 0 with
            | error e =>
              rw [hc] at h
              exact nomatch h
            | ok c =>
              rw [hc] at h
              have h' : (Except.ok (g.steps b v c ++ []) : Except String (List (Step W X))) =
                .ok l := h
              refine ⟨by simpa using h1, by simpa using h2, c, rfl, ?_⟩
              have := Except.ok.inj h'
              rw [List.append_nil] at this
              exact this.symm

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.chainSteps_one
