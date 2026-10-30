-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the words in front of a stand are below the prime, from the thread's letter.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/OkAtInside.lean: the field ok of LeftAtStand (ListPaid.lean):
where the invariant at a block's border says SaidOk of what has been seen, every word that the rounds
seen at a stand inside the block show is below the prime, and so at every front part of them.

  ok_of_inside   the statement

hA: the invariant holds the letter SaidOk (Thread/SaidOk.lean), as ThrS at a Said that holds it does.
No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.Thread.SaidOk
import Johnson.Desc.ProofFile.Honest.Law.Inside

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block viewWordsBelowPrime)
open ProofFile.Honest

variable {S Cl V W Y Pb : Type} {Bk : ProverCoinCounts}

/-- **The words in front of a stand.** -/
theorem ok_of_inside {φ : Face V W Pb} {chain : ℕ} {hs : List (Placed V W Y)} {b : Block S Cl}
    {A : Coins Bk → S → Mid W Y → Env → Prop} {n : ℕ} {k : Coins Bk} {m : Mid W Y} {E : Env}
    (hA : ∀ k s m E, A k s m E → viewWordsBelowPrime ⟨m.seen, []⟩ = true)
    (hin : InsideOf φ Bk chain hs b A n k m E) (i : ℕ) :
    viewWordsBelowPrime ⟨m.seen.take i, []⟩ = true := by
  obtain ⟨s, m₀, E₀, l, ds, y, a, hl, hd, hp, rfl, -⟩ := hin
  have hdl : (l.take n).map (·.decl) = b.rounds.take n := by
    rw [List.map_take, steps_decl hl, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have h1 := okViewW_of_yields _ _ _ _ (play_yields _ _ _ _ _ hp)
    (by rw [hdl]; exact drawsFit_bare _ _ hd) okViewW_nil
  have h2 : viewWordsBelowPrime ⟨y.2.seen, []⟩ = true := by
    rw [(play_mid _ _ _ _ _ hp).2.2]
    exact (okRounds_append _ _).2 ⟨hA _ _ _ _ a, h1⟩
  exact okRounds_sub h2 fun r hr => List.mem_of_mem_take hr

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.ok_of_inside
