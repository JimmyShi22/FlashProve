-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/ThrUnique.lean: AT ONE STAND OF THE PROVER's RUN THE THREAD
HOLDS OF ONE STATE OF THE VERIFIER ALONE. The thread's clause on how the state was made
(`Thread.Made`, Honest/Thread/Thr.lean) says that the state is the library's fold of the members in
front over the rounds that the run has shown and the columns that its tables give, from a state at
which the chain begins. The fold is a function; the columns are a function's value. So where the
chain's beginning is one state, two states under the thread at one border, one run's coins, one
stand and one set of tables are one. General in the thread. It is a step toward a term for the
second chain's letter `ends` (Honest/Thread/LastHead.lean): the two earlier chains' last states as
functions.

  `thr_state_unique`

Limits. The stand m and the tables E are the same on both sides: that they are functions of the
coins, the input and the challenges heard is another sentence (no clause of `Thr` says that m is
where the frame's own play stands). None is one of the library's goals. This file proves nothing
about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Thr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

/-- **ONE STAND, ONE STATE.** hfun: the chain begins at one state. -/
theorem thr_state_unique {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
    (hfun : ∀ k w hd s₀ s₁, T.begun k w hd s₀ → T.begun k w hd s₁ → s₀ = s₁) {b : Nat}
    {k : Coins Bk} {s s' : S} {m : Mid W X} {E : Env} (h : Thr T b k s m E)
    (h' : Thr T b k s' m E) : s = s' := by
  unfold Thr at h h'
  obtain ⟨-, -, -, -, hM, -, -⟩ := h
  obtain ⟨-, -, -, -, hM', -, -⟩ := h'
  unfold Thread.Made at hM hM'
  obtain ⟨-, -, -, -, s₀, cols, hb, hc, hf⟩ := hM
  obtain ⟨-, -, -, -, s₁, cols', hb', hc', hf'⟩ := hM'
  have e0 : s₀ = s₁ := hfun _ _ _ _ _ hb hb'
  have ec : cols = cols' := by
    rw [hc] at hc'
    exact Except.ok.inj hc'
  subst e0
  subst ec
  rw [hf] at hf'
  exact (Prod.mk.inj (Except.ok.inj hf')).1

end ProofFile.Honest

#print axioms ProofFile.Honest.thr_state_unique
