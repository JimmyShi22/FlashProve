-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/ReachBack.lean: FROM THE THREAD AT A BORDER TO THE LIBRARY's
"REACHED" (`Reach`, Johnson/Top/H0/Walk/Reach.lean), AND ONE STEP BACK ALONG IT. The thread's clause
(X) holds the verifier's own fold over the members in front; `reach_of_made`
(Honest/Thread/MadeLaw.lean) turns that into `Reach`, over the members' OWN steps. Here: the same
from the whole thread; and, at a border behind a member: the state in front of that member, reached
too, and THAT MEMBER's OWN YES from it to the state at the border. Lemmas; no definition. General in
the thread.

  `thr_reach_of`   the thread at b gives `Reach` at b, where b is a border of the chain (hb) and
     `begun` allows the state `start z` alone (h0)
  `thr_back`   under the like hb and h0: the thread at b + 1 gives a state s, reached at b, and
     `StepYes` of the member number b from s
  `thr_back_decide`   the same with the yes of the member's own decision

WHAT IT IS FOR. What the member number b lays into the verifier's state is had at b + 1 from its own
yes, by whatever lemma the authors of its kind have from a yes: so a member right behind it that
uses the fact needs no clause of the invariant's parameter `rides` for it.

Limits. THE STATE s IS BOUND INSIDE THESE LEMMAS' OWN "THERE IS": it is not said to be the state at
which the thread stood at b. The rounds and the columns of the yes are bound inside `StepYes`: of
these the library's own head says "no law may speak of 'the' rounds"
(Johnson/Top/H0/Walk/Reach.lean): nothing may be concluded of the run's transcript from them. ONE
STEP: what an earlier member has laid wants that every member between leaves it. None is one of the
library's goals. This file proves nothing about soundness, completeness, hiding or any other
property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw
import Johnson.Top.H0.Walk.ReachInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **THE THREAD AT A BORDER GIVES "REACHED" THERE.** start, z: the chain's first state as a
function of a public part, and that part (h0). -/
theorem thr_reach_of {P : Type} (start : P → S) (z : P) {b : Nat} {k : Coins Bk} {s : S}
    {m : Mid W X} {E : Env} (hb : b ≤ T.bs.length)
    (h0 : ∀ s₀, T.begun k m.st.input (m.st.heard.take T.front) s₀ → s₀ = start z)
    (hT : Thr T b k s m E) : Reach T.ft T.bs start b (z, s) := by
  unfold Thr at hT
  exact reach_of_made T start z hb h0 hT.2.2.2.2.1

/-- **ONE STEP BACK.** -/
theorem thr_back {P : Type} (start : P → S) (z : P) {b : Nat} {k : Coins Bk} {s' : S}
    {m : Mid W X} {E : Env} (hb : b + 1 ≤ T.bs.length)
    (h0 : ∀ s₀, T.begun k m.st.input (m.st.heard.take T.front) s₀ → s₀ = start z)
    (hT : Thr T (b + 1) k s' m E) :
    ∃ s blk, T.bs[b]? = some blk ∧ Reach T.ft T.bs start b (z, s) ∧ StepYes T.ft blk s s' := by
  have hr := thr_reach_of T start z hb h0 hT
  cases hr with
  | succ hr' hblk hy => exact ⟨_, _, hblk, hr', hy⟩

/-- The same with the yes of the member's own decision. -/
theorem thr_back_decide {P : Type} (start : P → S) (z : P) {b : Nat} {k : Coins Bk} {s' : S}
    {m : Mid W X} {E : Env} (hb : b + 1 ≤ T.bs.length)
    (h0 : ∀ s₀, T.begun k m.st.input (m.st.heard.take T.front) s₀ → s₀ = start z)
    (hT : Thr T (b + 1) k s' m E) :
    ∃ s blk rs gs, T.bs[b]? = some blk ∧ Reach T.ft T.bs start b (z, s) ∧
      blk.decide s rs gs = .ok s' := by
  obtain ⟨s, blk, hblk, hr, hy⟩ := thr_back T start z hb h0 hT
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  exact ⟨s, blk, rs, gs, hblk, hr, hd⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.thr_reach_of
#print axioms ProofFile.Honest.thr_back
#print axioms ProofFile.Honest.thr_back_decide
