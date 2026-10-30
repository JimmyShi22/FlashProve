-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/SameVectorAtRun.lean: "the same vector": the premise hv of the
statements on o_u's tree (`tree0_atU`, TreeIsColumnAt.lean; `tree0_lent_U`, CutOfBookAt.lean), at
two stands that have heard front pieces of one list of challenges: the vector that the proximity
test's member hands to `laid` at the test's front is the one that "send o_u" computes at its own
state.

Why it holds. What "send o_u" lays as its vector reads, of the challenges heard, none but the first
`atPoint` + 1: that is a law of the authors of the honest side of the linear claim's shared rounds
(`jobU_readsBelow`, over their notion `SendJob.readsBelow`: Honest/K14/SendingsPaid.lean). Both
stands have heard these.

  `data_same`        a job whose data reads none but the first n challenges has one data at two
                   lists that agree there: general in the job
  `same_vector`      the statement

Limits. The member carries no vector of its own (`v? := none`): at `some v` the member's vector is
v, and nothing is said. That two stands of a run have heard such pieces and have one input are
premises here. "send o_u" alone. A tie between terms: it names no value. Nothing on completeness,
soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.TreeIsColumnAt
import Johnson.Desc.ProofFile.Honest.K12.Sim.Row
import Johnson.Desc.ProofFile.Honest.K14.SendingsPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open ProofFile.Honest.K14 (SendJob SendPub jobU Ask jobU_readsBelow)

/-- A job whose data reads none but the first n challenges has one data at two lists that agree
there. -/
theorem data_same {J : SendJob} {n : ℕ} (hJ : J.readsBelow n) (a : Ask) (h h' : List Fmt.Drawn)
    (e : h.take n = h'.take n) :
    J.data { input := a, heard := h, own := () } =
      J.data { input := a, heard := h', own := () } := by
  rw [← hJ a h, ← hJ a h', e]

/-- **"THE SAME VECTOR", AT TWO STANDS OF ONE LIST OF CHALLENGES.** m: the stand in front of the
test's second part; mb: the sender's stand, in front of its first round. Both have heard front
pieces of one list ρs (hm, hb) and have one input (hi). "LIN point" lies in front of the sender's
round (h1) and of the test (h2). The member carries no vector of its own. Then the vector that the
member's text hands to `laid` at the test's front is the one that the sender computes at its own
state. -/
theorem same_vector {W X : Type} (A : SendPub) (ask : W → Ask) (J : TestJob W X)
    (m mb : ProofFile.Honest.Mid W X) (ρs : List Fmt.Drawn) (n N : ℕ) (hm : m.st.heard = ρs.take n)
    (hb : mb.st.heard = ρs.take N) (hi : mb.st.input = m.st.input) (h1 : A.atPoint < N)
    (h2 : A.atPoint + firstLen J.p.nums.stages < m.st.heard.length) :
    vecAt (jobU A) 0 ask none m.st.input (restFront J m) =
      (jobU A).data { input := ask mb.st.input, heard := mb.st.heard, own := () } 0 := by
  have hlen : m.st.heard.length ≤ n := by
    rw [hm]
    exact List.length_take_le _ _
  show (jobU A).data
    ⟨ask m.st.input, m.st.heard.take (m.st.heard.length - firstLen J.p.nums.stages), ()⟩ 0 = _
  rw [hi]
  refine congrFun (data_same (jobU_readsBelow A) _ _ _ ?_) 0
  rw [List.take_take, Nat.min_eq_left (by omega), hm, hb, List.take_take, List.take_take,
    Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.data_same
#print axioms ProofFile.Honest.K12.Light.same_vector
