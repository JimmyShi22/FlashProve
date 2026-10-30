-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/CoveredAtReturns.lean: TWO FACTS ON THE LIBRARY's `S.coveredAt`
(Johnson/Desc/First/State.lean), OF NO KIND: GUESTS IN THIS FOLDER: typed for the file
CovOfAtStart.lean beside it; they would sit as well beside that function. PUBLIC DATA ALONE: a
request's words, two numbers of the plan, a token. Two lemmas with their proofs; no definition; none
of the library's goals.

  `coveredAt_of_reqOk`  where the state's own test on the request says yes (`S.reqOk`) and y is an
                        entry of the vocabulary: `S.coveredAt` returns at y
  `coveredAt_sized`     what it returns passes the verifier's test on the four arrays' sizes
                        (`Head.Covered.sized`, OnBytes/Model/HeadLayout.lean) at the same T

By. `S.coveredAt_eq` (Johnson/Desc/First/StateLaws.lean): that function is `verify-on-bytes`'s
`Head.coveredOf` at the state's words. `coveredOf_ok`, `coveredOf_lawful`
(OnBytes/Flat/CoveredJoin.lean): that one returns where its four tests hold; what it returns has T
tokens.

LINES THAT STAND ELSEWHERE TOO. The proof of `coveredAt_of_reqOk` has nine lines that unfold
`S.reqOk`; the same nine stand in the proof of the library's `covered_of_parts`
(Johnson/AtFull/Shape/ReplyEnds.lean), whose end speaks of the token in the reply's seat, not of a
letter. `coveredAt_sized` unfolds `S.coveredAt` and splits its four tests, as `coveredAt_on`
(Johnson/Desc/ProofFile/Honest/K11/ClaimOfQuiet.lean) and `coveredAt_sizes`
(Johnson/Desc/ProofFile/Honest/K3/WitReq.lean) do. The last of these, of other authors, states the
sizes of three of the four arrays as equations; here all four are said, through the verifier's own
test.

NEAR. `covered_answers` (Johnson/Desc/Kinds/Law/SilentAnswers.lean) and `covered_of_parts`: the
first from the same facts, ending at `S.covered`, the token in the state's own reply's seat: they do
not fit a state in which no reply is laid. `covered_blank` (Johnson/AtFull/Desc/BlankReturns.lean):
the first at one request. `covered_wiped` (OnBytes/K/Early.lean): where `Head.coveredOf` returns it
returns at the token 0. `sized_same` (OnBytes/K/ReplyMore.lean): what it returns at T passes the
sizes' test at no other number. `coveredAt_same` (Johnson/AtFull/Shape/ReqAtHead.lean).

Limits. Unfoldings and calls. Nothing on any property.
-/
import Johnson.Desc.First.StateLaws
import OnBytes.Flat.CoveredJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.First (S)

/-- **Where the state's test on the request says yes, the covered positions are there.** -/
theorem coveredAt_of_reqOk {T V y : Nat} {s : S} (hq : s.reqOk T V = true) (hy : y < V) :
    ∃ cov, s.coveredAt T V y = .ok cov := by
  unfold S.reqOk at hq
  simp only [Bool.and_eq_true, beq_iff_eq] at hq
  obtain ⟨⟨q1, q2⟩, q3⟩ := hq
  have eT : s.reqT = T := by
    unfold S.reqT
    omega
  unfold S.tokv at q2
  unfold S.rowR S.rowE at q3
  rw [eT] at q2 q3
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not, ge_iff_le,
    gt_iff_lt, Nat.not_le, Nat.not_lt] at q3
  rw [S.coveredAt_eq]
  exact OnBytes.Flat.coveredOf_ok _ T V hy q1
    (fun v hv => of_decide_eq_true (Array.all_eq_true_iff_forall_mem.1 q2 v hv)) q3.1 q3.2

/-- **What it returns passes the test on the four arrays' sizes.** -/
theorem coveredAt_sized {T V y : Nat} {s : S} {cov : OnBytes.Model.Head.Covered}
    (h : s.coveredAt T V y = .ok cov) : cov.sized T = true := by
  have h0 := h
  rw [S.coveredAt_eq] at h0
  have t := (OnBytes.Flat.coveredOf_lawful h0).1
  unfold S.coveredAt at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · obtain rfl := Except.ok.inj h
          unfold OnBytes.Model.Head.Covered.sized
          rw [t]
          simp only [Array.size_map, Array.size_range, beq_self_eq_true, Bool.and_self]

end ProofFile.Honest.K2.Law

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K2.Law.coveredAt_of_reqOk
#print axioms ProofFile.Honest.K2.Law.coveredAt_sized
