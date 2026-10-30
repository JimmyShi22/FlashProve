-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/PtsFront.lean.

What is here. THE HONEST PARTS' SAMPLED VALUES (`ptsOf`, Johnson/Desc/K4/Honest/Front.lean) IN FRONT
OF THEIR ROUNDS: a field whose challenges have not all been heard is the empty array: the point of
the embedding outside the first group of layers, at every prefix; the two gated products' levels'
points at a prefix that ends in front of the level's last round. Statements and proofs.

K4 is the sub-protocol of the feed-forward layers' rounds.

  `innerAt_short`, `levelR_empty`   tools
  `at_ZE_else`   the embedding's point outside the first group
  `at_r12_front`, `at_r14_front`   the two levels' points in front of their last rounds

Limits. Equations between arrays of machine words, off the makers' text alone: no verifier's
function is named. One premise: as many challenges stand in front of the sub-protocol as the public
data say. Nothing on any other field. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PtsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (orderRange)
open OnBytes.Desc.First.K4.Honest

/-- Until all n challenges behind number s have been heard there is none of them. -/
theorem innerAt_short (own : List Fmt.Drawn) (s n : ℕ) (h : own.length < s + 1 + n) :
    innerAt own s n = #[] := by
  unfold innerAt whole
  by_cases hn : n = 0
  · subst hn
    simp [onesFrom]
  · have hs : (onesFrom own (s + 1) n).size ≠ n := by
      unfold onesFrom
      rw [List.size_toArray, List.length_map, List.length_take, List.length_drop]
      omega
    rw [if_neg (by rw [beq_iff_eq]; exact hs)]

/-- Of no challenges a level's point is empty. -/
theorem levelR_empty (mu : ℕ) (order : List ℕ) : levelR mu order #[] = #[] := by
  unfold levelR
  by_cases h : mu = 0
  · subst h
    simp
  · have h' : ((#[] : Array E).size != mu) = true := by
      rw [bne_iff_ne]
      exact fun e => h e.symm
    rw [if_pos h']

variable {Q : K4Pub} (w : K4In) (h : List Fmt.Drawn)

/-- **Outside the first group of layers the embedding's point is empty**, at every list of
challenges. -/
theorem at_ZE_else (hg : (Q.g == 0) = false) (heard : List Fmt.Drawn) :
    (ptsOf Q w heard).ZE = #[] := by
  rw [pts_ZE_val, hg]
  rfl

/-- **The first gated product's level's point is empty** at a prefix that ends in front of the
level's last round. -/
theorem at_r12_front (ds : List Fmt.Drawn) (hh : h.length = Q.r0) (n : ℕ)
    (hn : n < k4StartAt Q 4 + 1 + Q.P.rd.muH) : (ptsOf Q w (h ++ ds.take n)).r12 = #[] := by
  rw [pts_r12_val, own_take Q h ds hh, innerAt_short _ _ _ (by
    rw [List.length_take]
    omega), levelR_empty]

/-- **The second's likewise.** -/
theorem at_r14_front (ds : List Fmt.Drawn) (hh : h.length = Q.r0) (n : ℕ)
    (hn : n < k4StartAt Q 5 + 1 + Q.P.rd.muH2) : (ptsOf Q w (h ++ ds.take n)).r14 = #[] := by
  rw [pts_r14_val, own_take Q h ds hh, innerAt_short _ _ _ (by
    rw [List.length_take]
    omega), levelR_empty]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.innerAt_short
#print axioms ProofFile.Honest.K4.levelR_empty
#print axioms ProofFile.Honest.K4.at_ZE_else
#print axioms ProofFile.Honest.K4.at_r12_front
#print axioms ProofFile.Honest.K4.at_r14_front
