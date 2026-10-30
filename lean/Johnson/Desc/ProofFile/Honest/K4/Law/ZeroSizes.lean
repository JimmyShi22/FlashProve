-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ZeroSizes.lean: NO HYPOTHESIS. Nine statements with their
proofs.

What is here. HOW MANY COORDINATES THE SAMPLED VALUES HAVE AT THE ZERO CHALLENGES (`k4ZeroPts`,
Honest/K4/Part.lean) in front of each masked sumcheck of the feed-forward layers' own rounds (the
sub-protocol K4), at every public data Q and every value fo of what the lookup has sampled, WITH NO
HYPOTHESIS: the norms' token point in front of each of the seven; the point on the norms' numbers in
front of the first; the second token sumcheck's challenges in front of the fourth and every later
one; the batched sumcheck's in front of the fifth and every later one; the point on the layers with
routed experts in front of the sixth. Among these are sizes that the laws on the makers ask of
the sampled values (FitNorms, FitRows, FitStackPub and FitGated under Law/W/; none a part of the
library yet). How. The zero challenges hold as many elements as the verifier's table of rounds says,
and each round that makes a field stands in front of the sumcheck named (`k4StartAt`,
Law/StartsAre.lean; the fields by their rounds' numbers: Law/PtsVals.lean;
Johnson/Desc/K4/Honest/Law/PtsSizes.lean).

  `zero_own`, `zero_ownFits`, `zero_len`, `start_at`   the zero challenges in front of a sumcheck
  `PV_zero`, `rhoI_zero`, `rt_zero_at`, `rs_zero_at`, `rhoM_zero`   **the sizes**

Not shown here. Sizes alone. The embedding's two points at the merge's stand: Law/FitMergeZero.lean.
Nothing on soundness, on completeness or on any other property.

Kin. `rt_zero_at` and `rs_zero_at` at k = 6 ARE `rt_zero` and `rs_zero` (Law/FitMergeZero.lean),
stated again and not called; all four end as `pts_rt` and `pts_rs`
(Johnson/Desc/K4/Honest/Law/PtsSizes.lean) end, which are not called either. `zero_len` at k = 6 is
`zero_take_len` (Law/FitMergeZero.lean) in other letters. Sought: by statement, to the letter and up
to the bound letters, among the theorems of the library and of files that are no part of it yet, as
they lay with the writer: no hit; by short name: `start_at` stands in three further files of the
library (two read), `zero_len` and `zero_own` in one each under Honest/K12/Sim/ (read): other
matters.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FitMergeZero

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (RoundName Forest.Heard)
open OnBytes.Desc.First.K4 (Rd rounds masked layerRds pointRd batchRd k0)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.PtsLaw (OwnFits inner_size pts_PV pts_rhoI pts_rhoM preJoin
  preTerms preStack preJoin2)

variable (Q : K4Pub) (fo : Forest.Heard)

/-- K4's own among the zero challenges of which the first n have been heard. -/
theorem zero_own (n : ℕ) :
    ((k4ZeroHeard Q).take (Q.r0 + n)).drop Q.r0 = (k4ZeroOwn Q).take n := by
  unfold k4ZeroHeard
  exact drop_take_rep _ _ _ _

/-- They have the table's shape. -/
theorem zero_ownFits (n : ℕ) : OwnFits Q ((k4ZeroHeard Q).take (Q.r0 + n)) := by
  intro j d x hd hx
  rw [zero_own, List.getElem?_take] at hd
  split at hd
  · unfold k4ZeroOwn at hd
    rw [List.getElem?_map, hx] at hd
    obtain rfl := Option.some.inj hd
    simp
  · cases hd

/-- The number of a sumcheck's first round. -/
theorem start_at (k : ℕ) (hk : k < 7) : (starts Q).getD k 0 = k4StartAt Q k := by
  rw [starts_eq]
  match k, hk with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl

/-- In front of sumcheck number k stand as many of K4's own challenges as its first round's number
says. -/
theorem zero_len (k : ℕ) :
    (((k4ZeroHeard Q).take (Q.r0 + (starts Q).getD k 0)).drop Q.r0).length =
      (starts Q).getD k 0 := by
  have h := starts_le Q k
  rw [zero_own, List.length_take, k4ZeroOwn, List.length_map]
  omega

/-- **The norms' token point**, in front of each of the seven. -/
theorem PV_zero (k : ℕ) (hk : k < 7) :
    (k4ZeroPts Q fo ((starts Q).getD k 0)).PV.size = Q.P.y.h.lt := by
  refine pts_PV Q _ _ (zero_ownFits Q _) ?_
  rw [zero_len, start_at Q k hk]
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => simp only [k4StartAt]; omega

/-- **The point on the norms' numbers**, in front of the first. -/
theorem rhoI_zero : (k4ZeroPts Q fo ((starts Q).getD 0 0)).rhoI.size = Q.P.rd.lNI := by
  refine pts_rhoI Q _ _ (zero_ownFits Q _) ?_
  rw [zero_len, start_at Q 0 (by omega)]
  unfold preJoin k4StartAt k0
  by_cases hg : (Q.g == 0) = true <;> simp [hg]

/-- **The second token sumcheck's challenges**, in front of the fourth sumcheck and every later one.
-/
theorem rt_zero_at (k : ℕ) (h3 : 3 ≤ k) (hk : k < 7) :
    (k4ZeroPts Q fo ((starts Q).getD k 0)).rt.size = Q.P.y.h.lt := by
  have hle := starts_le Q k
  rw [start_at Q k hk] at hle ⊢
  unfold k4ZeroPts
  rw [pts_rt_val, zero_own]
  unfold innerAt
  refine inner_size _ _ _ ?_
  rw [List.length_take, k4ZeroOwn, List.length_map]
  interval_cases k <;> simp only [k4StartAt] at hle ⊢ <;> omega

/-- **The batched sumcheck's challenges**, in front of the fifth sumcheck and every later one. -/
theorem rs_zero_at (k : ℕ) (h4 : 4 ≤ k) (hk : k < 7) :
    (k4ZeroPts Q fo ((starts Q).getD k 0)).rs.size = Q.hp.lamS := by
  have hle := starts_le Q k
  rw [start_at Q k hk] at hle ⊢
  unfold k4ZeroPts
  rw [pts_rs_val, zero_own, Array.size_reverse]
  unfold innerAt
  refine inner_size _ _ _ ?_
  rw [List.length_take, k4ZeroOwn, List.length_map]
  interval_cases k <;> simp only [k4StartAt] at hle ⊢ <;> omega

/-- **The point on the layers with routed experts**, in front of the sixth. -/
theorem rhoM_zero : (k4ZeroPts Q fo ((starts Q).getD 5 0)).rhoM.size = Q.P.y.h.ll - 1 := by
  refine pts_rhoM Q _ _ (zero_ownFits Q _) ?_
  rw [zero_len, start_at Q 5 (by omega)]
  unfold preJoin2 preStack preTerms preJoin layerRds k4StartAt k0
  by_cases hg : (Q.g == 0) = true <;> simp [hg, masked_len] <;> omega

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.zero_own
#print axioms ProofFile.Honest.K4.zero_ownFits
#print axioms ProofFile.Honest.K4.start_at
#print axioms ProofFile.Honest.K4.zero_len
#print axioms ProofFile.Honest.K4.PV_zero
#print axioms ProofFile.Honest.K4.rhoI_zero
#print axioms ProofFile.Honest.K4.rt_zero_at
#print axioms ProofFile.Honest.K4.rs_zero_at
#print axioms ProofFile.Honest.K4.rhoM_zero
