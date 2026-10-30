-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/P1/SumTruth.lean: the sumcheck's sets of bad challenges ARE EMPTY AT THE TRUTH.
Algebra over a field, as in SumCore.lean: no text of a verifier, no bytes, no monad. Definitions,
statements and proofs.

Why. `sumcheck_rbr` and `masked` (SumCore.lean) give the sets of bad challenges under "there are",
with their sizes alone. So of a given honest run nobody can show that no bad element was drawn.
Here the two statements stand once more, to the letter, with one thing more under "there are" and
two facts more.

  `honest tq pre rs`: the run in which, behind the challenges pre, each round's polynomial is what
    tq gives for the challenges in front of it, and the challenges are rs.
  `sumcheck_rbr_true`: if S is summed to c, there are a function tq (the true round polynomial
    behind the challenges in front) and sets of bad challenges with: the sizes and the law of
    `sumcheck_rbr`; the set that belongs to the true polynomial is empty, whatever rounds stand in
    front; and for all challenges rs, one for each variable, the honest run is a run from c to S rs.
  `noBad_honest`: so no challenge of an honest run is bad.
  `masked_true`: the same for `masked`. If Cv is the sum, no eps is bad, and for every eps the
    honest run goes from muT + eps t to the masked summand at the challenges.

Two cheap fillings, tried. With tq the zero polynomial everywhere, the honest run would have to be a
run from c, so the zero polynomial's sum, 0, would have to be c. With no bad challenge at all, the
law would have to hold of every run, also of one whose first polynomial is wrong and agrees with the
true one at the first challenge. These are arguments in words, not theorems.

What is not shown. Nothing joins tq to what a prover's program sends. Nothing is said of
probabilities: sets are counted. The proofs are SumCore.lean's own, with the new parts laid in;
SumCore.lean is not turned.
-/
import OnBytes.Desc.First.P1.SumCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Desc.First.P1
open Polynomial

variable {K : Type} [Field K]

/-! ### The honest run -/

/-- The run behind the challenges pre in which each round's polynomial is tq of the challenges in
front of it. -/
def honest (tq : List K → K[X]) : List K → List K → List (K[X] × K)
  | _, [] => []
  | pre, r :: rs => (tq pre, r) :: honest tq (pre ++ [r]) rs

theorem honest_cons (tq : List K → K[X]) (pre : List K) (r : K) (rs : List K) :
    honest tq pre (r :: rs) = (tq pre, r) :: honest tq (pre ++ [r]) rs := rfl

theorem honest_shift (tq : List K → K[X]) (x : K) : ∀ (rs pre : List K),
    honest tq (x :: pre) rs = honest (fun l => tq (x :: l)) pre rs
  | [], _ => rfl
  | r :: rs, pre => by
    show (tq (x :: pre), r) :: honest tq (x :: (pre ++ [r])) rs =
      (tq (x :: pre), r) :: honest (fun l => tq (x :: l)) (pre ++ [r]) rs
    rw [honest_shift tq x rs (pre ++ [r])]

/-- The challenges of an honest run. -/
theorem honest_chal (tq : List K → K[X]) : ∀ (rs pre : List K),
    (honest tq pre rs).map (·.2) = rs
  | [], _ => rfl
  | r :: rs, pre => by
    rw [honest_cons, List.map_cons, honest_chal tq rs (pre ++ [r])]

/-- Each polynomial of an honest run is tq of the challenges in front of it. -/
theorem honest_poly (tq : List K → K[X]) : ∀ (rs pre : List K) (i : ℕ) (m : K[X] × K),
    (honest tq pre rs)[i]? = some m →
    m.1 = tq (pre ++ ((honest tq pre rs).take i).map (·.2))
  | [], _, _, _, h => by simp [honest] at h
  | r :: rs, pre, 0, m, h => by
    rw [honest_cons, List.getElem?_cons_zero] at h
    rw [← Option.some.inj h]
    simp
  | r :: rs, pre, i + 1, m, h => by
    rw [honest_cons, List.getElem?_cons_succ] at h
    rw [honest_poly tq rs (pre ++ [r]) i m h]
    simp [honest_cons]

/-- If the set that belongs to tq's polynomial is always empty, no challenge of an honest run is
bad. -/
theorem noBad_honest [DecidableEq K] {tq : List K → K[X]}
    {bad : List (K[X] × K) → K[X] → Finset K}
    (h : ∀ pre, bad pre (tq (pre.map (·.2))) = ∅) (rs : List K) :
    NoBad bad (honest tq [] rs) := by
  intro i m hi
  have e := honest_poly tq rs [] i m hi
  rw [List.nil_append] at e
  rw [e, h]
  simp

/-! ### The sumcheck -/

/-- **The sumcheck, round by round, with the truth.** -/
theorem sumcheck_rbr_true [DecidableEq K] : ∀ (vs : List (Wt K)) (S : List K → K) (c : K),
    IsSum vs S c →
    ∃ (tq : List K → K[X]) (bad : List (K[X] × K) → K[X] → Finset K),
      (∀ pre g, (bad pre g).card < dAt vs pre.length) ∧
      (∀ ms c0 cf, Chain vs ms c0 cf → cf = S (ms.map (·.2)) → NoBad bad ms → c0 = c) ∧
      (∀ pre, bad pre (tq (pre.map (·.2))) = ∅) ∧
      ∀ rs, rs.length = vs.length → Chain vs (honest tq [] rs) c (S rs)
  | [], S, c, h =>
    ⟨fun _ => 0, fun _ _ => ∅, fun _ _ => by simp [dAt], fun ms c0 cf hc hf _ => by
      cases ms with
      | nil =>
        have h1 : c0 = cf := hc
        rw [h1, hf]
        exact h
      | cons m ms => exact absurd hc (by simp [Chain]), fun _ => rfl, fun rs hr => by
      cases rs with
      | nil =>
        show c = S []
        exact (show S [] = c from h).symm
      | cons r rs => simp at hr⟩
  | w :: vs, S, c, ⟨q, hd, hs, hq⟩ => by
    classical
    have ih := fun x => sumcheck_rbr_true vs (fun rs => S (x :: rs)) (q.eval x) (hq x)
    choose tqx badx hcard hrun hempty hhon using ih
    refine ⟨fun l =>
      match l with
      | [] => q
      | x :: xs => tqx x xs, fun pre g =>
      match pre with
      | [] => if g.natDegree < w.d ∧ g ≠ q then (g - q).roots.toFinset else ∅
      | m :: pre' => badx m.2 pre' g, ?_, ?_, ?_, ?_⟩
    · intro pre g
      cases pre with
      | nil =>
        have hpos : 0 < w.d := lt_of_le_of_lt (Nat.zero_le _) hd
        show (if g.natDegree < w.d ∧ g ≠ q then (g - q).roots.toFinset else ∅).card < w.d
        split
        · rename_i hg
          calc (g - q).roots.toFinset.card ≤ Multiset.card (g - q).roots :=
                Multiset.toFinset_card_le _
            _ ≤ (g - q).natDegree := card_roots' _
            _ ≤ max g.natDegree q.natDegree := natDegree_sub_le _ _
            _ < w.d := max_lt hg.1 hd
        · simpa using hpos
      | cons m pre' =>
        have := hcard m.2 pre' g
        simpa [dAt] using this
    · intro ms c0 cf hc hf hb
      cases ms with
      | nil => exact absurd hc (by simp [Chain])
      | cons m ms =>
        obtain ⟨hg, hsum, hrest⟩ := hc
        have hb' : NoBad (badx m.2) ms := fun i m' hi => by
          have := hb (i + 1) m' (by simpa using hi)
          simpa using this
        have he : m.1.eval m.2 = q.eval m.2 := hrun m.2 ms _ cf hrest (by simpa using hf) hb'
        have h0 := hb 0 m (by simp)
        by_cases hgq : m.1 = q
        · rw [← hsum, hgq, hs]
        · exfalso
          apply h0
          show m.2 ∈ (if m.1.natDegree < w.d ∧ m.1 ≠ q then (m.1 - q).roots.toFinset else ∅)
          rw [if_pos ⟨hg, hgq⟩, Multiset.mem_toFinset, mem_roots (sub_ne_zero.mpr hgq)]
          show (m.1 - q).eval m.2 = 0
          rw [eval_sub, he, sub_self]
    · intro pre
      cases pre with
      | nil =>
        show (if q.natDegree < w.d ∧ q ≠ q then (q - q).roots.toFinset else ∅) = ∅
        rw [if_neg fun hh => hh.2 rfl]
      | cons m pre' => exact hempty m.2 pre'
    · intro rs hr
      cases rs with
      | nil => simp at hr
      | cons r rs' =>
        have hr' : rs'.length = vs.length := by simpa using hr
        rw [honest_cons, List.nil_append, honest_shift]
        exact ⟨hd, hs, hhon r rs' hr'⟩

/-! ### The masked sumcheck -/

/-- **The masked sumcheck, with the truth.** The statement of `masked`, and: if Cv is the sum, no
eps is bad; for every eps the set that belongs to the true polynomial is empty; and if Cv is the
sum, the honest run goes from muT + eps t to U + eps S + eps (t - Cv) Psi at the challenges. -/
theorem masked_true [DecidableEq K] (vs : List (Wt K)) (U S Psi : List K → K) (muT sigma : K)
    (hU : IsSum vs U muT) (hS : IsSum vs S sigma) (hP : IsSum vs Psi 1) (mu t Cv : K) :
    ∃ (badE : Finset K) (tq : K → List K → K[X])
      (bad : K → List (K[X] × K) → K[X] → Finset K),
      badE.card ≤ 1 ∧ (∀ eps pre g, (bad eps pre g).card < dAt vs pre.length) ∧
      (∀ eps ms cf, Chain vs ms (mu + eps * t) cf →
        cf = U (ms.map (·.2)) + eps * S (ms.map (·.2)) + eps * (t - Cv) * Psi (ms.map (·.2)) →
        eps ∉ badE → NoBad (bad eps) ms → Cv = sigma) ∧
      (Cv = sigma → badE = ∅) ∧
      (∀ eps pre, bad eps pre (tq eps (pre.map (·.2))) = ∅) ∧
      (Cv = sigma → ∀ eps rs, rs.length = vs.length →
        Chain vs (honest (tq eps) [] rs) (muT + eps * t)
          (U rs + eps * S rs + eps * (t - Cv) * Psi rs)) := by
  classical
  have hG : ∀ eps, IsSum vs (fun rs => U rs + eps * S rs + eps * (t - Cv) * Psi rs)
      (muT + eps * sigma + eps * (t - Cv) * 1) := fun eps =>
    (hU.add (hS.smul eps)).add (hP.smul (eps * (t - Cv)))
  choose tq bad hcard hrun hempty hhon using fun eps => sumcheck_rbr_true vs _ _ (hG eps)
  refine ⟨if Cv = sigma then ∅ else {(mu - muT) / (sigma - Cv)}, tq, bad, ?_, hcard, ?_,
    fun hC => if_pos hC, hempty, ?_⟩
  · split <;> simp
  · intro eps ms cf hc hf he hb
    have h := hrun eps ms _ cf hc hf hb
    by_contra hne
    rw [if_neg hne, Finset.mem_singleton] at he
    apply he
    have hs : sigma - Cv ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    rw [eq_div_iff hs]
    linear_combination -h
  · intro hC eps rs hr
    have e : muT + eps * t = muT + eps * sigma + eps * (t - Cv) * 1 := by
      rw [hC]
      ring
    rw [e]
    exact hhon eps rs hr

end OnBytes.Desc.First.P1
