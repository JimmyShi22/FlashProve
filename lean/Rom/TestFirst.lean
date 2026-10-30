-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/TestFirst.lean: the adaptive rule `ndTest` (hash block 0 first; the rest only if it passes the
check, or if this is the last attempt), for any check pass, flag l and marks st.

An algorithm searches for a nonce (proof of work): it makes the same kind of query with one nonce
after the other until hash block 0 of the answer passes a check, and goes on with that answer; if
none passes, with the last. Of a failed attempt that is not the last it reads hash block 0 only.

`ndTest pass l st` is the rule at one query: hash block 0 is always queried; hash block j ≥ 1 is
queried if (hash block 0 passes or l) and st marks j. pass: the check on hash block 0; l: whether
this attempt is the last (read off the query); st: which hash blocks the final attempt needs (marks,
as in Rom/OverOneN.lean). `ndTest pass l st` is a rule for the step of Rom/SpecOverOneA.lean (the
step to one hash function under an adaptive rule for which hash blocks of an answer are queried).

For this rule the file has the sequence that it shows (`maskFrom_ndTest`) and the number of hash
blocks that it queries (`cntFrom_ndTest`). (`maskFrom`: Rom/NeedA.lean; `cntFrom`, `shownA`, `numA`:
Rom/SpecOverOneA.lean.) Section 3 has the same at a query to a typed oracle: `block0_shownA`,
`shownA_kept`, `numA_fail`, `numA_le`.

Notation:
  `Dg lam`: a hash block, `Fin lam → Bool` (Rom/NeedA.lean)
  `NeedA` (Rom/NeedA.lean): a rule that says which hash blocks are queried
  `maskFrom nd bl K j acc` (Rom/NeedA.lean): a rule applied to a given sequence of hash blocks; no
      oracle is queried
  `cntFrom` (Rom/SpecOverOneA.lean): how many hash blocks a rule queries on a given sequence: the
      recursion of maskFrom, counted
  `extBl` (Rom/NeedA.lean): K hash blocks, continued by the all-zero block
  `OracleCoding S lam` (Rom/Family.lean): the query encoding; `m.blocks o`: a natural number for each
      oracle; `m.rng o : S.Rng o ≃ (Fin (m.blocks o) → Fin lam → Bool)`
  f: one oracle from bit strings to `lam` bits (Rom/Family.lean)

Limits: the search itself is not written out here, and no bound on the number of its queries is
proved. Nothing on any scheme.
-/
import Rom.OverOneA

set_option autoImplicit false

namespace Rom

variable {lam : ℕ}

/-! ## 1. The rule -/

/-- Hash block 0 first; the rest only if it passes the check, or if this attempt is the last. -/
def ndTest (pass : Dg lam → Bool) (l : Bool) (st : ℕ → Bool) : ℕ → (ℕ → Dg lam) → Bool :=
  fun j acc => j == 0 || ((pass (acc 0) || l) && st j)

/-- the number of marked indices among j, .., j + K − 1 -/
def cntSt (st : ℕ → Bool) : (K j : ℕ) → ℕ
  | 0, _ => 0
  | K + 1, j => (if st j then 1 else 0) + cntSt st K (j + 1)

theorem cntSt_le (st : ℕ → Bool) : ∀ K j, cntSt st K j ≤ K
  | 0, _ => le_rfl
  | K + 1, j => by
    have := cntSt_le st K (j + 1)
    unfold cntSt
    split_ifs <;> omega

/-! ## 2. What it queries and what it shows -/

/-- after hash block 0 the rule does not look further: hash block j + 1 is queried if (hash block 0
passes or l) and st marks it -/
theorem ndTest_succ (pass : Dg lam → Bool) (l : Bool) (st : ℕ → Bool) (j : ℕ) (acc : ℕ → Dg lam) :
    ndTest pass l st (j + 1) acc = ((pass (acc 0) || l) && st (j + 1)) := rfl

theorem cntFrom_tail (pass : Dg lam → Bool) (l : Bool) (st : ℕ → Bool) (bl : ℕ → Dg lam) :
    ∀ (K j : ℕ) (acc : ℕ → Dg lam), 1 ≤ j →
      cntFrom (ndTest pass l st) bl K j acc = if (pass (acc 0) || l) = true then cntSt st K j else 0
  | 0, _, _, _ => by simp [cntFrom, cntSt]
  | K + 1, j, acc, hj => by
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    unfold cntFrom cntSt
    rw [ndTest_succ]
    cases hd : (pass (acc 0) || l) with
    | false =>
      show cntFrom (ndTest pass l st) bl K (j + 1 + 1) acc = _
      rw [cntFrom_tail pass l st bl K (j + 1 + 1) acc (by omega), hd]
      simp
    | true =>
      cases hs : st (j + 1) with
      | false =>
        show cntFrom (ndTest pass l st) bl K (j + 1 + 1) acc = _
        rw [cntFrom_tail pass l st bl K (j + 1 + 1) acc (by omega), hd]
        simp
      | true =>
        show 1 +
            cntFrom (ndTest pass l st) bl K (j + 1 + 1) (Function.update acc (j + 1) (bl (j + 1))) =
          _
        rw [cntFrom_tail pass l st bl K (j + 1 + 1) _ (by omega),
          Function.update_of_ne (by omega), hd]
        simp

/-- The count: on a sequence bl of K + 1 hash blocks the rule queries 1 + (if pass (bl 0) or l then
`cntSt st K 1` else 0) hash blocks. -/
theorem cntFrom_ndTest (pass : Dg lam → Bool) (l : Bool) (st : ℕ → Bool) (bl : ℕ → Dg lam)
    (K : ℕ) (acc : ℕ → Dg lam) :
    cntFrom (ndTest pass l st) bl (K + 1) 0 acc =
      1 + if (pass (bl 0) || l) = true then cntSt st K 1 else 0 := by
  show 1 + cntFrom (ndTest pass l st) bl K 1 (Function.update acc 0 (bl 0)) = _
  rw [cntFrom_tail pass l st bl K 1 _ le_rfl, Function.update_self]

/-- A failed attempt that is not the last costs exactly one. -/
theorem cntFrom_ndTest_fail (pass : Dg lam → Bool) (st : ℕ → Bool) (bl : ℕ → Dg lam) (K : ℕ)
    (acc : ℕ → Dg lam) (h : pass (bl 0) = false) :
    cntFrom (ndTest pass false st) bl (K + 1) 0 acc = 1 := by
  rw [cntFrom_ndTest, h]
  rfl

/-- An attempt that passes, or the last, costs one and the marked hash blocks. -/
theorem cntFrom_ndTest_keep (pass : Dg lam → Bool) (l : Bool) (st : ℕ → Bool) (bl : ℕ → Dg lam)
    (K : ℕ) (acc : ℕ → Dg lam) (h : (pass (bl 0) || l) = true) :
    cntFrom (ndTest pass l st) bl (K + 1) 0 acc = 1 + cntSt st K 1 := by
  rw [cntFrom_ndTest, if_pos h]

theorem maskFrom_tail (pass : Dg lam → Bool) (l : Bool) (st : ℕ → Bool) (bl : ℕ → Dg lam) :
    ∀ (K j : ℕ) (acc : ℕ → Dg lam) (i : ℕ), 1 ≤ j →
      maskFrom (ndTest pass l st) bl K j acc i =
        if j ≤ i ∧ i < j + K ∧ ((pass (acc 0) || l) && st i) = true then bl i else acc i
  | 0, j, acc, i, _ => by
    rw [if_neg (by omega)]
    rfl
  | K + 1, j, acc, i, hj => by
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    unfold maskFrom
    rw [ndTest_succ]
    cases hd : ((pass (acc 0) || l) && st (j + 1)) with
    | false =>
      show maskFrom (ndTest pass l st) bl K (j + 1 + 1) acc i = _
      rw [maskFrom_tail pass l st bl K (j + 1 + 1) acc i (by omega)]
      by_cases hc : j + 1 + 1 ≤ i ∧ i < j + 1 + 1 + K ∧ ((pass (acc 0) || l) && st i) = true
      · rw [if_pos hc, if_pos ⟨by omega, by omega, hc.2.2⟩]
      · rw [if_neg hc, if_neg fun h => hc ⟨by
          rcases Nat.lt_or_ge (j + 1) i with h' | h'
          · omega
          · have e : i = j + 1 := by omega
            subst e
            rw [hd] at h
            exact absurd h.2.2 (by decide), by omega, h.2.2⟩]
    | true =>
      show maskFrom (ndTest pass l st) bl K (j + 1 + 1)
          (Function.update acc (j + 1) (bl (j + 1))) i = _
      rw [maskFrom_tail pass l st bl K (j + 1 + 1) _ i (by omega),
        Function.update_of_ne (show (0 : ℕ) ≠ j + 1 by omega)]
      by_cases hi : i = j + 1
      · subst hi
        rw [if_neg (by omega), Function.update_self, if_pos ⟨le_rfl, by omega, hd⟩]
      · rw [Function.update_of_ne hi]
        by_cases hc : j + 1 + 1 ≤ i ∧ i < j + 1 + 1 + K ∧ ((pass (acc 0) || l) && st i) = true
        · rw [if_pos hc, if_pos ⟨by omega, by omega, hc.2.2⟩]
        · rw [if_neg hc, if_neg fun h => hc ⟨by omega, by omega, h.2.2⟩]

/-- The sequence as the rule shows it: hash block 0 as it is; a later one as it is if (hash block 0
passes or l) and it is marked; else what acc has. -/
theorem maskFrom_ndTest (pass : Dg lam → Bool) (l : Bool) (st : ℕ → Bool) (bl : ℕ → Dg lam) (K : ℕ)
    (acc : ℕ → Dg lam) (i : ℕ) :
    maskFrom (ndTest pass l st) bl (K + 1) 0 acc i =
      if i = 0 then bl 0
      else if i < K + 1 ∧ ((pass (bl 0) || l) && st i) = true then bl i
      else acc i := by
  show maskFrom (ndTest pass l st) bl K 1 (Function.update acc 0 (bl 0)) i = _
  rw [maskFrom_tail pass l st bl K 1 _ i le_rfl, Function.update_self]
  by_cases hi : i = 0
  · subst hi
    rw [if_neg (by omega), if_pos rfl, Function.update_self]
  · rw [if_neg hi, Function.update_of_ne hi]
    by_cases hc : i < K + 1 ∧ ((pass (bl 0) || l) && st i) = true
    · rw [if_pos hc, if_pos ⟨by omega, by omega, hc.2⟩]
    · rw [if_neg hc, if_neg fun h => hc ⟨by omega, h.2.2⟩]

/-! ## 3. At a query to a typed oracle -/

theorem maskFrom_ndTest' (pass : Dg lam → Bool) (l : Bool) (st : ℕ → Bool) (bl : ℕ → Dg lam) {n : ℕ}
    (hn : 0 < n) (acc : ℕ → Dg lam) (i : ℕ) :
    maskFrom (ndTest pass l st) bl n 0 acc i =
      if i = 0 then bl 0
      else if i < n ∧ ((pass (bl 0) || l) && st i) = true then bl i
      else acc i := by
  obtain ⟨K, rfl⟩ : ∃ K, n = K + 1 := ⟨n - 1, by omega⟩
  exact maskFrom_ndTest pass l st bl K acc i

theorem cntFrom_ndTest' (pass : Dg lam → Bool) (l : Bool) (st : ℕ → Bool) (bl : ℕ → Dg lam) {n : ℕ}
    (hn : 0 < n) (acc : ℕ → Dg lam) :
    cntFrom (ndTest pass l st) bl n 0 acc =
      1 + if (pass (bl 0) || l) = true then cntSt st (n - 1) 1 else 0 := by
  obtain ⟨K, rfl⟩ : ∃ K, n = K + 1 := ⟨n - 1, by omega⟩
  exact cntFrom_ndTest pass l st bl K acc

variable {S : OSpec} {α : Type} (m : OracleCoding S lam) {need : NeedA S lam} {o : S.ι} {q : S.Dom o}
  {pass : Dg lam → Bool} {l : Bool} {st : ℕ → Bool}

/-- hash block 0 of the answer of a typed oracle -/
def block0 (o : S.ι) (r : S.Rng o) : Dg lam := extBl (m.rng o r) 0

/-- At an oracle with at least one hash block (hn), the rule `ndTest` (hq) shows hash block 0 as it
is. -/
theorem block0_shownA (hn : 0 < m.blocks o) (hq : need o q = ndTest pass l st) (r : S.Rng o) :
    block0 m o (shownA m need o q r) = block0 m o r := by
  unfold block0 shownA extBl
  rw [dif_pos hn, dif_pos hn, Equiv.apply_symm_apply, hq,
    maskFrom_ndTest' pass l st _ hn, if_pos rfl, dif_pos hn]

/-- At an oracle with at least one hash block (hn), under the rule `ndTest` (hq), an attempt that
passes, or the last, is shown whole, if all hash blocks are marked. -/
theorem shownA_kept (hn : 0 < m.blocks o) (hq : need o q = ndTest pass l fun _ => true)
    (r : S.Rng o) (hp : (pass (block0 m o r) || l) = true) : shownA m need o q r = r := by
  unfold shownA
  rw [Equiv.symm_apply_eq]
  funext j
  rw [hq, maskFrom_ndTest' pass l _ _ hn]
  have hp' : (pass (extBl (m.rng o r) 0) || l) = true := hp
  have ej : extBl (m.rng o r) j = m.rng o r j := by
    unfold extBl
    rw [dif_pos j.isLt]
  by_cases h0 : (j : ℕ) = 0
  · rw [if_pos h0, ← ej, h0]
  · rw [if_neg h0, if_pos ⟨j.isLt, by rw [hp']; rfl⟩, ej]

/-- At an oracle with at least one hash block (hn), under the rule `ndTest` (hq), a failed attempt
that is not the last costs exactly one query to f. -/
theorem numA_fail (hn : 0 < m.blocks o) (hq : need o q = ndTest pass false st)
    (r : S.Rng o) (hp : pass (block0 m o r) = false) : numA m need o q r = 1 := by
  unfold numA
  have hp' : pass (extBl (m.rng o r) 0) = false := hp
  rw [hq, cntFrom_ndTest' pass false st _ hn, hp']
  rfl

/-- At an oracle with at least one hash block (hn), under the rule `ndTest` (hq), no attempt costs
more than the hash blocks of its oracle. -/
theorem numA_le (hn : 0 < m.blocks o) (hq : need o q = ndTest pass l st) (r : S.Rng o) :
    numA m need o q r ≤ m.blocks o := by
  unfold numA
  rw [hq, cntFrom_ndTest' pass l st _ hn]
  have := cntSt_le st (m.blocks o - 1) 1
  split_ifs <;> omega

end Rom
