-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/NeedA.lean: adaptive rules for which hash blocks of an oracle's answer are queried.

When typed random oracles (one oracle for each kind of query, with structured inputs and outputs)
are implemented by one hash function with `lam` output bits, an answer is a sequence of hash blocks
of `lam` bits, and each costs one hash query. Rom/OverOneN.lean selects the hash blocks to query by
a function of the query only. Here the decision on hash block j may also depend on those obtained
before it. No oracle algorithm occurs in this file.

  `NeedA S lam`   A rule: `need o q j acc` says whether hash block j of the answer of oracle o at
                  query q is queried. The files that apply a rule give it as `acc` the hash blocks
                  obtained so far, with the all-zero block `dig0` (Rom/OverOneN.lean) at every other
                  index.
  `maskFrom`      A rule applied to a given sequence of hash blocks at the K indices from j on. It
                  depends on the sequence only at these indices (`maskFrom_congr`); under the rule
                  that always says yes it copies them (`maskFrom_all`).
  `NeedA.Below`   The rule queries no hash block from a given index on.

Rom/SpecOverOneA.lean, Rom/StateFirst.lean and Rom/StateFirstLazy.lean import this file.

Limits: nothing is stated about any algorithm, or about any replacement of one family of oracles by
another.
-/
import Rom.OverOneN

set_option autoImplicit false

namespace Rom

/-- A hash block. -/
abbrev Dg (lam : ℕ) : Type := Fin lam → Bool

/-- A rule that says which hash blocks are queried. -/
abbrev NeedA (S : OSpec) (lam : ℕ) : Type := (o : S.ι) → S.Dom o → ℕ → (ℕ → Dg lam) → Bool

variable {S : OSpec} {lam : ℕ}

/-- A rule applied to a given sequence of hash blocks; no oracle is queried.
`maskFrom nd bl K j acc` goes through the K indices from j on and returns acc with `bl i` written at
each index i at which the rule nd says yes, given acc as written so far. -/
def maskFrom (nd : ℕ → (ℕ → Dg lam) → Bool) (bl : ℕ → Dg lam) :
    (K j : ℕ) → (ℕ → Dg lam) → ℕ → Dg lam
  | 0, _, acc => acc
  | K + 1, j, acc =>
      match nd j acc with
      | true => maskFrom nd bl K (j + 1) (Function.update acc j (bl j))
      | false => maskFrom nd bl K (j + 1) acc

theorem maskFrom_congr (nd : ℕ → (ℕ → Dg lam) → Bool) {bl bl' : ℕ → Dg lam} :
    ∀ (K j : ℕ) (acc : ℕ → Dg lam),
      (∀ i, j ≤ i → i < j + K → bl i = bl' i) → maskFrom nd bl K j acc = maskFrom nd bl' K j acc
  | 0, _, _, _ => rfl
  | K + 1, j, acc, h => by
    unfold maskFrom
    cases nd j acc with
    | true =>
      show maskFrom nd bl K (j + 1) (Function.update acc j (bl j)) =
        maskFrom nd bl' K (j + 1) (Function.update acc j (bl' j))
      rw [h j le_rfl (by omega)]
      exact maskFrom_congr nd K (j + 1) _ fun i h1 h2 => h i (by omega) (by omega)
    | false => exact maskFrom_congr nd K (j + 1) _ fun i h1 h2 => h i (by omega) (by omega)

/-- No hash block yet: the all-zero sequence. -/
def acc0 (lam : ℕ) : ℕ → Dg lam := fun _ => dig0 lam

/-- K hash blocks, continued by the all-zero block. -/
def extBl {K : ℕ} (bl : Fin K → Dg lam) : ℕ → Dg lam := fun i =>
  if h : i < K then bl ⟨i, h⟩ else dig0 lam

theorem maskFrom_all (bl : ℕ → Dg lam) :
    ∀ (K j : ℕ) (acc : ℕ → Dg lam) (i : ℕ),
      maskFrom (fun _ _ => true) bl K j acc i = if j ≤ i ∧ i < j + K then bl i else acc i
  | 0, j, acc, i => by
    rw [if_neg (by omega)]
    rfl
  | K + 1, j, acc, i => by
    show maskFrom (fun _ _ => true) bl K (j + 1) (Function.update acc j (bl j)) i = _
    rw [maskFrom_all bl K (j + 1)]
    by_cases h : i = j
    · subst h
      rw [if_neg (by omega), if_pos (by omega), Function.update_self]
    · rw [Function.update_of_ne h]
      by_cases h2 : j + 1 ≤ i ∧ i < j + 1 + K
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

/-- The rule queries nothing from the index `nb o q` on. -/
def NeedA.Below (need : NeedA S lam) (nb : (o : S.ι) → S.Dom o → ℕ) : Prop :=
  ∀ o q j acc, nb o q ≤ j → need o q j acc = false

end Rom
