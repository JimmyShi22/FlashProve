-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/OverOneA.lean: the step to one hash function under an adaptive rule for which hash blocks are
queried: the proof of `Spec.ofNeedA` of Rom/SpecOverOneA.lean, and lemmas on `maskFrom`
(Rom/NeedA.lean) and on queries.

In the comments, the shown sequence is `maskFrom nd bl K j acc`; the hash function's own sequence is
`fun i => g () (pts i)`; the true answer is `readBlocks m g o q` (Rom/Prefix.lean).

 1. A rule on a sequence: `maskFrom_lt`, `cntFrom_congr`, `walk_idem`.
 2. The run under a fixed hash function: `runEager_askA`, `shown_read`.
 4. Queries: `queryBound_askA_bind`, `CostBoundV.mono`, `CostBoundV.of_costBoundAt`.
 5. Sanity lemmas: `maskFrom_static`, `cntFrom_static` (a rule that does not look at the hash blocks
    so far), `ofNeedA`.

Notation:
  `NeedA`, `nd`: a rule that says which hash blocks are queried; `nd`, of type
      `ℕ → (ℕ → Dg lam) → Bool`, is a rule at one query (Rom/NeedA.lean)
  `Dg lam`: a hash block; `bl`, `acc`: sequences of hash blocks, of type `ℕ → Dg lam`; acc: the hash
      blocks so far (Rom/SpecOverOneA.lean, `askA`)
  `maskFrom nd bl K j acc`: a rule applied to a given sequence of hash blocks; no oracle is queried
      (Rom/NeedA.lean); K indices from j on
  `cntFrom`: how many hash blocks a rule queries on a given sequence: the recursion of maskFrom,
      counted (Rom/SpecOverOneA.lean)
  `acc0`: no hash block yet: the all-zero sequence; `extBl`: K hash blocks, continued by the
      all-zero block (Rom/NeedA.lean)
  `strsOf`: the strings of the hash blocks of the answer at (o, q) (Rom/SpecOverOneA.lean); `pts`:
      of type `ℕ → List Bool`
  `CostBoundV` (Rom/SpecOverOneA.lean): on every path the weights of the queries add up to at most
      t, where the weight of a query may depend on its answer
  `shownA`, `askA`: Rom/SpecOverOneA.lean
  f (in "4. Queries to f"): one hash function f (the head of Rom/SpecOverOneA.lean); in the
      statements of 2 `g : Fam (rom lam)`

Limits: what the head of Rom/SpecOverOneA.lean lists as not said is not said here either.
-/
import Rom.SpecOverOneA

set_option autoImplicit false

namespace Rom
open ZKCP
open scoped ENNReal

variable {S : OSpec} {lam : ℕ} {α β : Type}

/-! ## 1. A rule on a sequence -/

/-- `maskFrom` leaves the indices before its start unchanged. -/
theorem maskFrom_lt (nd : ℕ → (ℕ → Dg lam) → Bool) (bl : ℕ → Dg lam) :
    ∀ (K j : ℕ) (acc : ℕ → Dg lam) (i : ℕ), i < j → maskFrom nd bl K j acc i = acc i
  | 0, _, _, _, _ => rfl
  | K + 1, j, acc, i, h => by
    unfold maskFrom
    cases nd j acc with
    | true =>
      show maskFrom nd bl K (j + 1) (Function.update acc j (bl j)) i = acc i
      rw [maskFrom_lt nd bl K (j + 1) _ i (by omega), Function.update_of_ne (by omega)]
    | false => exact maskFrom_lt nd bl K (j + 1) acc i (by omega)

theorem cntFrom_congr (nd : ℕ → (ℕ → Dg lam) → Bool) {bl bl' : ℕ → Dg lam} :
    ∀ (K j : ℕ) (acc : ℕ → Dg lam),
      (∀ i, j ≤ i → i < j + K → bl i = bl' i) → cntFrom nd bl K j acc = cntFrom nd bl' K j acc
  | 0, _, _, _ => rfl
  | K + 1, j, acc, h => by
    unfold cntFrom
    cases nd j acc with
    | true =>
      show 1 + cntFrom nd bl K (j + 1) (Function.update acc j (bl j)) =
        1 + cntFrom nd bl' K (j + 1) (Function.update acc j (bl' j))
      rw [h j le_rfl (by omega),
        cntFrom_congr nd K (j + 1) _ fun i h1 h2 => h i (by omega) (by omega)]
    | false => exact cntFrom_congr nd K (j + 1) acc fun i h1 h2 => h i (by omega) (by omega)

/-- On a sequence bl' that equals the shown sequence at the indices j to j + K − 1, the rule gives
the same result (`maskFrom`) and the same count (`cntFrom`) as on bl. -/
theorem walk_idem (nd : ℕ → (ℕ → Dg lam) → Bool) (bl : ℕ → Dg lam) :
    ∀ (K j : ℕ) (acc bl' : ℕ → Dg lam),
      (∀ i, j ≤ i → i < j + K → bl' i = maskFrom nd bl K j acc i) →
      maskFrom nd bl' K j acc = maskFrom nd bl K j acc ∧
      cntFrom nd bl' K j acc = cntFrom nd bl K j acc
  | 0, _, _, _, _ => ⟨rfl, rfl⟩
  | K + 1, j, acc, bl', h => by
    have hj := h j le_rfl (by omega)
    unfold maskFrom cntFrom at *
    cases hn : nd j acc with
    | true =>
      rw [hn] at h hj
      have e : bl' j = bl j := by
        refine hj.trans ?_
        show maskFrom nd bl K (j + 1) (Function.update acc j (bl j)) j = bl j
        rw [maskFrom_lt nd bl K (j + 1) _ j (by omega), Function.update_self]
      have ih := walk_idem nd bl K (j + 1) (Function.update acc j (bl j)) bl'
        fun i h1 h2 => h i (by omega) (by omega)
      show maskFrom nd bl' K (j + 1) (Function.update acc j (bl' j)) =
          maskFrom nd bl K (j + 1) (Function.update acc j (bl j)) ∧
        1 + cntFrom nd bl' K (j + 1) (Function.update acc j (bl' j)) =
          1 + cntFrom nd bl K (j + 1) (Function.update acc j (bl j))
      rw [e]
      exact ⟨ih.1, congrArg (1 + ·) ih.2⟩
    | false =>
      rw [hn] at h
      exact walk_idem nd bl K (j + 1) acc bl' fun i h1 h2 => h i (by omega) (by omega)

/-! ## 2. The run under a fixed hash function -/

/-- What askA returns: the rule applied to the hash function's own sequence. -/
theorem runEager_askA (g : Fam (rom lam)) (nd : ℕ → (ℕ → Dg lam) → Bool) (pts : ℕ → List Bool) :
    ∀ (K j : ℕ) (acc : ℕ → Dg lam),
      (askA lam nd pts K j acc).runEager g = PMF.pure (maskFrom nd (fun i => g () (pts i)) K j acc)
  | 0, _, _ => rfl
  | K + 1, j, acc => by
    unfold askA maskFrom
    cases nd j acc with
    | true => exact runEager_askA g nd pts K (j + 1) _
    | false => exact runEager_askA g nd pts K (j + 1) acc

/-- the sequence of the true answer is the hash function's own sequence, as far as the answer has
hash blocks -/
theorem extBl_read (m : OracleCoding S lam) (g : Fam (rom lam)) (o : S.ι) (q : S.Dom o)
    (i : ℕ) (h : i < m.blocks o) :
    g () (strsOf m o q i) = extBl (m.rng o (readBlocks m g o q)) i := by
  unfold strsOf extBl readBlocks
  rw [dif_pos h, dif_pos h, Equiv.apply_symm_apply]
  rfl

/-- The hash blocks that `overOneA` joins at (o, q) are the true answer as the rule shows it. -/
theorem shown_read (m : OracleCoding S lam) (need : NeedA S lam) (g : Fam (rom lam))
    (o : S.ι) (q : S.Dom o) :
    ((m.rng o).symm fun j : Fin (m.blocks o) =>
        maskFrom (need o q) (fun i => g () (strsOf m o q i)) (m.blocks o) 0 (acc0 lam) j) =
      shownA m need o q (readBlocks m g o q) := by
  unfold shownA
  rw [maskFrom_congr (need o q) (m.blocks o) 0 (acc0 lam) fun i _ h =>
      extBl_read m g o q i (by omega)]

/-! ## 4. Queries to f -/

theorem OComp.CostBoundV.mono {w : (o : S.ι) → S.Dom o → S.Rng o → ℕ} :
    ∀ {c : OComp S α} {s t : ℕ}, c.CostBoundV w s → s ≤ t → c.CostBoundV w t
  | .pure _, _, _, _, _ => trivial
  | .sample _ k, _, _, h, hst => fun r => OComp.CostBoundV.mono (c := k r) (h r) hst
  | .query _ _ _, _, _, h, hst => fun r => let ⟨t', h1, h2⟩ := h r; ⟨t', h1.trans hst, h2⟩

/-- A bound for a weight that does not depend on the answer (`CostBoundAt`) gives `CostBoundV`. -/
theorem OComp.CostBoundV.of_costBoundAt {w : (o : S.ι) → S.Dom o → ℕ} :
    ∀ {c : OComp S α} {t : ℕ}, c.CostBoundAt w t → c.CostBoundV (fun o q _ => w o q) t
  | .pure _, _, _ => trivial
  | .sample _ k, _, h => fun r => OComp.CostBoundV.of_costBoundAt (c := k r) (h r)
  | .query _ _ k, _, h =>
    fun r => let ⟨t', h1, h2⟩ := h; ⟨t', h1.ge, OComp.CostBoundV.of_costBoundAt (c := k r) (h2 r)⟩

/-- `askA` followed by any program F: if for every sequence bl the hash blocks queried on it
(`cntFrom`) and a bound on the program at the sequence as shown (`F (maskFrom nd bl K j acc)`) add
up to at most t, there are at most t queries (`QueryBound`). -/
theorem queryBound_askA_bind
    (nd : ℕ → (ℕ → Dg lam) → Bool) (pts : ℕ → List Bool) (F : (ℕ → Dg lam) → OComp (rom lam) β) :
    ∀ (K j : ℕ) (acc : ℕ → Dg lam) (t : ℕ),
      (∀ bl, ∃ t', cntFrom nd bl K j acc + t' ≤ t ∧ (F (maskFrom nd bl K j acc)).QueryBound t') →
      ((askA lam nd pts K j acc).bind F).QueryBound t
  | 0, j, acc, t, h => by
    obtain ⟨t', h1, h2⟩ := h acc
    have h1' : 0 + t' ≤ t := h1
    exact OComp.QueryBound.mono h2 (by omega)
  | K + 1, j, acc, t, h => by
    unfold askA
    unfold cntFrom maskFrom at h
    cases hn : nd j acc with
    | false =>
      rw [hn] at h
      exact queryBound_askA_bind nd pts F K (j + 1) acc t h
    | true =>
      rw [hn] at h
      obtain ⟨t0, h0, -⟩ := h acc
      obtain ⟨t, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by
        have : 1 + cntFrom nd acc K (j + 1) (Function.update acc j (acc j)) + t0 ≤ t := h0
        omega⟩
      show ∀ r, ((askA lam nd pts K (j + 1) (Function.update acc j r)).bind F).QueryBound t
      intro r
      refine queryBound_askA_bind nd pts F K (j + 1) _ t fun bl => ?_
      obtain ⟨t', h1, h2⟩ := h (Function.update bl j r)
      have e1 : Function.update bl j r j = r := Function.update_self j r bl
      have c1 : cntFrom nd (Function.update bl j r) K (j + 1) (Function.update acc j r) =
          cntFrom nd bl K (j + 1) (Function.update acc j r) :=
        cntFrom_congr nd K (j + 1) _ fun i hi _ => Function.update_of_ne (by omega) _ _
      have c2 : maskFrom nd (Function.update bl j r) K (j + 1) (Function.update acc j r) =
          maskFrom nd bl K (j + 1) (Function.update acc j r) :=
        maskFrom_congr nd K (j + 1) _ fun i hi _ => Function.update_of_ne (by omega) _ _
      have h1' : 1 +
            cntFrom nd (Function.update bl j r) K (j + 1)
              (Function.update acc j (Function.update bl j r j)) + t' ≤ t + 1 := h1
      have h2' : (F
          (maskFrom nd (Function.update bl j r) K (j + 1)
            (Function.update acc j (Function.update bl j r j)))).QueryBound t' := h2
      rw [e1, c1] at h1'
      rw [e1, c2] at h2'
      exact ⟨t', by omega, h2'⟩

/-! ## 5. Sanity lemmas: a rule that does not look at the hash blocks so far -/

theorem maskFrom_static (s : ℕ → Bool) (bl : ℕ → Dg lam) :
    ∀ (K j : ℕ) (acc : ℕ → Dg lam) (i : ℕ), maskFrom (fun j _ => s j) bl K j acc i =
      if j ≤ i ∧ i < j + K ∧ s i = true then bl i else acc i
  | 0, j, acc, i => by
    rw [if_neg (by omega)]
    rfl
  | K + 1, j, acc, i => by
    unfold maskFrom
    cases hs : s j with
    | true =>
      show maskFrom (fun j _ => s j) bl K (j + 1) (Function.update acc j (bl j)) i = _
      rw [maskFrom_static s bl K (j + 1)]
      by_cases hi : i = j
      · subst hi
        rw [if_neg (by omega), Function.update_self, if_pos ⟨le_rfl, by omega, hs⟩]
      · rw [Function.update_of_ne hi]
        by_cases hc : j + 1 ≤ i ∧ i < j + 1 + K ∧ s i = true
        · rw [if_pos hc, if_pos ⟨by omega, by omega, hc.2.2⟩]
        · rw [if_neg hc, if_neg fun h => hc ⟨by omega, by omega, h.2.2⟩]
    | false =>
      show maskFrom (fun j _ => s j) bl K (j + 1) acc i = _
      rw [maskFrom_static s bl K (j + 1)]
      by_cases hc : j + 1 ≤ i ∧ i < j + 1 + K ∧ s i = true
      · rw [if_pos hc, if_pos ⟨by omega, by omega, hc.2.2⟩]
      · rw [if_neg hc, if_neg fun h => hc ⟨by
          rcases Nat.lt_or_ge j i with h' | h'
          · omega
          · have : i = j := by omega
            subst this
            rw [hs] at h
            exact absurd h.2.2 (by decide), by omega, h.2.2⟩]

theorem cntFrom_static (bl : ℕ → Dg lam) :
    ∀ (n : ℕ) (nd : Fin n → Bool) (j : ℕ) (s : ℕ → Bool) (acc : ℕ → Dg lam),
      (∀ i : Fin n, s (j + i) = nd i) → cntFrom (fun j _ => s j) bl n j acc = cnt n nd
  | 0, _, _, _, _, _ => rfl
  | n + 1, nd, j, s, acc, h => by
    have h0 : s j = nd 0 := h 0
    have ih := fun acc => cntFrom_static bl n (fun i => nd i.succ) (j + 1) s acc fun i => by
      have := h i.succ
      rwa [show j + ((i.succ : Fin (n + 1)) : ℕ) = j + 1 + (i : ℕ) by simp; omega] at this
    unfold cntFrom cnt
    rw [← h0]
    cases s j with
    | true =>
      show 1 + cntFrom (fun j _ => s j) bl n (j + 1) _ = _
      rw [ih]
      rfl
    | false =>
      show cntFrom (fun j _ => s j) bl n (j + 1) acc = _
      rw [ih]
      simp

theorem ofNeedA : Spec.ofNeedA := by
  intro S lam m need
  have row : ∀ (o : S.ι) (q : S.Dom o) (bl : ℕ → Dg lam) (j : Fin (m.blocks o)),
      maskFrom (NeedA.ofNeed need o q) bl (m.blocks o) 0 (acc0 lam) j =
        if need o q j = true then bl j else dig0 lam := by
    intro o q bl j
    have := maskFrom_static (fun i => if h : i < m.blocks o then need o q ⟨i, h⟩ else false) bl
      (m.blocks o) 0 (acc0 lam) j
    refine this.trans ?_
    have e : (if h : (j : ℕ) < m.blocks o then need o q ⟨j, h⟩ else false) = need o q j :=
      dif_pos j.isLt
    rw [e]
    by_cases hn : need o q j = true
    · rw [if_pos ⟨Nat.zero_le _, by have := j.isLt; omega, hn⟩, if_pos hn]
    · rw [if_neg fun h => hn h.2.2, if_neg hn]
      rfl
  refine ⟨fun α g c => ?_, fun o q r j hj => ?_, fun o q r => ?_⟩
  · induction c with
    | pure a => rfl
    | sample n k ih =>
      simp only [OComp.overOneA, OComp.overOneN, OComp.runEager]
      congr 1; funext r; exact ih r
    | query o q k ih =>
      simp only [OComp.overOneA, OComp.overOneN, OComp.runEager_bind,
        runEager_askA, runEager_askSome]
      refine (PMF.pure_bind _ _).trans (Eq.trans ?_ (PMF.pure_bind _ _).symm)
      rw [ih]
      congr 3
      refine congrArg (m.rng o).symm (funext fun j => ?_)
      rw [row]
      unfold valSome strsOf
      rw [dif_pos j.isLt]
  · unfold shownA
    rw [Equiv.apply_symm_apply, row, if_pos hj]
    unfold extBl
    rw [dif_pos j.isLt]
  · exact cntFrom_static _ (m.blocks o) (need o q) 0 _ _ fun i => by
      show (if h : 0 + (i : ℕ) < m.blocks o then need o q ⟨0 + i, h⟩ else false) = need o q i
      rw [dif_pos (by have := i.isLt; omega)]
      congr 1
      exact Fin.ext (Nat.zero_add _)

end Rom
