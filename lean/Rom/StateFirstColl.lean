-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/StateFirstColl.lean: the step that expands a long answer of a random oracle from a state
(Rom/StateFirst.lean), lemmas for its main lemma (`Spec.mixClose`, Rom/StateFirstMix.lean) and for
`coll_le` (Rom/StateFirstColl2.lean): one query that was made before (`expand_old`), one new query
(`new_step`), and how often a new state is not good (`pr_not_good`: for a uniform answer in a
nonempty R, at most m · 2^-(2 lam), if at most m states have an entry at dr). This error term is for
a state that is made now and has an older entry at dr.

The step leads from a family S of typed oracles, the first family, to the second, `stSpec S lam C`.
There a chain oracle returns only a state: the chaining value and the last block, hid, of its old
answer; the other hash blocks are answers of an added oracle dr to expansion queries (state,
counter). (`Link`, `stSpec`: Rom/StateFirst.lean.)

That `Rel` is preserved along a run: Rom/StateFirstRel.lean. The inductions:
Rom/StateFirstColl2.lean (against the reduction's interpretation with a shadow table),
Rom/StateFirstMain.lean (with a ghost table).

Notation:
  `toAns` (Rom/StateFirstMix.lean): what the second family answers where the first answers r
  `putDr` (Rom/StateFirstDr.lean): the table with hash blocks written at the expansion queries of a
      state
  `drVal` (Rom/StateFirstMix.lean): what a table answers at a query to dr without a coin: its own
      earlier answer; else the hash block of the oldest entered answer with that state that has such
      a hash block
  `runLazy` (Rom/OComp.lean): lazy sampling from a table: an entry is sampled when it is first
      queried
  `Prob.cnt` (Prob/Cnt.lean): the number of elements of a finite type with the property P
  `upd` (in `new_step`): for each answer a of the second family a table, of type
      `c.Ans → Table (stSpec S lam C)`
  Ψ (in `new_step`): a function of an answer a and a pair of an answer and a table, with values in
      `ℝ≥0∞`
-/
import Rom.StateFirstDr
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Rom
open Prob
open scoped ENNReal

variable {S : OSpec} {lam : ℕ} (C : ∀ o, Link lam (S.Rng o)) {α : Type}

/-- The lazily sampled tables Tp (second family), T (first) and a table b of all chain answers (a
`Book`) are consistent. -/
structure Rel (Tp : Table (stSpec S lam C)) (T : Table S) (b : Book S lam) : Prop where
  st : ∀ o q, Tp (.inl o) q = (T o q).map (C o).toAns
  made : ∀ o q, (C o).isPlain = false → findMade b.made o q = T o q
  dr : ∀ p, Tp (.inr ()) p = drVal C b p
  blk : ∀ o q r, T o q = some r →
    ∀ σ, (C o).stateOf r = some σ → ∀ j v, (C o).blockOf r j = some v → drVal C b (σ, j) = some v

namespace Link
variable {R : Type}

/-- the state of a new answer has no entry at dr yet, at the counters below `nK` -/
def good (c : Link lam R) (D : (Dg lam × Dg lam) × ℕ → Option (Dg lam)) (r : R) : Prop :=
  ∀ σ, c.stateOf r = some σ → ∀ j, j < c.nK → D (σ, j) = none

/-- the hash block that the answer r gives at the query p to dr -/
def own (c : Link lam R) (r : R) (p : (Dg lam × Dg lam) × ℕ) : Option (Dg lam) :=
  if c.stateOf r = some p.1 then c.blockOf r p.2 else none

end Link

/-- the table of the second family after a new answer: its hash blocks are written -/
def after {R : Type} : (c : Link lam R) → Table (stSpec S lam C) → R → Table (stSpec S lam C)
  | .plain, Tq, _ => Tq
  | .chain K e, Tq, r => putDr C Tq (e r).2 0 K (e r).1

theorem after_inl {R : Type} (c : Link lam R) (Tq : Table (stSpec S lam C)) (r : R) (o : S.ι) :
    after C c Tq r (.inl o) = Tq (.inl o) := by
  cases c <;> rfl

theorem after_dr {R : Type} (c : Link lam R) (Tq : Table (stSpec S lam C))
    (r : R) (p : (Dg lam × Dg lam) × ℕ) :
    after C c Tq r (.inr ()) p = match c.own r p with
      | some v => some v
      | none => Tq (.inr ()) p := by
  cases c with
  | plain => rfl
  | chain K e =>
    show (if h : p.1 = (e r).2 ∧ 0 ≤ p.2 ∧ p.2 < 0 + K then some ((e r).1 ⟨p.2 - 0, by omega⟩)
        else Tq (.inr ()) p) = _
    have eo : (Link.chain K e).own r p =
      if some (e r).2 = some p.1 then (if h : p.2 < K then some ((e r).1 ⟨p.2, h⟩) else none)
      else none := rfl
    rw [eo]
    by_cases h1 : (e r).2 = p.1
    · by_cases h2 : p.2 < K
      · rw [dif_pos ⟨h1.symm, Nat.zero_le _, by omega⟩, if_pos (congrArg some h1), dif_pos h2]
        rfl
      · rw [dif_neg (by omega), if_pos (congrArg some h1), dif_neg h2]
    · rw [dif_neg (fun h => h1 h.1.symm), if_neg (fun h => h1 (Option.some.inj h))]

/-- A query that was made before, under h: expanding the state of r returns r and leaves the table
unchanged. -/
theorem expand_old {R : Type} (c : Link lam R) (r : R) (Tp : Table (stSpec S lam C))
    (h : ∀ σ, c.stateOf r = some σ → ∀ j v, c.blockOf r j = some v → Tp (.inr ()) (σ, j) = some v) :
    (expand C c (c.toAns r)).runLazy Tp = PMF.pure (r, Tp) := by
  cases c with
  | plain => rfl
  | chain K e =>
    show ((askDr C (e r).2 0 K).bind fun bl => .pure (e.symm (bl, (e r).2))).runLazy Tp = _
    rw [OComp.runLazy_bind, runLazy_askDr_old C (e r).2 K 0 Tp (e r).1 fun j => by
      rw [Nat.zero_add]
      exact h (e r).2 rfl j.val _ (dif_pos j.isLt), PMF.pure_bind]
    show PMF.pure (e.symm ((e r).1, (e r).2), Tp) = _
    rw [Prod.mk.eta, Equiv.symm_apply_apply]

/-- A new query, under hupd (all tables upd a have the entries D at dr), R nonempty: the mean of
Ψ ≤ 1 over a uniform answer of the second family and its expansion is at most the mean over a
uniform r of the first, with 1 where r is not good for D. -/
theorem new_step {R : Type} [Fintype R] [Nonempty R] (c : Link lam R)
    (upd : c.Ans → Table (stSpec S lam C)) (D : (Dg lam × Dg lam) × ℕ → Option (Dg lam))
    (hupd : ∀ a p, upd a (.inr ()) p = D p) (Ψ : c.Ans → R × Table (stSpec S lam C) → ℝ≥0∞)
    (hΨ : ∀ a x, Ψ a x ≤ 1) [DecidablePred (c.good D)] :
    (expect (unif c.Ans) fun a => expect ((expand C c a).runLazy (upd a)) (Ψ a)) ≤
      expect (unif R) fun r =>
        if c.good D r then Ψ (c.toAns r) (r, after C c (upd (c.toAns r)) r) else 1 := by
  cases c with
  | plain =>
    refine le_of_eq (expect_congr _ fun r => ?_)
    have hg : (Link.plain : Link lam R).good D r := fun σ h => by cases h
    rw [if_pos hg]
    exact expect_pure _ _
  | chain K e =>
    have hR : unif R = (unif ((Fin K → Dg lam) × Dg lam × Dg lam)).map e.symm :=
      (map_unif_equiv e.symm).symm
    rw [hR, expect_map, unif_prod, expect_prod, expect_comm]
    refine expect_mono _ fun σ => ?_
    by_cases hg : ∀ j, j < K → D (σ, j) = none
    · have e1 : (expand C (Link.chain K e) σ).runLazy (upd σ) =
          (unif (Fin K → Dg lam)).map fun bl => (e.symm (bl, σ), putDr C (upd σ) σ 0 K bl) := by
        show ((askDr C σ 0 K).bind fun bl => .pure (e.symm (bl, σ))).runLazy (upd σ) = _
        rw [OComp.runLazy_bind,
          runLazy_askDr_new C σ K 0 (upd σ) fun j hj => by rw [Nat.zero_add, hupd]; exact hg j hj,
          PMF.bind_map]
        rfl
      rw [e1, expect_map]
      refine le_of_eq (expect_congr _ fun bl => ?_)
      have hgood : (Link.chain K e).good D (e.symm (bl, σ)) := fun σ' h j hj => by
        have : σ' = σ := by
          have h' : some (e (e.symm (bl, σ))).2 = some σ' := h
          rw [Equiv.apply_symm_apply] at h'
          exact (Option.some.inj h').symm
        subst this
        exact hg j hj
      show _ = if (Link.chain K e).good D (e.symm (bl, σ)) then _ else _
      rw [if_pos hgood]
      show Ψ σ (e.symm (bl, σ), putDr C (upd σ) σ 0 K bl) =
        Ψ (e (e.symm (bl, σ))).2
          (e.symm (bl, σ),
            putDr C (upd (e (e.symm (bl, σ))).2) (e (e.symm (bl, σ))).2 0 K (e (e.symm (bl, σ))).1)
      rw [Equiv.apply_symm_apply]
    · refine le_trans (expect_le_of_forall_le _ fun x _ => hΨ σ x) (le_of_eq ?_)
      have : ∀ bl : Fin K → Dg lam, ¬ (Link.chain K e).good D (e.symm (bl, σ)) := fun bl h => hg fun j hj => h σ (by
        show some (e (e.symm (bl, σ))).2 = some σ
        rw [Equiv.apply_symm_apply]
        rfl) j hj
      rw [expect_congr _ (G := fun _ => 1) fun bl => if_neg (this bl), expect_const]

/-! ## How often a new state is not good -/

/-- the weight of one state, 2^-(2 lam) -/
def wSt (lam : ℕ) : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ (2 * lam))⁻¹

theorem card_state (lam : ℕ) :
    (Fintype.card (Dg lam × Dg lam) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (2 * lam) := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, two_mul, pow_add]
  push_cast
  rfl

theorem pr_not_good {R : Type} [Fintype R] [Nonempty R] (c : Link lam R)
    (D : (Dg lam × Dg lam) × ℕ → Option (Dg lam)) (m : ℕ)
    (hm : Prob.cnt (fun σ : Dg lam × Dg lam => ∃ j, D (σ, j) ≠ none) ≤ m) :
    pr (unif R) {r | ¬ c.good D r} ≤ (m : ℝ≥0∞) * wSt lam := by
  cases c with
  | plain =>
    have : {r : R | ¬ (Link.plain : Link lam R).good D r} = ∅ :=
      Set.eq_empty_of_forall_notMem fun r h => h fun σ hs => by cases hs
    rw [this]
    simp [pr]
  | chain K e =>
    have hR : unif R = (unif ((Fin K → Dg lam) × Dg lam × Dg lam)).map e.symm :=
      (map_unif_equiv e.symm).symm
    rw [hR, pr_map]
    have hsub : (e.symm ⁻¹' {r | ¬ (Link.chain K e).good D r}) ⊆
        {x : (Fin K → Dg lam) × Dg lam × Dg lam | ∃ j, D (x.2, j) ≠ none} := fun x hx => by
      by_contra hn
      simp only [Set.mem_setOf_eq, not_exists, not_not] at hn
      refine hx fun σ hs j _ => ?_
      have h' : some (e (e.symm x)).2 = some σ := hs
      rw [Equiv.apply_symm_apply] at h'
      rw [← Option.some.inj h']
      exact hn j
    refine le_trans (pr_mono _ hsub) ?_
    have h2 : pr (unif ((Fin K → Dg lam) × Dg lam × Dg lam)) {x | ∃ j, D (x.2, j) ≠ none} =
        pr (unif (Dg lam × Dg lam)) {σ | ∃ j, D (σ, j) ≠ none} := by
      rw [unif_prod, ← map_snd_prod (unif (Fin K → Dg lam)) (unif (Dg lam × Dg lam)), pr_map,
        map_snd_prod]
      rfl
    rw [h2]
    refine le_trans (pr_unif_le_of_cnt_le hm) (le_of_eq ?_)
    rw [card_state, div_eq_mul_inv]
    rfl

/-- an average with the bad values replaced by 1: at most the average plus their probability -/
theorem expect_ite_le {γ : Type} (p : PMF γ) (G : γ → Prop) [DecidablePred G] (F : γ → ℝ≥0∞) :
    (expect p fun x => if G x then F x else 1) ≤ expect p F + pr p {x | ¬ G x} := by
  rw [pr_eq_expect, ← expect_add]
  refine expect_mono _ fun x => ?_
  by_cases h : G x
  · rw [if_pos h]
    exact le_self_add
  · rw [if_neg h, if_pos (show x ∈ {x | ¬ G x} from h)]
    exact le_add_self

end Rom
