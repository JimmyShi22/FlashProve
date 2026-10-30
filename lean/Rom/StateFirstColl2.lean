-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/StateFirstColl2.lean: the step that expands a long answer of a random oracle from a state
(Rom/StateFirst.lean): an induction over a mixed program that compares its real interpretation with
the reduction's interpretation with a shadow table (`coll_le`; `shadow`, Rom/StateFirstMix.lean).
Its result `mixColl` serves programs in which no raw query follows a typed one (`mixClose_rawFirst`,
Rom/StateFirstKit2.lean); Rom/StateFirstMain.lean repeats the induction for `Spec.mixClose`.

Chain oracles, states, dr: `Link`, `stSpec` (Rom/StateFirst.lean); mixed programs, `real'`,
`MixBound`, the flag of `shadow`: Rom/StateFirstMix.lean; `good`: Rom/StateFirstColl.lean.

Notation:
  `C`: for each oracle o of S, a `Link lam (S.Rng o)` (Rom/StateFirst.lean): how an oracle with
      answers in R is treated (`plain` or `chain K e`)
  mixed program: an `OComp (mixSpec C) α` (Rom/StateFirstMix.lean): typed and raw queries; `.inl o`:
      a typed query, to the first family; `.inr (.inl o)`, `.inr (.inr ())`: raw queries, to the
      second family (the last to dr)
  `real` (Rom/StateFirstMix.lean): the real interpretation: typed queries are expanded (state, then
      expansion queries); raw queries stay
  `real'` (Rom/StateFirstMix.lean): the real interpretation in which a raw query for a state is also
      followed by the expansion queries, whose answers are discarded
  `shadow` (Rom/StateFirstMix.lean): the reduction's interpretation with a shadow: it answers as
      `ideal C false` does, from the table bF; in addition it keeps the table bT of all chain
      answers, and raises the flag when the two tables disagree at a query to dr that is made
  `Sh` (Rom/StateFirstMix.lean): the reduction's table (`bF`), a shadow table in which typed queries
      are entered too (`bT`), and a flag (`fl`)
  `Book` (Rom/StateFirstMix.lean): the reduction's table: the chain answers seen, oldest first
      (`made`), and the answers that it has itself given for dr at other queries (`loose`)
  `MixBound C c t r` (Rom/StateFirstMix.lean): on every path at most t typed queries at chain
      oracles (typed queries at unchanged oracles are free) and r raw queries
  Tp, T (in `Rel C Tp T b`, Rom/StateFirstColl.lean): lazily sampled tables: Tp of the second family
      (`Table (stSpec S lam C)`), T of the first (`Table S`)
-/
import Rom.StateFirstRel
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Rom
open Prob
open scoped ENNReal

variable {S : OSpec} {lam : ℕ} {C : ∀ o, Link lam (S.Rng o)} {α : Type}

/-- the error term n (m + n) / 2^(2 lam) -/
def bnd (lam n m : ℕ) : ℝ≥0∞ := ((n * (m + n) : ℕ) : ℝ≥0∞) * wSt lam

theorem bnd_mono {lam n n' m m' : ℕ} (hn : n ≤ n') (hm : m ≤ m') : bnd lam n m ≤ bnd lam n' m' := by
  unfold bnd
  gcongr

theorem bnd_step (lam n m : ℕ) : bnd lam n (m + 1) + (m : ℝ≥0∞) * wSt lam ≤ bnd lam (n + 1) m := by
  unfold bnd
  rw [← add_mul]
  refine mul_le_mul_left ?_ _
  have : n * (m + 1 + n) + m ≤ (n + 1) * (m + (n + 1)) := by nlinarith
  exact_mod_cast this

theorem pr_not_good_plain {R : Type} [Fintype R] [Nonempty R] (c : Link lam R)
    (hc : c.isPlain = true) (D : (Dg lam × Dg lam) × ℕ → Option (Dg lam)) :
    pr (unif R) {r | ¬ c.good D r} = 0 := by
  have : {r : R | ¬ c.good D r} = ∅ :=
    Set.eq_empty_of_forall_notMem fun r h =>
      h fun σ hs => by rw [isPlain_of_stateOf c hs] at hc; cases hc
  rw [this]
  simp [pr]

/-- One query for an answer of the first family or a state, under `Rel`, hIH: one more term, the
probability that a new state is not `good`. -/
theorem st_step {Tp : Table (stSpec S lam C)} {T : Table S} {b : Book S lam} (hRel : Rel C Tp T b)
    (o : S.ι) (q : S.Dom o) (KR : (C o).Ans → S.Rng o → OComp (stSpec S lam C) α) {γ : Type}
    (KI : S.Rng o → OComp S γ) (E : Set α) (EI : Set (γ × Table S)) (β : ℝ≥0∞)
    (hIH : ∀ r Tp' T', Rel C Tp' T' (b.note C o q r) →
      pr ((KR ((C o).toAns r) r).runLazy Tp') {x | x.1 ∈ E} ≤ pr ((KI r).runLazy T') EI + β) :
    pr ((OComp.query (S := stSpec S lam C) (.inl o) q fun a =>
          (expand C (C o) a).bind (KR a)).runLazy Tp) {x | x.1 ∈ E} ≤
      pr ((OComp.query o q KI).runLazy T) EI + β +
        pr (unif (S.Rng o)) {r | ¬ (C o).good (drVal C b) r} := by
  classical
  cases hT : T o q with
  | some r =>
    have hTp : Tp (.inl o) q = some ((C o).toAns r) := by rw [hRel.st, hT]; rfl
    have e1 : (OComp.query (S := stSpec S lam C) (.inl o) q fun a =>
          (expand C (C o) a).bind (KR a)).runLazy Tp =
        (KR ((C o).toAns r) r).runLazy Tp := by
      simp only [OComp.runLazy, hTp]
      rw [OComp.runLazy_bind,
        expand_old C (C o) r Tp fun σ hs j v hv => by
          rw [hRel.dr]; exact hRel.blk o q r hT σ hs j v hv, PMF.pure_bind]
    have e2 : (OComp.query o q KI).runLazy T = (KI r).runLazy T := by simp only [OComp.runLazy, hT]
    rw [e1, e2]
    refine le_trans (hIH r Tp T ?_) le_self_add
    rw [rel_old hRel hT r]
    exact hRel
  | none =>
    have hTp : Tp (.inl o) q = none := by rw [hRel.st, hT]; rfl
    have e1 : pr ((OComp.query (S := stSpec S lam C) (.inl o) q fun a =>
            (expand C (C o) a).bind (KR a)).runLazy Tp) {x | x.1 ∈ E} =
        expect (unif (C o).Ans) fun a =>
          expect ((expand C (C o) a).runLazy (Tp.set (S := stSpec S lam C) (.inl o) q a))
              fun x => pr ((KR a x.1).runLazy x.2) {x | x.1 ∈ E} := by
      simp only [OComp.runLazy, hTp]
      rw [pr_bind]
      refine expect_congr _ fun a => ?_
      rw [OComp.runLazy_bind, pr_bind]
    have e2 : pr ((OComp.query o q KI).runLazy T) EI =
        expect (unif (S.Rng o)) fun r => pr ((KI r).runLazy (T.set o q r)) EI := by
      simp only [OComp.runLazy, hT]
      rw [pr_bind]
    rw [e1, e2]
    refine le_trans (new_step C (C o) (fun a => Tp.set (S := stSpec S lam C) (.inl o) q a) (drVal C b) (fun a p => by
      show (Tp.set (S := stSpec S lam C) (.inl o) q a) (.inr ()) p = _
      rw [Table.set_ne_oracle (S := stSpec S lam C) Tp
          (show (Sum.inr () : S.ι ⊕ Unit) ≠ Sum.inl o from fun e => by cases e)]
      exact hRel.dr p) (fun a x => pr ((KR a x.1).runLazy x.2) {x | x.1 ∈ E}) fun a x => pr_le_one _ _) ?_
    refine le_trans
      (expect_mono _
        (G := fun r =>
            if (C o).good (drVal C b) r then pr ((KI r).runLazy (T.set o q r)) EI + β else 1)
        fun r => ?_) ?_
    · beta_reduce
      by_cases hg : (C o).good (drVal C b) r
      · rw [if_pos hg, if_pos hg]
        exact hIH r _ _ (rel_new hRel hT r hg)
      · rw [if_neg hg, if_neg hg]
    · refine le_trans (expect_ite_le _ _ _) ?_
      rw [expect_add, expect_const]

theorem pr_sample_le {S₁ S₂ : OSpec} {γ₁ γ₂ : Type} (n : ℕ) (k₁ : Fin (n + 1) → OComp S₁ γ₁)
    (k₂ : Fin (n + 1) → OComp S₂ γ₂) (T₁ : Table S₁) (T₂ : Table S₂) (E₁ : Set (γ₁ × Table S₁))
    (E₂ : Set (γ₂ × Table S₂)) (β : ℝ≥0∞)
    (h : ∀ x, pr ((k₁ x).runLazy T₁) E₁ ≤ pr ((k₂ x).runLazy T₂) E₂ + β) :
    pr ((OComp.sample n k₁).runLazy T₁) E₁ ≤ pr ((OComp.sample n k₂).runLazy T₂) E₂ + β := by
  simp only [OComp.runLazy]
  rw [pr_bind, pr_bind]
  refine le_trans (expect_mono _ h) ?_
  rw [expect_add, expect_const]

/-- a raised flag stays raised -/
theorem shadow_fl (c : OComp (mixSpec C) α) :
    ∀ (s : Sh S lam) (T : Table S),
      s.fl = true → ∀ x ∈ ((shadow C c s).runLazy T).support, x.1.2.fl = true := by
  induction c with
  | pure a =>
    intro s T hs x hx
    simp only [shadow, OComp.runLazy, PMF.support_pure, Set.mem_singleton_iff] at hx
    rw [hx]
    exact hs
  | sample n k ih =>
    intro s T hs x hx
    simp only [shadow, OComp.runLazy, PMF.mem_support_bind_iff] at hx
    obtain ⟨r, -, hr⟩ := hx
    exact ih r s T hs x hr
  | query y q k ih =>
    intro s T hs x hx
    match y, q, k, ih, hx with
    | .inl o, q, k, ih, hx =>
      simp only [shadow, OComp.runLazy] at hx
      cases hT : T o q with
      | some r => rw [hT] at hx; exact ih r { s with bT := s.bT.note C o q r } T hs x hx
      | none =>
        rw [hT] at hx
        obtain ⟨r, -, hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
        exact ih r { s with bT := s.bT.note C o q r } _ hs x hr
    | .inr (.inl o), q, k, ih, hx =>
      simp only [shadow, OComp.runLazy] at hx
      cases hT : T o q with
      | some r => rw [hT] at hx; exact ih _ { s with bT := s.bT.note C o q r, bF := s.bF.note C o q r } T hs x hx
      | none =>
        rw [hT] at hx
        obtain ⟨r, -, hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
        exact ih _ { s with bT := s.bT.note C o q r, bF := s.bF.note C o q r } _ hs x hr
    | .inr (.inr u), p, k, ih, hx =>
      simp only [shadow] at hx
      cases hv : drVal C s.bF p with
      | some v =>
        rw [hv] at hx
        exact ih v _ T (by simp [hs]) x hx
      | none =>
        rw [hv] at hx
        simp only [OComp.runLazy] at hx
        obtain ⟨r, -, hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
        exact ih _ _ T (by simp [hs]) x hr

theorem pr_shadow_fl (c : OComp (mixSpec C) α) (s : Sh S lam) (T : Table S)
    (hs : s.fl = true) (E : Set α) :
    pr ((shadow C c s).runLazy T) {x | x.1.1 ∈ E ∨ x.1.2.fl = true} = 1 :=
  pr_eq_one_of_support_subset _ fun x hx => Or.inr (shadow_fl c s T hs x hx)

/-- From related tables (`Rel`, Rom/StateFirstColl.lean), under `MixBound`: Pr[real' ∈ E] ≤ Pr[the
reduction's interpretation ∈ E, or the flag is raised] + n (m + n) / 2^(2 lam), where n = t + r
bounds the queries still to come that can write into the shadow table, and m its entries. The error
term is for a state that is made now and has an older entry at dr. -/
theorem coll_le (c : OComp (mixSpec C) α) :
    ∀ (t r m : ℕ) (Tp : Table (stSpec S lam C)) (T : Table S) (s : Sh S lam), MixBound C c t r →
      Rel C Tp T s.bT → s.bT.made.length + s.bT.loose.length ≤ m →
      ∀ E : Set α, pr ((real' C c).runLazy Tp) {x | x.1 ∈ E} ≤
        pr ((shadow C c s).runLazy T) {x | x.1.1 ∈ E ∨ x.1.2.fl = true} + bnd lam (t + r) m := by
  induction c with
  | pure a =>
    intro t r m Tp T s _ _ _ E
    simp only [real', shadow, OComp.runLazy]
    rw [pr_pure, pr_pure]
    refine le_trans ?_ le_self_add
    by_cases h : a ∈ E
    · rw [if_pos (show ((a, Tp) : α × Table (stSpec S lam C)) ∈ {x | x.1 ∈ E} from h),
        if_pos (show (((a, s), T) : (α × Sh S lam) × Table S) ∈ {x | x.1.1 ∈ E ∨ x.1.2.fl = true}
            from Or.inl h)]
    · rw [if_neg (show ((a, Tp) : α × Table (stSpec S lam C)) ∉ {x | x.1 ∈ E} from h)]
      exact zero_le _
  | sample n k ih =>
    intro t r m Tp T s hB hRel hm E
    exact pr_sample_le n _ _ Tp T _ _ _ fun x => ih x t r m Tp T s (hB x) hRel hm E
  | query x q k ih =>
    intro t r m Tp T s hB hRel hm E
    match x, q, k, ih, hB with
    | .inl o, q, k, ih, hB =>
      have hB' : if (C o).isPlain = true then
        ∀ x, MixBound C (k x) t r else ∃ t', t = t' + 1 ∧ ∀ x, MixBound C (k x) t' r := hB
      show pr ((OComp.query (S := stSpec S lam C) (.inl o) q fun a =>
            (expand C (C o) a).bind fun r => real' C (k r)).runLazy Tp) {x | x.1 ∈ E} ≤
        pr ((OComp.query o q fun r => shadow C (k r) { s with bT := s.bT.note C o q r }).runLazy T)
            {x | x.1.1 ∈ E ∨ x.1.2.fl = true} + _
      by_cases hp : (C o).isPlain = true
      · rw [if_pos hp] at hB'
        have h1 := st_step hRel o q (fun _ r =>
          real' C (k r)) (fun r =>
              shadow C (k r) { s with bT := s.bT.note C o q r }) E {x | x.1.1 ∈ E ∨
              x.1.2.fl = true} (bnd lam (t + r) m) fun r' Tp' T' hR' =>
          ih r' t r m Tp' T' _ (hB' r') hR' (by show (s.bT.note C o q r').made.length + (s.bT.note C o q r').loose.length ≤ m; rw [note_plain C s.bT o q r' hp]; exact hm) E
        rwa [pr_not_good_plain (C o) hp, add_zero] at h1
      · rw [if_neg hp] at hB'
        obtain ⟨t', rfl, hB''⟩ := hB'
        have h1 := st_step hRel o q (fun _ r =>
          real' C (k r)) (fun r =>
              shadow C (k r) { s with bT := s.bT.note C o q r }) E {x | x.1.1 ∈ E ∨
              x.1.2.fl = true} (bnd lam (t' + r) (m + 1)) fun r' Tp' T' hR' =>
          ih r' t' r (m + 1) Tp' T' _ (hB'' r') hR'
            (le_trans (size_note C s.bT o q r') (Nat.add_le_add_right hm 1)) E
        refine le_trans h1 ?_
        rw [add_assoc]
        refine add_le_add_right
          (le_trans (add_le_add_right
              (pr_not_good (C o) (drVal C s.bT) m (le_trans (cnt_drVal_le C s.bT) hm)) _) ?_) _
        rw [show t' + 1 + r = t' + r + 1 by omega]
        exact bnd_step lam (t' + r) m
    | .inr (.inl o), q, k, ih, hB =>
      cases r with
      | zero => exact absurd hB (by simp [MixBound])
      | succ r' =>
        have hB' : ∀ x, MixBound C (k x) t r' := hB
        show pr ((OComp.query (S := stSpec S lam C) (.inl o) q fun a =>
              (expand C (C o) a).bind fun _ => real' C (k a)).runLazy Tp) {x | x.1 ∈ E} ≤
          pr ((OComp.query o q fun r =>
                shadow C (k ((C o).toAns r))
                  { s with bT := s.bT.note C o q r, bF := s.bF.note C o q r }).runLazy T)
              {x | x.1.1 ∈ E ∨ x.1.2.fl = true} + _
        have h1 := st_step hRel o q (fun a _ =>
          real' C (k a)) (fun r =>
              shadow C (k ((C o).toAns r))
                  { s with bT := s.bT.note C o q r, bF := s.bF.note C o q r }) E {x | x.1.1 ∈ E ∨
              x.1.2.fl = true} (bnd lam (t + r') (m + 1)) fun r'' Tp' T' hR' =>
          ih _ t r' (m + 1) Tp' T' _ (hB' _) hR'
            (le_trans (size_note C s.bT o q r'') (Nat.add_le_add_right hm 1)) E
        refine le_trans h1 ?_
        rw [add_assoc]
        refine add_le_add_right
          (le_trans (add_le_add_right
              (pr_not_good (C o) (drVal C s.bT) m (le_trans (cnt_drVal_le C s.bT) hm)) _) ?_) _
        rw [show t + (r' + 1) = t + r' + 1 by omega]
        exact bnd_step lam (t + r') m
    | .inr (.inr ()), p, k, ih, hB =>
      cases r with
      | zero => exact absurd hB (by simp [MixBound])
      | succ r' =>
        have hB' : ∀ x, MixBound C (k x) t r' := hB
        have hdr : Tp (.inr ()) p = drVal C s.bT p := hRel.dr p
        by_cases hd : drVal C s.bT p = drVal C s.bF p
        · have hfl : (s.fl || s.dis C p) = s.fl := by simp [Sh.dis, hd]
          cases hv : drVal C s.bF p with
          | some v =>
            have e1 : (real' C (OComp.query (S := mixSpec C) (.inr (.inr ())) p k)).runLazy Tp =
                (real' C (k v)).runLazy Tp := by
              rw [hd, hv] at hdr
              simp only [real', OComp.runLazy, hdr]
            have e2 : shadow C (OComp.query (S := mixSpec C) (.inr (.inr ())) p k) s =
                shadow C (k v) s := by
              simp only [shadow, hv]
              rw [hfl]
            rw [e1, e2]
            exact le_trans (ih v t r' m Tp T s (hB' v) hRel hm E)
              (add_le_add_right (bnd_mono (by omega) le_rfl) _)
          | none =>
            have e1 : pr ((real' C (OComp.query (S := mixSpec C) (.inr (.inr ())) p k)).runLazy Tp)
                  {x | x.1 ∈ E} =
                expect (unif (Fin (nDg lam + 1))) fun x =>
                  pr ((real' C (k (digE lam x))).runLazy
                        (Tp.set (S := stSpec S lam C) (.inr ()) p (digE lam x)))
                      {x | x.1 ∈ E} := by
              rw [hd, hv] at hdr
              simp only [real', OComp.runLazy, hdr]
              rw [pr_bind]
              have hu : (PMF.uniformOfFintype (Dg lam)) =
                  (unif (Fin (nDg lam + 1))).map (digE lam) :=
                (map_unif_equiv (digE lam)).symm
              show expect (PMF.uniformOfFintype (Dg lam)) _ = _
              rw [hu, expect_map]
            have e2 : pr
                  ((shadow C (OComp.query (S := mixSpec C) (.inr (.inr ())) p k) s).runLazy T)
                  {x | x.1.1 ∈ E ∨ x.1.2.fl = true} =
                expect (unif (Fin (nDg lam + 1))) fun x =>
                  pr ((shadow C (k (digE lam x))
                        ⟨{ s.bT with loose := (p, digE lam x) :: s.bT.loose },
                          { s.bF with loose := (p, digE lam x) :: s.bF.loose },
                          s.fl⟩).runLazy T)
                      {x | x.1.1 ∈ E ∨ x.1.2.fl = true} := by
              simp only [shadow, hv, OComp.runLazy]
              rw [hfl, pr_bind]
            rw [e1, e2]
            refine le_trans (expect_mono _ fun x => ih (digE lam x) t r' (m + 1) _ T
              ⟨{ s.bT with loose := (p, digE lam x) :: s.bT.loose },
                { s.bF with loose := (p, digE lam x) :: s.bF.loose },
                s.fl⟩
              (hB' _) (rel_loose hRel (hd.trans hv) (digE lam x)) (by
              show s.bT.made.length + (s.bT.loose.length + 1) ≤ m + 1
              omega) E) ?_
            rw [expect_add, expect_const]
            refine add_le_add_right
              (le_trans le_self_add (le_trans (bnd_step lam (t + r') m) (le_of_eq ?_))) _
            rw [show t + (r' + 1) = t + r' + 1 by omega]
        · -- the two tables disagree: the flag is raised
          have hfl : (s.fl || s.dis C p) = true := by simp [Sh.dis, hd]
          have h1 : pr ((shadow C (OComp.query (S := mixSpec C) (.inr (.inr ())) p k) s).runLazy T)
                {x | x.1.1 ∈ E ∨ x.1.2.fl = true} = 1 := by
            cases hv : drVal C s.bF p with
            | some v =>
              have e2 : shadow C (OComp.query (S := mixSpec C) (.inr (.inr ())) p k) s =
                  shadow C (k v) { s with fl := true } := by
                simp only [shadow, hv]
                rw [hfl]
              rw [e2]
              exact pr_shadow_fl _ _ T rfl E
            | none =>
              simp only [shadow, hv, OComp.runLazy]
              rw [hfl, pr_bind,
                expect_congr _ (G := fun _ => 1) fun x => pr_shadow_fl _ _ T rfl E, expect_const]
          rw [h1]
          exact le_trans (pr_le_one _ _) le_self_add

theorem rel_empty : Rel C (Table.empty (stSpec S lam C)) (Table.empty S) ⟨[], []⟩ :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl, fun _ _ _ h => by cases h⟩

/-- `coll_le` from empty tables, stated with `Pr`, for the real interpretation itself. -/
theorem mixColl (c : OComp (mixSpec C) α) (t r : ℕ) (hB : MixBound C c t r) (E : Set α) :
    Pr (real C c) (fun _ => E) ≤
      Pr (shadow C c ⟨⟨[], []⟩, ⟨[], []⟩, false⟩) (fun _ => {x | x.1 ∈ E ∨ x.2.fl = true}) +
        collP lam (t + r) (t + r) := by
  have e0 : Pr (real C c) (fun _ => E) = Pr (real' C c) (fun _ => E) := by
    unfold Pr PrCoins
    simp only [runEager_real']
  rw [e0, Pr_eq_law, Pr_eq_law]
  unfold OComp.law
  rw [pr_map, pr_map]
  refine le_trans (coll_le c t r 0 _ _ ⟨⟨[], []⟩, ⟨[], []⟩, false⟩ hB rel_empty (le_refl _) E)
    (add_le_add_right (le_of_eq ?_) _)
  unfold bnd collP wSt
  rw [Nat.zero_add, div_eq_mul_inv]

end Rom
