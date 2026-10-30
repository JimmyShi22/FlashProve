-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/SkipRun.lean: in mode I, under the hypotheses of `Skip.run`, what is never shown leaves no
trace. The meaning of the relation `Skip` of Rom/Skip.lean, in mode I of Rom/Defer.lean.

`Skip.run`: if c₂ is c₁ without work that is never shown (`Skip Q w c₁ c₂`) and the states d₁, d₂
are related (`StRel w d₁ d₂`, Rom/SkipRel.lean), then the runs of c₁ from d₁ and of c₂ from d₂ in
mode I have a coupling (`Cpl`, Rom/Cpl.lean) under which the results are related by Q and the states
are related again, for some correspondence w'. In particular the two tables stay equal, so anyone
who reads the results and the table sees the same, in this sense: `Skip.Post Q` holds (the results
are related by Q, the tables are equal).

Why: in mode I a marked evaluation is answered by a fresh uniform value and writes nothing (it does
not touch the table); an evaluation charged to a hidden (dead or sealed) token is never released;
and the tail of a fresh uniform answer is a fresh uniform string (`unif_split_snd`), which is what
the second program samples in the rule `markedF`.

`interact_cpl`: from single moves to whole runs of an adversary against two challengers.

Notation:
  `c.run true d`: `Step.run` (Rom/Defer.lean): the run of a step; modeI = true is mode I, false is
      mode R
  marked evaluation, charged: `Step.marked o t us pt inj k` (the head of Rom/Defer.lean): every
      marked evaluation is charged to one token t, in which its point is injective; it may hold
      further tokens us
  tail (the same head): the answer splits into a visible part, which the program gets, and a tail,
      which it gets as a new token
  released: the field `released` of `Ev`, the record of one marked evaluation; `releaseAll`
      (Rom/Defer.lean)
  dead, sealed: the fields `dd`, `sl` of `Wd` (Rom/Skip.lean)
  `World` (Rom/World.lean): the challenger of an experiment, together with the oracles: a state, a
      randomized answer to each oracle query, a randomized reply to each call
  `Adv` (Rom/World.lean): an adversary: it halts with an output, flips coins, queries an oracle, or
      makes a call m and receives an answer

Limits: nothing about mode R, the real experiment: there the left-out work does leave entries in the
table. The step from mode R to mode I is the lemma on deferred programming (`Spec.defer`).
-/
import Rom.SkipRel
import Rom.Cpl

namespace Rom
open Prob

variable {S : OSpec} {sp : Split S}

/-- the tail of a uniform answer is a uniform string -/
theorem unif_split_snd (sp : Split S) (o : S.ι) :
    (PMF.uniformOfFintype (S.Rng o)).map (fun r => (sp.split o r).2) =
      PMF.uniformOfFintype (Fin (sp.tl o) → Bool) := by
  classical
  haveI : Finite (sp.Vis o) :=
    Finite.of_surjective (fun r => (sp.split o r).1) fun v =>
      ⟨(sp.split o).symm (v, fun _ => false), by simp⟩
  haveI : Fintype (sp.Vis o) := Fintype.ofFinite _
  haveI : Nonempty (sp.Vis o) := ⟨(sp.split o (Classical.arbitrary _)).1⟩
  have h1 : (PMF.uniformOfFintype (S.Rng o)).map (sp.split o) =
      PMF.uniformOfFintype (sp.Vis o × (Fin (sp.tl o) → Bool)) :=
    map_unif_equiv (sp.split o)
  have h2 : (PMF.uniformOfFintype (S.Rng o)).map (fun r => (sp.split o r).2) =
      ((PMF.uniformOfFintype (S.Rng o)).map (sp.split o)).map Prod.snd := by
    rw [PMF.map_comp]; rfl
  rw [h2, h1]
  exact (congrArg (fun μ => PMF.map Prod.snd μ) unif_prod).trans (map_snd_prod _ _)

variable {α₁ α₂ : Type}

/-- what holds at the end of two coupled runs -/
def Skip.Post (Q : Wd → α₁ → α₂ → Prop) (x₁ : α₁ × DSt S) (x₂ : α₂ × DSt S) : Prop :=
  ∃ w', Q w' x₁.1 x₂.1 ∧ StRel w' x₁.2 x₂.2

/-- What is never shown leaves no trace: under `Skip Q w c₁ c₂`, from states related by `StRel w`,
the two runs in mode I have a coupling under which `Skip.Post Q` holds. -/
theorem Skip.run {Q : Wd → α₁ → α₂ → Prop} {w : Wd} {c₁ : Step S sp α₁}
    {c₂ : Step S sp α₂} (h : Skip Q w c₁ c₂) :
    ∀ d₁ d₂ : DSt S, StRel w d₁ d₂ → Cpl (Skip.Post Q) (c₁.run true d₁) (c₂.run true d₂) := by
  induction h with
  | pure h => exact fun d₁ d₂ hs => Cpl.pure ⟨_, h, hs⟩
  | sample n _ ih =>
    intro d₁ d₂ hs
    refine Cpl.bind (Cpl.diag _) fun a b hab => ?_
    subst hab
    exact ih a d₁ d₂ hs
  | plain o q _ ih =>
    intro d₁ d₂ hs
    simp only [Step.run]
    rw [← hs.table, ← hs.nPlain]
    refine Cpl.bind (Cpl.diag _) fun a b hab => ?_
    subst hab
    exact ih a.1 _ _ ⟨hs.tok, rfl, hs.evs, rfl, hs.viol⟩
  | fresh ℓ _ ih =>
    intro d₁ d₂ hs
    refine Cpl.bind (Cpl.diag _) fun a b hab => ?_
    subst hab
    exact ih _ _ hs.tok.n₁ hs.tok.n₂ _ _
      ⟨hs.tok.pair _, hs.table, hs.evs.mono (Wd.le_pair _ hs.tok.n₁ hs.tok.n₂), hs.nPlain, hs.viol⟩
  | @marked w o t₁ t₂ us₁ us₂ pt inj k₁ k₂ ht hus _ ih =>
    intro d₁ d₂ hs
    simp only [Step.run, if_true]
    refine Cpl.bind (Cpl.diag _) fun a b hab => ?_
    subst hab
    have hw := Wd.le_pair w hs.tok.n₁ hs.tok.n₂
    have hP : pt (d₁.val t₁) (us₁.map d₁.val) = pt (d₂.val t₂) (us₂.map d₂.val) := by
      have e1 : d₁.val t₁ = d₂.val t₂ := hs.tok.val _ _ ht
      have e2 : us₁.map d₁.val = us₂.map d₂.val := hs.tok.map_val hus
      rw [e1, e2]
    refine ih _ _ _ hs.tok.n₁ hs.tok.n₂ _ _ ⟨hs.tok.pair _, hs.table, ?_, hs.nPlain, ?_⟩
    · have h1 := (hs.evs.mono hw).snoc_both
        (e₁ := ⟨o, pt (d₁.val t₁) (us₁.map d₁.val), a, t₁, us₁, d₁.vals.length, false⟩)
        (c := t₂) (us := us₂) (t := d₂.vals.length) (hw.rel _ _ ht)
          (Skip.forall₂_rel_mono hw hus) (Or.inl (Wd.pair_ρ _ _ _))
      simp only [Ev.ren, hP] at h1
      simp only [hP]
      exact h1
    · intro hv
      rw [Bool.or_eq_false_iff] at hv ⊢
      exact ⟨hs.viol hv.1, markBad_rel hs o ht hus hv.2⟩
  | @markedS w o t₁ t₂ us₁ us₂ pt inj k₁ k₂ ht hus _ ih =>
    intro d₁ d₂ hs
    simp only [Step.run, if_true]
    refine Cpl.bind (Cpl.diag _) fun a b hab => ?_
    subst hab
    have hw := Wd.le_shut w hs.tok.n₁ hs.tok.n₂
    have hP : pt (d₁.val t₁) (us₁.map d₁.val) = pt (d₂.val t₂) (us₂.map d₂.val) := by
      have e1 : d₁.val t₁ = d₂.val t₂ := hs.tok.val _ _ ht
      have e2 : us₁.map d₁.val = us₂.map d₂.val := hs.tok.map_val hus
      rw [e1, e2]
    refine ih _ _ _ hs.tok.n₁ hs.tok.n₂ _ _ ⟨hs.tok.shut _, hs.table, ?_, hs.nPlain, ?_⟩
    · have h1 := (hs.evs.mono hw).snoc_both
        (e₁ := ⟨o, pt (d₁.val t₁) (us₁.map d₁.val), a, t₁, us₁, d₁.vals.length, false⟩)
        (c := t₂) (us := us₂) (t := d₂.vals.length) (hw.rel _ _ ht)
          (Skip.forall₂_rel_mono hw hus) (Or.inr (Wd.shut_sl _ _ _))
      simp only [Ev.ren, hP] at h1
      simp only [hP]
      exact h1
    · intro hv
      rw [Bool.or_eq_false_iff] at hv ⊢
      exact ⟨hs.viol hv.1, markBad_rel hs o ht hus hv.2⟩
  | @reveal w ts₁ ts₂ k₁ k₂ hts _ ih =>
    intro d₁ d₂ hs
    simp only [Step.run]
    have ht' := hs.tok.reveal hts
    have hr := releaseAll_rel ht' hs.evs d₁.table
    have e2 : ts₁.map d₁.val = ts₂.map d₂.val := hs.tok.map_val (Skip.forall₂_rel hts)
    rw [e2]
    refine ih _ _ _ ⟨ht', ?_, ?_, hs.nPlain, ?_⟩
    · rw [← hs.table]; exact hr.1
    · rw [← hs.table]; exact hr.2
    · intro hv
      rw [Bool.or_eq_false_iff, Bool.or_eq_false_iff] at hv ⊢
      refine ⟨⟨hs.viol hv.1.1, ?_⟩, ?_⟩
      · have h1 : closedUnder (d₁.shown ++ ts₁)
              (releaseAll true (d₁.shown ++ ts₁) d₁.evs d₁.table).1 = true := by
          simpa using hv.1.2
        have h2 := closedUnder_rel ht' hr.2 h1
        rw [← hs.table, h2]
        rfl
      · rw [List.any_eq_false]
        intro u hu
        obtain ⟨a, _, hab⟩ := TokRel.mem_right hts hu
        have := (hs.tok.lt _ _ (Or.inl hab)).2
        simp only [decide_eq_true_eq]
        omega
  | sampleL n _ ih => exact fun d₁ d₂ hs => Cpl.bind_left _ fun a => ih a d₁ d₂ hs
  | freshL ℓ _ ih =>
    intro d₁ d₂ hs
    exact Cpl.bind_left _ fun a =>
      ih _ hs.tok.n₁ _ _
        ⟨hs.tok.dead _, hs.table, hs.evs.mono (Wd.le_dead _ hs.tok.n₁), hs.nPlain, hs.viol⟩
  | @markedL w o t₁ us₁ pt inj k₁ c₂ ht _ ih =>
    intro d₁ d₂ hs
    simp only [Step.run, if_true]
    have hw := Wd.le_dead w hs.tok.n₁
    refine Cpl.bind_left _ fun a =>
      ih _ _ hs.tok.n₁ _ _
        ⟨hs.tok.dead _, hs.table, (hs.evs.mono hw).snoc_left (hw.hid _ ht), hs.nPlain, fun hv => ?_⟩
    rw [Bool.or_eq_false_iff] at hv
    exact hs.viol hv.1
  | @markedF w o t₁ us₁ pt inj k₁ k₂ ht _ ih =>
    intro d₁ d₂ hs
    simp only [Step.run, if_true]
    have hw := Wd.le_pair w hs.tok.n₁ hs.tok.n₂
    rw [← unif_split_snd sp o]
    refine Cpl.bind (Cpl.map_right _ _) fun a b hab => ?_
    subst hab
    refine ih _ _ _ hs.tok.n₁ hs.tok.n₂ _ _
      ⟨hs.tok.pair _, hs.table, (hs.evs.mono hw).snoc_left (hw.hid _ ht), hs.nPlain, fun hv => ?_⟩
    rw [Bool.or_eq_false_iff] at hv
    exact hs.viol hv.1

/-! ## From moves to runs -/

variable {Out In α : Type}

/-- Two challengers whose moves can be coupled from related states, with equal answers and related
states, give runs that can be coupled from related states, with equal outputs and related states. -/
theorem interact_cpl (W₁ W₂ : World S Out In) (Rel : W₁.σ → W₂.σ → Prop)
    (hq : ∀ s₁ s₂ o q,
      Rel s₁ s₂ → Cpl (fun x y => x.1 = y.1 ∧ Rel x.2 y.2) (W₁.answer s₁ o q) (W₂.answer s₂ o q))
    (hc : ∀ s₁ s₂ m,
      Rel s₁ s₂ → Cpl (fun x y => x.1 = y.1 ∧ Rel x.2 y.2) (W₁.reply s₁ m) (W₂.reply s₂ m))
    (A : Adv S Out In α) :
    ∀ s₁ s₂, Rel s₁ s₂ →
      Cpl (fun x y => x.1 = y.1 ∧ Rel x.2 y.2) (interact W₁ A s₁) (interact W₂ A s₂) := by
  induction A with
  | halt a => exact fun s₁ s₂ h => Cpl.pure ⟨rfl, h⟩
  | sample n k ih =>
    intro s₁ s₂ h
    refine Cpl.bind (Cpl.diag _) fun a b hab => ?_
    subst hab
    exact ih a s₁ s₂ h
  | query o q k ih =>
    intro s₁ s₂ h
    refine Cpl.bind (hq s₁ s₂ o q h) fun x y hxy => ?_
    rw [hxy.1]
    exact ih _ _ _ hxy.2
  | call m k ih =>
    intro s₁ s₂ h
    refine Cpl.bind (hc s₁ s₂ m h) fun x y hxy => ?_
    rw [hxy.1]
    exact ih _ _ _ hxy.2

end Rom
