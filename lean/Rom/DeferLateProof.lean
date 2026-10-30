-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Rom/DeferLateProof.lean: proof of Spec.lateView of Rom/DeferLate.lean.

  late_step is the general form for one step: results of different types, related by post, and,
  under the hypotheses of its statement, any two pay-offs that agree on related results and states
  have the same expectation. The two programs use the same coins in the same order, so the proof is
  an induction on the relation Late; the main work is at a reveal, where the point that the Step
  program computed at the marked evaluation equals the point that the LStep program computes now
  (`forget_postReveal`, from `Ctx.Knows` and `release_forget`).
  `late_interact` carries `late_step` through a whole run, by induction on the adversary, under the
  hypotheses of its statement; `lateView` follows from it at the empty context. (The namespace
  `DeferTail` is that of Rom/DeferProof_tail.lean.)

  Notation:
    `Step`, `DSt`, `Ev`, `Tok` (Rom/Defer.lean); `LStep`, `LSt`, `Late`, `Ctx`, `Ctx.Knows`,
      `lwrite`, `Ev.forget` (Rom/DeferLate.lean)
    `wr`, `Newly`, `rel1`, `markedBad`, `postMarked`, `postReveal`, `withT`, `gv`, `gv_append_left`,
      `interact_ext` (Rom/DeferProof_tail.lean); `noviol_of_safe` (Rom/DeferPublic.lean)
    `F`, `G` in `late_step`: `α × DSt S → ℝ≥0∞`, `β × LSt S → ℝ≥0∞`: the two pay-offs; `Sf`:
      `α × DSt S → Prop`: any property of the outcomes of P that excludes a violation of the rules
      (`hSf`)
-/
import Rom.DeferLate

open scoped ENNReal
open Prob
namespace Rom
namespace DeferTail

variable {S : OSpec} {sp : Split S}

theorem lwrite_eq {pts : Ctx S} {val : Tok → Bits} (T : Table S) (e : Ev S) {pt : Clo S e.o}
    (h1 : pts e.charged e.o = some pt) (h2 : e.pt = pt (val e.charged) (e.others.map val)) :
    lwrite pts val T e.forget = wr T e := by
  unfold lwrite wr Ev.forget
  dsimp only
  rw [h1]
  dsimp only
  rw [← h2]
  cases T e.o e.pt <;> rfl

theorem lrelease_cons_newly (pts : Ctx S) (val : Tok → Bits) {shown : List Tok} {e : Ev S}
    (h : Newly shown e) (es : List (LEv S)) (T : Table S) :
    lrelease pts val shown (e.forget :: es) T =
      ({ e.forget with released := true } ::
          (lrelease pts val shown es (lwrite pts val T e.forget)).1,
        (lrelease pts val shown es (lwrite pts val T e.forget)).2) := by
  rw [lrelease, if_pos (show (!e.forget.released && shown.contains e.forget.charged) = true from
    (cond_iff_newly shown e).2 h)]

theorem lrelease_cons_not (pts : Ctx S) (val : Tok → Bits) {shown : List Tok} {e : Ev S}
    (h : ¬ Newly shown e) (es : List (LEv S)) (T : Table S) :
    lrelease pts val shown (e.forget :: es) T =
      (e.forget :: (lrelease pts val shown es T).1, (lrelease pts val shown es T).2) := by
  rw [lrelease, if_neg (show ¬ (!e.forget.released && shown.contains e.forget.charged) = true from
    fun hc => h ((cond_iff_newly shown e).1 hc))]

/-- If the closures supplied now give the stored points, a release with them does what the release
with the stored points does. -/
theorem release_forget (pts : Ctx S) (val : Tok → Bits) (shown : List Tok) :
    ∀ (evs : List (Ev S)) (T : Table S),
      (∀ e ∈ evs, Newly shown e →
        ∃ pt, pts e.charged e.o = some pt ∧ e.pt = pt (val e.charged) (e.others.map val)) →
      lrelease pts val shown (evs.map Ev.forget) T =
        ((releaseAll true shown evs T).1.map Ev.forget, (releaseAll true shown evs T).2) := by
  intro evs
  induction evs with
  | nil => intro T _; rfl
  | cons e es ih =>
    intro T h
    have hes := fun e' he' => h e' (List.mem_cons_of_mem _ he')
    rw [List.map_cons]
    by_cases hn : Newly shown e
    · obtain ⟨pt, h1, h2⟩ := h e List.mem_cons_self hn
      rw [lrelease_cons_newly pts val hn, releaseAll_cons_newly true hn, lwrite_eq T e h1 h2]
      show _ = (_ :: (releaseAll true shown es (wr T e)).1.map Ev.forget,
          (releaseAll true shown es (wr T e)).2)
      rw [ih (wr T e) hes]
      rfl
    · rw [lrelease_cons_not pts val hn, releaseAll_cons_not true hn, ih T hes]
      rfl

theorem val_append {d : DSt S} {t : Tok} (h : t < d.vals.length) (z : List Bits) :
    (d.vals ++ z).getD t [] = d.val t :=
  gv_append_left h z

/-- new tokens do not disturb what the context knows, if the evaluations and the shown tokens are
the same -/
theorem knows_append {Γ : Ctx S} {d d' : DSt S} (hK : Γ.Knows d) (z : List Bits)
    (hv : d'.vals = d.vals ++ z) (he : d'.evs = d.evs) (hs : d'.shown = d.shown) : Γ.Knows d' := by
  intro e hmem hr
  rw [he] at hmem
  obtain ⟨⟨pt, h1, h2⟩, h3, h4, h5⟩ := hK e hmem hr
  have hval : ∀ t, t < d.vals.length → d'.val t = d.val t := fun t ht => by
    show d'.vals.getD t [] = _
    rw [hv]; exact val_append ht z
  refine ⟨⟨pt, h1, ?_⟩, ?_, ?_, by rw [hs]; exact h5⟩
  · rw [hval _ h3, List.map_congr_left fun x hx => hval x (h4 x hx)]
    exact h2
  · rw [hv, List.length_append]; exact Nat.lt_add_right _ h3
  · intro x hx
    rw [hv, List.length_append]; exact Nat.lt_add_right _ (h4 x hx)

theorem knows_marked {Γ : Ctx S} {d : DSt S} (hK : Γ.Knows d) (o : S.ι) (t : Tok) (us : List Tok)
    (pt : Clo S o) (r : S.Rng o) (T : Table S) (hb : markedBad d o t us = false) :
    (Γ.set t o pt).Knows (postMarked sp d o t us (pt (d.val t) (us.map d.val)) r T) := by
  obtain ⟨ht, hus, _, hsh, hind⟩ := markedBad_false hb
  have hval : ∀ x, x < d.vals.length →
      (postMarked sp d o t us (pt (d.val t) (us.map d.val)) r T).val x = d.val x :=
    fun x hx => val_append hx _
  have hlen : ∀ x, x < d.vals.length →
      x < (postMarked sp d o t us (pt (d.val t) (us.map d.val)) r T).vals.length := fun x hx => by
    show x < (d.vals ++ [_]).length
    rw [List.length_append]; exact Nat.lt_add_right _ hx
  intro e hmem hr
  rcases List.mem_append.1 (show e ∈ d.evs ++ [_] from hmem) with hmem | hmem
  · obtain ⟨⟨pt', h1, h2⟩, h3, h4, h5⟩ := hK e hmem hr
    refine ⟨⟨pt', ?_, ?_⟩, hlen _ h3, fun x hx => hlen x (h4 x hx), h5⟩
    · by_cases hc : e.charged = t
      · have ho : e.o ≠ o := fun ho => (hind e hmem ho).1 hc
        rw [hc, Ctx.set_ne_oracle Γ t ho, ← hc]
        exact h1
      · rw [Ctx.set_ne_tok Γ hc]
        exact h1
    · rw [hval _ h3, List.map_congr_left fun x hx => hval x (h4 x hx)]
      exact h2
  · obtain rfl := List.mem_singleton.1 hmem
    refine ⟨⟨pt, Ctx.set_same Γ t o pt, ?_⟩, hlen _ ht, fun x hx => hlen x (hus x hx), hsh⟩
    show pt (d.val t) (us.map d.val) = pt _ _
    rw [hval _ ht, List.map_congr_left fun x hx => hval x (hus x hx)]

theorem knows_reveal {Γ : Ctx S} {d : DSt S} (hK : Γ.Knows d) (ts : List Tok) :
    Γ.Knows (postReveal true d ts) := by
  intro e' hmem hr
  have hmem' : e' ∈ d.evs.map (rel1 (d.shown ++ ts)) := by
    have : e' ∈ (releaseAll true (d.shown ++ ts) d.evs d.table).1 := hmem
    rwa [releaseAll_fst] at this
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hmem'
  obtain ⟨hn, hr'⟩ := rel1_unreleased hr
  rw [rel1_of_not_newly hn]
  obtain ⟨h1, h3, h4, _⟩ := hK e he hr'
  refine ⟨h1, h3, h4, fun hc => hn ⟨hr', ?_⟩⟩
  have hc' : e.charged ∈ d.shown ++ ts := hc
  simpa using hc'

theorem forget_postReveal {Γ : Ctx S} {d : DSt S} (hK : Γ.Knows d) (ts : List Tok) (pts : Ctx S)
    (hp : ∀ t ∈ ts, ∀ o pt, Γ t o = some pt → pts t o = some pt) :
    (postReveal true d ts).forget =
      { d.forget with
        table := (lrelease pts d.forget.val (d.forget.shown ++ ts) d.forget.evs d.forget.table).2,
        shown := d.forget.shown ++ ts,
        evs := (lrelease pts d.forget.val (d.forget.shown ++ ts)
            d.forget.evs d.forget.table).1 } := by
  have h := release_forget pts d.val (d.shown ++ ts) d.evs d.table fun e he hn => by
    obtain ⟨⟨pt, h1, h2⟩, _, _, h5⟩ := hK e he hn.1
    have hc : e.charged ∈ d.shown ++ ts := by simpa using hn.2
    rcases List.mem_append.1 hc with hc | hc
    · exact absurd hc h5
    · exact ⟨pt, hp _ hc _ _ h1, h2⟩
  have h' : lrelease pts d.forget.val (d.forget.shown ++ ts) d.forget.evs d.forget.table
      = ((releaseAll true (d.shown ++ ts) d.evs d.table).1.map Ev.forget,
          (releaseAll true (d.shown ++ ts) d.evs d.table).2) := h
  rw [h']
  rfl

/-- One step, in general form. Sf is any property of the outcomes of P that excludes a violation of
the rules. -/
theorem late_step {α β : Type} {post : ℕ → Ctx S → α → β → Prop} (Sf : α × DSt S → Prop)
    (hSf : ∀ y, Sf y → y.2.viol = false) (F : α × DSt S → ℝ≥0∞) (G : β × LSt S → ℝ≥0∞)
    (hFG : ∀ n' Γ' a b d', post n' Γ' a b → Γ'.Knows d' → n' ≤ d'.vals.length → Sf (a, d') →
      F (a, d') = G (b, d'.forget))
    {n : ℕ} {Γ : Ctx S} {P : Step S sp α} {Q : LStep S sp β} (h : Late post n Γ P Q) :
    ∀ d : DSt S, Γ.Knows d → n ≤ d.vals.length → (∀ y ∈ (P.run true d).support, Sf y) →
      expect (P.run true d) F = expect (Q.run d.forget) G := by
  induction h with
  | pure h =>
    intro d hK hn hs
    rw [run_pure, LStep.run, expect_pure, expect_pure]
    exact hFG _ _ _ _ d h hK hn
      (hs _ (by rw [run_pure]; exact (PMF.mem_support_pure_iff _ _).2 rfl))
  | sample _ ih =>
    intro d hK hn hs
    rw [run_sample, LStep.run, expect_bind, expect_bind]
    refine expect_congr _ fun r => ih r d hK hn fun y hy => hs y ?_
    rw [run_sample]
    exact (PMF.mem_support_bind_iff _ _ _).2 ⟨r, PMF.mem_support_uniformOfFintype r, hy⟩
  | @plain n Γ o q k k' _ ih =>
    intro d hK hn hs
    rw [run_plain, LStep.run, expect_bind, expect_bind]
    refine expect_congr_support _ fun z hz => ih z.1 (postPlain d o z.2) hK hn fun y hy => hs y ?_
    rw [run_plain]
    exact (PMF.mem_support_bind_iff _ _ _).2 ⟨z, hz, hy⟩
  | @fresh n Γ L k k' _ ih =>
    intro d hK hn hs
    rw [run_fresh, LStep.run, expect_bind, expect_bind]
    refine expect_congr _ fun u =>
      ih _ hn (postFresh d (List.ofFn u)) (knows_append hK _ rfl rfl rfl)
        (by simp [postFresh]) fun y hy => hs y ?_
    rw [run_fresh]
    exact (PMF.mem_support_bind_iff _ _ _).2 ⟨u, PMF.mem_support_uniformOfFintype u, hy⟩
  | @marked n Γ o t us pt inj k k' _ ih =>
    intro d hK hn hs
    have hs' : ∀ r : S.Rng o, ∀ y ∈ ((k (sp.split o r).1 d.vals.length).run true
        (postMarked sp d o t us (pt (d.val t) (us.map d.val)) r d.table)).support, Sf y := by
      intro r y hy
      refine hs y ?_
      rw [run_marked_I]
      exact (PMF.mem_support_bind_iff _ _ _).2 ⟨r, PMF.mem_support_uniformOfFintype r, hy⟩
    have hb : markedBad d o t us = false := by
      have h1 := noviol_of_safe _ _ fun y hy => hSf y (hs' (Classical.arbitrary _) y hy)
      have h2 : (d.viol || markedBad d o t us) = false := h1
      simp only [Bool.or_eq_false_iff] at h2
      exact h2.2
    rw [run_marked_I, LStep.run, expect_bind, expect_bind]
    show _ = expect (PMF.uniformOfFintype (S.Rng o)) _
    refine expect_congr _ fun r => ?_
    have hf : (postMarked sp d o t us (pt (d.val t) (us.map d.val)) r d.table).forget =
        { d.forget with
          vals := d.forget.vals ++ [List.ofFn (sp.split o r).2],
          evs := d.forget.evs ++ [⟨o, r, t, us, d.forget.vals.length, false⟩] } := by
      simp [postMarked, DSt.forget, Ev.forget]
    rw [← hf]
    exact ih _ _ hn _ (knows_marked hK o t us pt r d.table hb) (by simp [postMarked]) (hs' r)
  | @reveal n Γ ts pts k k' hp _ ih =>
    intro d hK hn hs
    rw [run_reveal, LStep.run, ← forget_postReveal hK ts pts hp]
    exact ih _ (postReveal true d ts) (knows_reveal hK ts) hn fun y hy =>
      hs y (by rw [run_reveal]; exact hy)

theorem late_interact {Out In α : Type} (C : Chall S sp Out In)
    (C' : LChall S sp Out In) (R : ℕ → Ctx S → C.τ → C'.τ → Prop)
    (hstep : ∀ n Γ s s' m, R n Γ s s' →
      Late (fun n' Γ' a b => a.1 = b.1 ∧ R n' Γ' a.2 b.2) n Γ (C.step s m) (C'.step s' m))
    (F : α → ℝ≥0∞) (A : Adv S Out In α) :
    ∀ (n : ℕ) (Γ : Ctx S) (s : C.τ) (s' : C'.τ) (d : DSt S), R n Γ s s' → Γ.Knows d →
      n ≤ d.vals.length → (∀ x ∈ (interact (C.world true) A (s, d)).support, x.2.2.viol = false) →
      expect (interact (C.world true) A (s, d)) (fun x => F x.1) =
        expect (interact C'.world A (s', d.forget)) fun x => F x.1 := by
  induction A with
  | halt a =>
    intro n Γ s s' d _ _ _ _
    simp only [interact, expect_pure]
  | sample m k ih =>
    intro n Γ s s' d hR hK hn hs
    simp only [interact, expect_bind]
    refine expect_congr _ fun r => ih r n Γ s s' d hR hK hn fun x hx => hs x ?_
    rw [interact]
    exact (PMF.mem_support_bind_iff _ _ _).2 ⟨r, PMF.mem_support_uniformOfFintype r, hx⟩
  | query o q k ih =>
    intro n Γ s s' d hR hK hn hs
    simp only [interact, Chall.world, LChall.world, expect_bind, expect_map]
    refine expect_congr_support _ fun z hz =>
      ih z.1 n Γ s s' (withT d z.2) hR hK hn fun x hx => hs x ?_
    rw [interact]
    exact (PMF.mem_support_bind_iff _ _ _).2
      ⟨(z.1, (s, withT d z.2)), (PMF.mem_support_map_iff _ _ _).2 ⟨z, hz, rfl⟩, hx⟩
  | call m k ih =>
    intro n Γ s s' d hR hK hn hs
    simp only [interact, Chall.world, LChall.world, expect_bind, expect_map]
    refine late_step
      (fun y => ∀ x ∈ (interact (C.world true) (k y.1.1) (y.1.2, y.2)).support, x.2.2.viol = false)
      (fun y hy => ?_) _ _ (fun n' Γ' a b d' hab hK' hn' hsf => ?_) (hstep n Γ s s' m hR) d hK hn
      fun y hy x hx => hs x ?_
    · obtain ⟨x, hx⟩ := (interact (C.world true) (k y.1.1) (y.1.2, y.2)).support_nonempty
      by_contra hc
      have := (interact_ext C _ _ x hx).viol (by simpa using hc)
      rw [hy x hx] at this
      simp at this
    · have := ih a.1 n' Γ' a.2 b.2 d' hab.2 hK' hn' hsf
      rw [hab.1] at this
      rw [hab.1]
      exact this
    · rw [interact]
      exact (PMF.mem_support_bind_iff _ _ _).2
        ⟨(y.1.1, (y.1.2, y.2)), (PMF.mem_support_map_iff _ _ _).2 ⟨y, hy, rfl⟩, hx⟩

theorem lateView : Spec.lateView := by
  intro S sp Out In α C C' R hstep A s₀ s₀' hR hs
  refine ext_of_expect fun F => ?_
  rw [expect_map, expect_map]
  exact late_interact C C' R hstep F A 0 (Ctx.empty S) s₀ s₀' (DSt.init S) hR
    (fun e he => by simp [DSt.init] at he) (Nat.zero_le _) hs

end DeferTail
end Rom

