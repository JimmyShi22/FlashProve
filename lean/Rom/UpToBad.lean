-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/UpToBad.lean: identical until bad, and step-by-step closeness, for interactive experiments.

The privacy proofs go from one experiment to the next. In each experiment an adversary makes oracle
queries and calls, and a challenger (`World`, Rom/World.lean) answers them from its own state. Two
arguments recur:
  * identical until bad: the two challengers answer alike until some event happens in the second
    experiment;
  * a hybrid over the moves: each move of the two challengers differs by at most z, so N moves
    differ by at most N z.
Both are instances of one theorem, `tv_interact_le`: if every move of the two challengers, from
related states, can be coupled so that, except with probability z, either the bad event has happened
or the answers agree and the states are related again, and if a bad state stays bad, then from
related start states the adversary's outputs are within
Pr[bad in the second experiment] + (the sum of the z along the most expensive path).

Sources. VCV-io (https://github.com/Verified-zkEVM/VCV-io), at commit afa6593f,
ProgramLogic/Relational/SimulateQ/UntilBad.lean, proves identical-until-bad; our first lemma (a bad
state stays bad) has the same statement and the same short induction as its first lemma, and the two
comments share a plain nine-word phrase. VCV-io also proves identical-until-bad and a per-query
error bound (the textbook lemmas), in another formulation. The general theorem here has the same
frame and the same order of lemmas as VCV-io's (a bad state stays bad; starting bad gives bad with
probability one; induction over the adversary), in another formulation; the first case of
`bad_of_mem_support_interact` also shares words with two other files of VCV-io. lean/CREDITS.md,
section 4, has VCV-io's entry.

-/
import Rom.World
noncomputable section -- Lean tags what it cannot compile

open scoped ENNReal
open Prob

namespace Rom

variable {S : OSpec} {Out In α : Type}

/-! ## 1. The cost of an adversary's most expensive path -/

/-- If a query to oracle o costs zq o and a call costs zc: the supremum of the cost over the
adversary's paths (below: its most expensive path). -/
def Adv.cost (zq : S.ι → ℝ≥0∞) (zc : ℝ≥0∞) : Adv S Out In α → ℝ≥0∞
  | .halt _ => 0
  | .sample _ k => ⨆ r, (k r).cost zq zc
  | .query o _ k => zq o + ⨆ r, (k r).cost zq zc
  | .call _ k => zc + ⨆ a, (k a).cost zq zc

theorem Adv.cost_zero (A : Adv S Out In α) : A.cost (fun _ => 0) 0 = 0 := by
  induction A with
  | halt a => rfl
  | sample n k ih => simp [Adv.cost, ih]
  | query o q k ih => simp [Adv.cost, ih]
  | call m k ih => simp [Adv.cost, ih]

/-- If only calls cost anything, an adversary with `A.Bounded t N` (at most N calls) has cost at
most N zc. -/
theorem Adv.cost_le_calls (zc : ℝ≥0∞) (A : Adv S Out In α) (t : S.ι → ℕ)
    (N : ℕ) (h : A.Bounded t N) :
    A.cost (fun _ => 0) zc ≤ N * zc := by
  induction A generalizing t N with
  | halt a => exact zero_le _
  | sample n k ih => exact iSup_le fun r => ih r t N (h r)
  | query o q k ih =>
    simp only [Adv.cost, zero_add]
    exact iSup_le fun r => ih r _ N (h.2 r)
  | call m k ih =>
    cases N with
    | zero => exact h.elim
    | succ N =>
      calc zc + ⨆ a, (k a).cost (fun _ => 0) zc ≤ zc + N * zc := by
            gcongr
            exact iSup_le fun a => ih a t N (h a)
        _ = ((N + 1 : ℕ) : ℝ≥0∞) * zc := by push_cast; ring

/-- If t o > 0, then lowering t o by one lowers Σ t o' · zq o' by zq o. -/
theorem budget_step [Fintype S.ι] (zq : S.ι → ℝ≥0∞) (t : S.ι → ℕ) (o : S.ι) (h : 0 < t o) :
    zq o + ∑ o', (Function.update t o (t o - 1) o' : ℝ≥0∞) * zq o' =
      ∑ o', (t o' : ℝ≥0∞) * zq o' := by
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ o),
    ← Finset.add_sum_erase Finset.univ (fun o' => (t o' : ℝ≥0∞) * zq o') (Finset.mem_univ o)]
  have hrest : ∑ o' ∈ Finset.univ.erase o, (Function.update t o (t o - 1) o' : ℝ≥0∞) * zq o'
      = ∑ o' ∈ Finset.univ.erase o, (t o' : ℝ≥0∞) * zq o' :=
    Finset.sum_congr rfl fun o' ho' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase ho')]
  have hhead : zq o + ((t o - 1 : ℕ) : ℝ≥0∞) * zq o = (t o : ℝ≥0∞) * zq o := by
    obtain ⟨n, hn⟩ : ∃ n, t o = n + 1 := ⟨t o - 1, by omega⟩
    rw [hn]
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  rw [hrest, Function.update_self, ← add_assoc, hhead]

/-- An adversary with at most t o queries to each oracle o and at most N calls has cost at most
Σ t o · zq o + N zc. -/
theorem Adv.cost_le_of_bounded [Fintype S.ι] (zq : S.ι → ℝ≥0∞) (zc : ℝ≥0∞) (A : Adv S Out In α)
    (t : S.ι → ℕ) (N : ℕ) (h : A.Bounded t N) :
    A.cost zq zc ≤ ∑ o, (t o : ℝ≥0∞) * zq o + N * zc := by
  induction A generalizing t N with
  | halt a => exact zero_le _
  | sample n k ih => exact iSup_le fun r => ih r t N (h r)
  | query o q k ih =>
    calc zq o + ⨆ r, (k r).cost zq zc
        ≤ zq o + (∑ o', (Function.update t o (t o - 1) o' : ℝ≥0∞) * zq o' + N * zc) := by
          gcongr
          exact iSup_le fun r => ih r _ N (h.2 r)
      _ = ∑ o', (t o' : ℝ≥0∞) * zq o' + N * zc := by rw [← add_assoc, budget_step zq t o h.1]
  | call m k ih =>
    cases N with
    | zero => exact h.elim
    | succ N =>
      calc zc + ⨆ a, (k a).cost zq zc ≤ zc + (∑ o, (t o : ℝ≥0∞) * zq o + N * zc) := by
            gcongr
            exact iSup_le fun a => ih a t N (h a)
        _ = ∑ o, (t o : ℝ≥0∞) * zq o + ((N + 1 : ℕ) : ℝ≥0∞) * zc := by push_cast; ring

/-! ## 2. Moves that are coupled up to an error -/

/-- The outcome of a coupled move is fine: the bad event has happened in the second experiment, or
the two answers agree and the two new states are related. -/
def Fine {σ₁ σ₂ X : Type} (Rel : σ₁ → σ₂ → Prop) (bad : σ₂ → Prop) (x : (X × σ₁) × (X × σ₂)) :
    Prop :=
  bad x.2.2 ∨ (x.1.1 = x.2.1 ∧ Rel x.1.2 x.2.2)

/-- Two moves (distributions of an answer and a new state) can be coupled so that the outcome is
fine except with probability z. -/
def CoupledUpTo {σ₁ σ₂ X : Type} (Rel : σ₁ → σ₂ → Prop) (bad : σ₂ → Prop) (z : ℝ≥0∞)
    (p₁ : PMF (X × σ₁)) (p₂ : PMF (X × σ₂)) : Prop :=
  ∃ c : PMF ((X × σ₁) × (X × σ₂)),
    c.map Prod.fst = p₁ ∧ c.map Prod.snd = p₂ ∧ pr c {x | ¬ Fine Rel bad x} ≤ z

/-- Every move of the two challengers from related states, the second not yet bad, is coupled up to
an error: zq o for a query to oracle o, zc for a call. And a bad state stays bad. -/
structure StepClose (W₁ W₂ : World S Out In) (Rel : W₁.σ → W₂.σ → Prop) (bad : W₂.σ → Prop)
    (zq : S.ι → ℝ≥0∞) (zc : ℝ≥0∞) : Prop where
  answer : ∀ s₁ s₂ o q,
    Rel s₁ s₂ → ¬ bad s₂ → CoupledUpTo Rel bad (zq o) (W₁.answer s₁ o q) (W₂.answer s₂ o q)
  reply : ∀ s₁ s₂ m, Rel s₁ s₂ → ¬ bad s₂ → CoupledUpTo Rel bad zc (W₁.reply s₁ m) (W₂.reply s₂ m)
  bad_answer : ∀ s₂ o q, bad s₂ → ∀ x ∈ (W₂.answer s₂ o q).support, bad x.2
  bad_reply : ∀ s₂ m, bad s₂ → ∀ x ∈ (W₂.reply s₂ m).support, bad x.2

/-- The hypothesis of "identical until bad" (`StepCoupled`) implies `StepClose` with all errors 0.
-/
theorem StepCoupled.stepClose {W₁ W₂ : World S Out In} {Rel : W₁.σ → W₂.σ → Prop}
    {bad : W₂.σ → Prop} (h : StepCoupled W₁ W₂ Rel bad) :
    StepClose W₁ W₂ Rel bad (fun _ => 0) 0 where
  answer := fun s₁ s₂ o q hR hb => by
    obtain ⟨c, h1, h2, h3⟩ := h.1 s₁ s₂ o q hR hb
    exact ⟨c, h1, h2,
      (pr_eq_zero_of_forall_not_mem c (E := {x | ¬ Fine Rel bad x}) fun x hx hn => hn (h3 x hx)).le⟩
  reply := fun s₁ s₂ m hR hb => by
    obtain ⟨c, h1, h2, h3⟩ := h.2.1 s₁ s₂ m hR hb
    exact ⟨c, h1, h2,
      (pr_eq_zero_of_forall_not_mem c (E := {x | ¬ Fine Rel bad x}) fun x hx hn => hn (h3 x hx)).le⟩
  bad_answer := h.2.2.1
  bad_reply := h.2.2.2

/-- One coupled move. G₁ and G₂ are what is still to come, as functions of the outcome of the move
in either experiment. -/
theorem expect_le_of_coupling {A₁ A₂ : Type} (c : PMF (A₁ × A₂)) (G₁ : A₁ → ℝ≥0∞) (G₂ : A₂ → ℝ≥0∞)
    (fine : A₁ × A₂ → Prop) {κ : ℝ≥0∞} (h₁ : ∀ a, G₁ a ≤ 1)
    (h : ∀ x, fine x → G₁ x.1 ≤ G₂ x.2 + κ) :
    expect (c.map Prod.fst) G₁ ≤ expect (c.map Prod.snd) G₂ + κ + pr c {x | ¬ fine x} := by
  obtain ⟨ind, hind, hval⟩ :
      ∃ ind : A₁ × A₂ → ℝ≥0∞, pr c {x | ¬ fine x} = expect c ind ∧ ∀ x, ¬ fine x → ind x = 1 :=
    ⟨_, pr_eq_expect c _, fun x hx => if_pos hx⟩
  rw [expect_map, expect_map, hind]
  calc expect c (fun x => G₁ x.1) ≤ expect c (fun x => (G₂ x.2 + κ) + ind x) := by
        refine expect_mono c fun x => ?_
        by_cases hx : fine x
        · exact (h x hx).trans le_self_add
        · rw [hval x hx]
          exact (h₁ x.1).trans le_add_self
    _ = expect c (fun x => G₂ x.2) + κ + expect c ind := by
        rw [expect_add, expect_add, expect_const]

/-! ## 3. A bad state stays bad -/

/-- If no move of the world leaves the set bad, a run from a bad state ends in a bad state. -/
theorem bad_of_mem_support_interact (W : World S Out In) (bad : W.σ → Prop)
    (hq : ∀ s o q, bad s → ∀ x ∈ (W.answer s o q).support, bad x.2)
    (hc : ∀ s m, bad s → ∀ x ∈ (W.reply s m).support, bad x.2) (A : Adv S Out In α)
    (s : W.σ) (hs : bad s) :
    ∀ x ∈ (interact W A s).support, bad x.2 := by
  induction A generalizing s with
  | halt a =>
    intro x hx
    simp only [interact, PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact hs
  | sample n k ih =>
    intro x hx
    simp only [interact, PMF.mem_support_bind_iff] at hx
    obtain ⟨r, _, hr⟩ := hx
    exact ih r s hs x hr
  | query o q k ih =>
    intro x hx
    simp only [interact, PMF.mem_support_bind_iff] at hx
    obtain ⟨p, hp, hx'⟩ := hx
    exact ih p.1 p.2 (hq s o q hs p hp) x hx'
  | call m k ih =>
    intro x hx
    simp only [interact, PMF.mem_support_bind_iff] at hx
    obtain ⟨p, hp, hx'⟩ := hx
    exact ih p.1 p.2 (hc s m hs p hp) x hx'

/-! ## 4. The general theorem -/

section Main
variable {W₁ W₂ : World S Out In}
  {Rel : W₁.σ → W₂.σ → Prop} {bad : W₂.σ → Prop} {zq : S.ι → ℝ≥0∞} {zc : ℝ≥0∞}

theorem StepClose.pr_eq_one_of_bad
    (h : StepClose W₁ W₂ Rel bad zq zc) (E : Set α) (A : Adv S Out In α) (s₂ : W₂.σ) (hb : bad s₂) :
    pr (interact W₂ A s₂) {x | x.1 ∈ E ∨ bad x.2} = 1 :=
  pr_eq_one_of_support_subset _ fun x hx =>
    Or.inr (bad_of_mem_support_interact W₂ bad h.bad_answer h.bad_reply A s₂ hb x hx)

/-- What one move contributes to the induction, for a query and for a call alike. -/
theorem StepClose.move_le (h : StepClose W₁ W₂ Rel bad zq zc) (E : Set α)
    {X : Type} (k : X → Adv S Out In α) {p₁ : PMF (X × W₁.σ)} {p₂ : PMF (X × W₂.σ)}
    {z : ℝ≥0∞} (hc : CoupledUpTo Rel bad z p₁ p₂)
    (ih : ∀ (a : X) (s₁ : W₁.σ) (s₂ : W₂.σ), Rel s₁ s₂ → ¬ bad s₂ →
      pr (interact W₁ (k a) s₁) {x | x.1 ∈ E} ≤
        pr (interact W₂ (k a) s₂) {x | x.1 ∈ E ∨ bad x.2} + (k a).cost zq zc) :
    pr (p₁.bind fun p => interact W₁ (k p.1) p.2) {x | x.1 ∈ E} ≤
      pr (p₂.bind fun p => interact W₂ (k p.1) p.2) {x | x.1 ∈ E ∨ bad x.2} +
        (z + ⨆ a, (k a).cost zq zc) := by
  obtain ⟨c, h1, h2, h3⟩ := hc
  rw [pr_bind, pr_bind, ← h1, ← h2]
  have hstep := expect_le_of_coupling c
    (fun p : X × W₁.σ => pr (interact W₁ (k p.1) p.2) {x | x.1 ∈ E})
    (fun p : X × W₂.σ => pr (interact W₂ (k p.1) p.2) {x | x.1 ∈ E ∨ bad x.2})
    (Fine Rel bad) (κ := ⨆ a, (k a).cost zq zc) (fun p => pr_le_one _ _) (fun x hx => by
      change pr (interact W₁ (k x.1.1) x.1.2) {x | x.1 ∈ E}
        ≤ pr (interact W₂ (k x.2.1) x.2.2) {x | x.1 ∈ E ∨ bad x.2} + ⨆ a, (k a).cost zq zc
      by_cases hb : bad x.2.2
      · rw [h.pr_eq_one_of_bad E (k x.2.1) x.2.2 hb]
        exact (pr_le_one _ _).trans le_self_add
      · obtain ⟨he, hR⟩ := hx.resolve_left hb
        rw [← he]
        exact (ih x.1.1 x.1.2 x.2.2 hR hb).trans
          (by gcongr; exact le_iSup (fun a => (k a).cost zq zc) x.1.1))
  calc _ ≤ _ := hstep
    _ ≤ expect (c.map Prod.snd)
            (fun p : X × W₂.σ => pr (interact W₂ (k p.1) p.2) {x | x.1 ∈ E ∨ bad x.2}) +
          (⨆ a, (k a).cost zq zc) + z := by gcongr
    _ = _ := by ring

/-- The core. Under `StepClose`, from related states: every event about the adversary's output is at
most as likely in the first experiment as "the event or bad" in the second, up to the cost of the
adversary's most expensive path. -/
theorem StepClose.pr_interact_le (h : StepClose W₁ W₂ Rel bad zq zc) (E : Set α)
    (A : Adv S Out In α) (s₁ : W₁.σ) (s₂ : W₂.σ) (hR : Rel s₁ s₂) :
    pr (interact W₁ A s₁) {x | x.1 ∈ E} ≤
      pr (interact W₂ A s₂) {x | x.1 ∈ E ∨ bad x.2} + A.cost zq zc := by
  by_cases hb : bad s₂
  · rw [h.pr_eq_one_of_bad E A s₂ hb]
    exact (pr_le_one _ _).trans le_self_add
  induction A generalizing s₁ s₂ with
  | halt a =>
    classical
    simp only [interact, pr_pure, Adv.cost, add_zero, Set.mem_setOf_eq]
    by_cases ha : a ∈ E <;> simp [ha]
  | sample n k ih =>
    simp only [interact, Adv.cost]
    rw [pr_bind, pr_bind]
    calc
      expect (PMF.uniformOfFintype (Fin (n + 1)))
            (fun r => pr (interact W₁ (k r) s₁) {x | x.1 ∈ E}) ≤
          expect (PMF.uniformOfFintype (Fin (n + 1)))
            (fun r => pr (interact W₂ (k r) s₂) {x | x.1 ∈ E ∨ bad x.2} + ⨆ r, (k r).cost zq zc) :=
          expect_mono _ fun r => (ih r s₁ s₂ hR hb).trans
            (by gcongr; exact le_iSup (fun r => (k r).cost zq zc) r)
      _ = _ := by rw [expect_add, expect_const]
  | query o q k ih =>
    exact h.move_le E k (h.answer s₁ s₂ o q hR hb) ih
  | call m k ih =>
    exact h.move_le E k (h.reply s₁ s₂ m hR hb) ih

/-- The general theorem. Under `StepClose`, from related states: the adversary's outputs in the two
experiments are within Pr[bad in the second] + the cost of its most expensive path. -/
theorem tv_interact_le (h : StepClose W₁ W₂ Rel bad zq zc) (A : Adv S Out In α) (s₁ : W₁.σ)
    (s₂ : W₂.σ) (hR : Rel s₁ s₂) :
    tv ((interact W₁ A s₁).map Prod.fst) ((interact W₂ A s₂).map Prod.fst) ≤
      pr (interact W₂ A s₂) {x | bad x.2} + A.cost zq zc :=
  tv_le_of_forall_pr_le fun E => by
    rw [pr_map, pr_map]
    calc
      pr (interact W₁ A s₁) (Prod.fst ⁻¹' E) ≤
          pr (interact W₂ A s₂) {x | x.1 ∈ E ∨ bad x.2} + A.cost zq zc :=
        h.pr_interact_le E A s₁ s₂ hR
      _ ≤ (pr (interact W₂ A s₂) (Prod.fst ⁻¹' E) + pr (interact W₂ A s₂) {x | bad x.2}) +
            A.cost zq zc := by
          gcongr
          exact pr_union_le _ _ _
      _ = _ := by ring

/-- The general theorem for an adversary with at most t o queries to each oracle o and at most N
calls. -/
theorem tv_interact_le_of_bounded [Fintype S.ι] (h : StepClose W₁ W₂ Rel bad zq zc)
    (A : Adv S Out In α) (t : S.ι → ℕ) (N : ℕ) (hA : A.Bounded t N) (s₁ : W₁.σ)
    (s₂ : W₂.σ) (hR : Rel s₁ s₂) :
    tv ((interact W₁ A s₁).map Prod.fst) ((interact W₂ A s₂).map Prod.fst) ≤
      pr (interact W₂ A s₂) {x | bad x.2} + (∑ o, (t o : ℝ≥0∞) * zq o + N * zc) :=
  (tv_interact_le h A s₁ s₂ hR).trans (by gcongr; exact A.cost_le_of_bounded zq zc t N hA)

/-- Hybrid over the calls. Under `StepClose` with zq = 0, from related states, for an adversary with
`A.Bounded t N`: N calls cost N zc (in addition to the probability of bad). -/
theorem tv_interact_le_calls (h : StepClose W₁ W₂ Rel bad (fun _ => 0) zc) (A : Adv S Out In α)
    (t : S.ι → ℕ) (N : ℕ) (hA : A.Bounded t N) (s₁ : W₁.σ) (s₂ : W₂.σ) (hR : Rel s₁ s₂) :
    tv ((interact W₁ A s₁).map Prod.fst) ((interact W₂ A s₂).map Prod.fst)
      ≤ pr (interact W₂ A s₂) {x | bad x.2} + N * zc :=
  (tv_interact_le h A s₁ s₂ hR).trans (by gcongr; exact A.cost_le_calls zc t N hA)

end Main

/-- Identical until bad, for interactive experiments. -/
theorem upToBad : Spec.upToBad := by
  intro S Out In α W₁ W₂ Rel bad h A s₁ s₂ hR
  have := tv_interact_le h.stepClose A s₁ s₂ hR
  rwa [Adv.cost_zero, add_zero] at this

/-! ## 5. The probability of bad -/

/-- If each move from a state that is not bad leads to a bad state with probability at most zq o (a
query to o) or zc (a call), then a run from a state that is not bad ends in a bad state with
probability at most the cost of the adversary's most expensive path. -/
theorem pr_bad_interact_le (W : World S Out In) (bad : W.σ → Prop) (zq : S.ι → ℝ≥0∞)
    (zc : ℝ≥0∞) (hq : ∀ s o q, ¬ bad s → pr (W.answer s o q) {x | bad x.2} ≤ zq o)
    (hc : ∀ s m, ¬ bad s → pr (W.reply s m) {x | bad x.2} ≤ zc) (A : Adv S Out In α)
    (s : W.σ) (hs : ¬ bad s) :
    pr (interact W A s) {x | bad x.2} ≤ A.cost zq zc := by
  induction A generalizing s with
  | halt a =>
    classical
    simp [interact, pr_pure, hs]
  | sample n k ih =>
    simp only [interact, Adv.cost]
    exact pr_bind_le_of_forall _ _ _ fun r _ =>
      (ih r s hs).trans (le_iSup (fun r => (k r).cost zq zc) r)
  | query o q k ih =>
    simp only [interact, Adv.cost]
    refine (pr_bind_le_add (W.answer s o q) _ _ {x | bad x.2}
      (ε := ⨆ r, (k r).cost zq zc) ?_).trans ?_
    · intro p _ hp
      exact (ih p.1 p.2 hp).trans (le_iSup (fun r => (k r).cost zq zc) p.1)
    · gcongr
      exact hq s o q hs
  | call m k ih =>
    simp only [interact, Adv.cost]
    refine (pr_bind_le_add (W.reply s m) _ _ {x | bad x.2} (ε := ⨆ a, (k a).cost zq zc) ?_).trans ?_
    · intro p _ hp
      exact (ih p.1 p.2 hp).trans (le_iSup (fun a => (k a).cost zq zc) p.1)
    · gcongr
      exact hc s m hs

/-! ## 6. A chain of challengers -/

/-- Hybrid over a chain of challengers W 0, .., W n, each started in its own state: the distances
between neighbours add up. -/
theorem tv_worlds_hybrid (W : ℕ → World S Out In) (s : ∀ i, (W i).σ) (A : Adv S Out In α) (n : ℕ) :
    tv ((interact (W 0) A (s 0)).map Prod.fst) ((interact (W n) A (s n)).map Prod.fst) ≤
      ∑ i ∈ Finset.range n, tv ((interact (W i) A (s i)).map Prod.fst)
        ((interact (W (i + 1)) A (s (i + 1))).map Prod.fst) :=
  tv_hybrid_range (fun i => (interact (W i) A (s i)).map Prod.fst) n

/-! ## 7. Two challengers on one state space whose moves are close in statistical distance -/


/-- Close moves. If all moves of two challengers on the same states are close, then, from the same
start state, output and final state together are within the cost of the adversary's most expensive
path. -/
theorem tv_interact_state_le {σ : Type} (ans₁ ans₂ : σ → (o : S.ι) → S.Dom o → PMF (S.Rng o × σ))
    (rep₁ rep₂ : σ → Out → PMF (In × σ)) (zq : S.ι → ℝ≥0∞) (zc : ℝ≥0∞)
    (hq : ∀ s o q, tv (ans₁ s o q) (ans₂ s o q) ≤ zq o) (hc : ∀ s m, tv (rep₁ s m) (rep₂ s m) ≤ zc)
    (A : Adv S Out In α) (s : σ) :
    tv (interact (⟨σ, ans₁, rep₁⟩ : World S Out In) A s)
        (interact (⟨σ, ans₂, rep₂⟩ : World S Out In) A s) ≤
      A.cost zq zc := by
  induction A generalizing s with
  | halt a => simp [interact]
  | sample n k ih =>
    simp only [interact, Adv.cost]
    exact tv_bind_right_le_of_forall _ _ _ fun r _ =>
      (ih r s).trans (le_iSup (fun r => (k r).cost zq zc) r)
  | query o q k ih =>
    simp only [interact, Adv.cost]
    refine (tv_bind_le_of_forall _ _ _ _ (z := ⨆ r, (k r).cost zq zc) fun p => ?_).trans ?_
    · exact (ih p.1 p.2).trans (le_iSup (fun r => (k r).cost zq zc) p.1)
    · gcongr
      exact hq s o q
  | call m k ih =>
    simp only [interact, Adv.cost]
    refine (tv_bind_le_of_forall _ _ _ _ (z := ⨆ a, (k a).cost zq zc) fun p => ?_).trans ?_
    · exact (ih p.1 p.2).trans (le_iSup (fun a => (k a).cost zq zc) p.1)
    · gcongr
      exact hc s m

end Rom
