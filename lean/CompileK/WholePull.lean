-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/WholePull.lean: `Spec.hvzk_pull`: under the hypotheses of its statement, honest-verifier
zero knowledge of the whole object (`HVZKWhole`, Hiop/Whole.lean) is kept when verifier messages
are made by samplers. A black box: nothing is asked of the interface but HVZKWhole and `0 < L.maxBatchSize`.

Definitions, statements and proofs.
The compiler does not compile an interface L itself but `L.draws dr`: each verifier message is
φ(blocks), the blocks uniform (Iop/Pull.lean, Iop/BatchWireDraw.lean), and what is shown of a run
holds the blocks. φ(uniform blocks) is not uniform: it has a density of at most K against the
uniform law (`Samplers.Good`; `prRho_preimage_le`, Iop/PullProofs.lean; for all slots of a session
together K^N: `prBRho_preimage_le`, Iop/BatchPullProofs.lean).
The pulled object is `L.pull σT σL σB` (Iop/BatchPull.lean): in every round the verifier message is
a point of the sampler's source, which φ pushes to a verifier message of L; the fibre of ρ is what
φ sends to ρ.

Main names:
  `hvzk_pull : Spec.hvzk_pull`: under the hypotheses of its statement,
      HVZKWhole L Ryes B (simWhole L Sm i₀) z ⇒
      HVZKWhole (L.pull σT σL σB) Ryes B (simWhole _ (simsPull L σT σL σB Sm) i₀)
        (factor B L.maxBatchSize KT KL KB · z),
    factor = KT · KL^nenc · (KB^N)^(Σ_j sess j): one factor for each run that the bounds B allow.
    Same bounds B, same relation; the run simulators are the old ones at the pushed verifier
    messages.
  `hvzk_draws`: the same for `L.draws dr` and the run simulators `simsD` of Top/ProgDraw.lean, all
    three K = κ₀^n.

How: rejection sampling inside the environment. An environment of the pulled object is played
against the object (`tr`, `trE`), with outputs in Option α. After each run it is shown (ρ, o) with
ρ uniform (exactly: `adaptQ`, `adaptB`); it draws a point ρ' of the fibre of ρ, each with
probability μ'(ρ') / (K μ(ρ)), or gives up and stops with none (`fib`, `adapt`); then it goes on
with (ρ', o carried over). Given that it does not give up, ρ' has the law of the pulled object, and
this happens with probability exactly 1/K (`adapts_run`). When the pulled environment stops, the
new one tosses a coin for each run that the bounds allow and that was not asked for (`pad`), so
that every path carries the same factor (`expect_tr`, `expect_view`): whatever is measured of the
pulled view is the factor times the same measured of the outputs "some ..". The adapter reads ρ
only, so it is the same on the real and on the simulated side; hence the distance of the two pulled
views is at most the factor times the distance of the two views of the object (`tv_view_pull`). The
new environment asks for the same runs at the same places, so it keeps the bounds (`adm_tr`). It is
used that the honest output of a session for J, and the simulator, read the verifier's randomness
only through the slots of J (`adapts_bsess`, `adapts_simBsess`).
  Part 1: rejection; `Adapts`; the adapter of a run. Part 2: the environment; the factor. Part 3:
    bounds, view, distance. Part 4: the adapters of the three kinds of runs, real and simulated.
    Part 5: the theorems.

Limits: the factor is paid on z for every run that the bounds allow, all at once: run by run
(`drawsPropsB`, Iop/BatchWireDraw.lean, then `hvzk_whole`, Hiop/WholeProof.lean) each run's own
error is multiplied by the factor of that run alone, which is less. That is the price of the black
box. With κ₀ = 1 (no bias) the factor is 1. This file says nothing on running time: the new
environment evaluates probabilities of fibres. The simulator is again the named one (`simWhole`),
around the pulled run simulators.

Terms: lean/GLOSSARY.md.
-/
import Hiop.WholeProof
import Iop.BatchPullProofs
import Iop.BatchPullNamed
import Top.ProgDraw

set_option autoImplicit false

noncomputable section

namespace Hiop.Pull
open Prob Iop Iop.BatchPull Compile.Lifetime Compile.BatchLife
open scoped ENNReal

/-! ## Part 1. Rejection -/

section Rej
variable {β : Type}

/-- a function on β as a function on Option β that is 0 at none -/
def lift (F : β → ℝ≥0∞) : Option β → ℝ≥0∞
  | none => 0
  | some b => F b

variable [Fintype β]

open Classical in
/-- some b with probability w b, none with the rest (none for sure, if the w b add up to more than
1) -/
def rej (w : β → ℝ≥0∞) : PMF (Option β) :=
  if h : ∑ b, w b ≤ 1 then
    PMF.ofFintype (fun o => match o with
      | none => 1 - ∑ b, w b
      | some b => w b) (by rw [Fintype.sum_option]; exact tsub_add_cancel_of_le h)
  else PMF.pure none

theorem expect_rej {w : β → ℝ≥0∞} (h : ∑ b, w b ≤ 1) (F : β → ℝ≥0∞) :
    expect (rej w) (lift F) = ∑ b, w b * F b := by
  classical
  unfold rej
  rw [dif_pos h, expect_fintype, Fintype.sum_option]
  simp only [PMF.ofFintype_apply, lift, mul_zero, zero_add]

end Rej

/-- the coin that shows some () with probability 1 / K, if 1 ≤ K -/
def coin (K : ℝ≥0∞) : PMF (Option Unit) := rej fun _ => K⁻¹

theorem expect_coin {K : ℝ≥0∞} (h1 : 1 ≤ K) (hK : K ≠ ⊤) (v : ℝ≥0∞) :
    K * expect (coin K) (lift fun _ => v) = v := by
  unfold coin
  rw [expect_rej (by simpa using ENNReal.inv_le_one.2 h1)]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [← mul_assoc, ENNReal.mul_inv_cancel (fun h => by rw [h] at h1; simp at h1) hK, one_mul]

/-- P' is P seen through the adapter Ad, up to the factor K: the adapter turns what is shown of a
run of the one object into what is shown of a run of the other, or gives up. -/
def Adapts {A A' : Type} (P : PMF A) (P' : PMF A') (Ad : A → PMF (Option A')) (K : ℝ≥0∞) : Prop :=
  ∀ F : A' → ℝ≥0∞, K * expect P (fun a => expect (Ad a) (lift F)) = expect P' F

section Fibre
variable {R R' : Type} [Fintype R] [Fintype R']

open Classical in
/-- given ρ: a point ρ' of the fibre of ρ, with probability μ' ρ' / (K μ ρ), or none (as `rej`) -/
def fib (μ : PMF R) (μ' : PMF R') (φ : R' → R) (K : ℝ≥0∞) (ρ : R) : PMF (Option R') :=
  rej fun ρ' => if φ ρ' = ρ then μ' ρ' / (K * μ ρ) else 0

variable {μ : PMF R} {μ' : PMF R'} {φ : R' → R} {K : ℝ≥0∞}

omit [Fintype R] in
theorem map_apply_eq_sum (μ' : PMF R') (φ : R' → R) (ρ : R) :
    (μ'.map φ) ρ = ∑ ρ', (open Classical in if φ ρ' = ρ then μ' ρ' else 0) := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  exact Finset.sum_congr rfl fun ρ' _ => by simp only [eq_comm]

omit [Fintype R] in
theorem fib_sum_le (hden : ∀ ρ, (μ'.map φ) ρ ≤ K * μ ρ) (ρ : R) :
    ∑ ρ', (open Classical in if φ ρ' = ρ then μ' ρ' / (K * μ ρ) else 0) ≤ 1 := by
  classical
  have e : ∑ ρ', (if φ ρ' = ρ then μ' ρ' / (K * μ ρ) else 0) = (μ'.map φ) ρ / (K * μ ρ) := by
    rw [map_apply_eq_sum, div_eq_mul_inv, Finset.sum_mul]
    exact Finset.sum_congr rfl fun ρ' _ => by split_ifs <;> simp [div_eq_mul_inv]
  rw [e]
  exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact hden ρ)

/-- The adapter of a run whose shown data are (ρ, o), ρ of law μ and o of law ker ρ: draw ρ' in the
fibre, carry o over by g. -/
def adapt {O O' : Type} (μ : PMF R) (μ' : PMF R') (φ : R' → R) (K : ℝ≥0∞) (g : O → O') (u : R × O) :
    PMF (Option (R' × O')) :=
  (fib μ μ' φ K u.1).map (Option.map fun ρ' => (ρ', g u.2))

theorem lift_comp_map {β γ : Type} (F : γ → ℝ≥0∞) (h : β → γ) :
    (fun o : Option β => lift F (o.map h)) = lift fun b => F (h b) := by
  funext o
  cases o <;> rfl

theorem adapts_run {O O' : Type} (hKt : K ≠ ⊤) (hden : ∀ ρ, (μ'.map φ) ρ ≤ K * μ ρ)
    (ker : R → PMF O) (g : O → O') :
    Adapts (μ.bind fun ρ => (ker ρ).map fun o => (ρ, o))
      (μ'.bind fun ρ' => (ker (φ ρ')).map fun o => (ρ', g o)) (adapt μ μ' φ K g) K := by
  classical
  intro F
  simp only [expect_bind, expect_map, adapt, lift_comp_map]
  unfold fib
  simp only [expect_rej (fib_sum_le hden _), expect_finset_sum, expect_const_mul]
  rw [expect_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ' _ => ?_
  rw [expect_fintype,
    Finset.sum_eq_single (φ ρ') (fun ρ _ hne => by rw [if_neg (Ne.symm hne)]; simp)
      (fun h => absurd (Finset.mem_univ _) h), if_pos rfl]
  have hle : μ' ρ' ≤ K * μ (φ ρ') := le_trans (by
    rw [map_apply_eq_sum]
    exact (le_of_eq (by simp)).trans (Finset.single_le_sum (f := fun x => if φ x = φ ρ' then μ' x else 0) (fun _ _ => zero_le _) (Finset.mem_univ ρ'))) (hden (φ ρ'))
  have hcancel : K * μ (φ ρ') * (μ' ρ' / (K * μ (φ ρ'))) = μ' ρ' :=
    ENNReal.mul_div_cancel' (fun h0 => le_antisymm (h0 ▸ hle) (zero_le _))
      (fun ht => absurd ht (ENNReal.mul_ne_top hKt (PMF.apply_ne_top _ _)))
  rw [← mul_assoc, ← mul_assoc, hcancel]

end Fibre

theorem Adapts.use {A A' : Type} {P : PMF A} {P' : PMF A'} {Ad : A → PMF (Option A')}
    {K : ℝ≥0∞} (h : Adapts P P' Ad K) (c : ℝ≥0∞) (G : Option A' → ℝ≥0∞) (Φ : A' → ℝ≥0∞)
    (h0 : G none = 0) (h1 : ∀ u', c * G (some u') = Φ u') :
    K * c * expect P (fun u => expect (Ad u) G) = expect P' Φ := by
  have e : ∀ o, c * G o = lift Φ o := fun o => by
    cases o with
    | none => rw [h0, mul_zero]; rfl
    | some u' => exact h1 u'
  have e2 : c * expect P (fun u => expect (Ad u) G) = expect P fun u => expect (Ad u) (lift Φ) := by
    rw [← expect_const_mul]
    refine expect_congr _ fun u => ?_
    rw [← expect_const_mul]
    exact expect_congr _ e
  rw [mul_assoc, e2]
  exact h Φ

/-! ## Part 2. An environment of the pulled object as an environment of the object -/

section Env
variable {I X : Type} {L : BatchProtocol I X} {σT : Samplers L.offline.shape} {σL : Samplers L.link.shape}
  {σB : Samplers L.onlineBatch.loc.shape} {α : Type}

/-- toss n coins; stop with none as soon as one of them shows none -/
def pad (K : ℝ≥0∞) : ℕ → Env L (Option α) → Env L (Option α)
  | 0, t => t
  | n + 1, t => .draw (Option Unit) (coin K) fun o => match o with
      | none => .stop none
      | some _ => pad K n t

variable (AdL : Sess L.link → PMF (Option (Sess (L.pull σT σL σB).link)))
  (AdB : (J : Finset (Fin L.maxBatchSize)) → BSess L.onlineBatch J → PMF (Option (BSess (L.pull σT σL σB).onlineBatch J)))
  (KL KB : ℝ≥0∞)

/-- The environment t of the pulled object, played against the object. After each run it passes
what is shown through the adapter, and stops with none if that gives up. a, b: how many further
encoded indices and how many sessions it may still ask for; when t stops it tosses the coins of the
runs that it has not asked for, so that all paths carry the same factor. -/
def tr : Env (L.pull σT σL σB) α → ℕ → ℕ → Env L (Option α)
  | .stop x, a, b => pad KL a (pad KB b (.stop (some x)))
  | .fresh _, 0, _ => .stop none
  | .fresh k, a + 1, b => .fresh fun u => .draw _ (AdL u) fun o => match o with
      | none => .stop none
      | some u' => tr (k u') a b
  | .session _ _ _ _ _, _, 0 => .stop none
  | .session e J xs rest k, a, b + 1 => .session e J xs rest fun u => .draw _ (AdB J u) fun o => match o with
      | none => .stop none
      | some u' => tr (k u') a b
  | .read e p k, a, b => .read e p fun y => tr (k y) a b
  | .draw β d k, a, b => .draw β d fun y => tr (k y) a b

/-- on every path at most a further encoded indices and at most b sessions -/
def RunsLe : Env (L.pull σT σL σB) α → ℕ → ℕ → Prop
  | .stop _, _, _ => True
  | .fresh _, 0, _ => False
  | .fresh k, a + 1, b => ∀ u, RunsLe (k u) a b
  | .session _ _ _ _ _, _, 0 => False
  | .session _ _ _ _ k, a, b + 1 => ∀ u, RunsLe (k u) a b
  | .read _ _ k, a, b => ∀ y, RunsLe (k y) a b
  | .draw _ _ k, a, b => ∀ y, RunsLe (k y) a b

theorem expect_pad {K : ℝ≥0∞} (h1 : 1 ≤ K) (hK : K ≠ ⊤) (H : Host L) (s : H.σ)
    (F : α → ℝ≥0∞) (t : Env L (Option α)) :
    ∀ n : ℕ, K ^ n * expect ((pad K n t).run H s) (lift F) = expect (t.run H s) (lift F)
  | 0 => by rw [pow_zero, one_mul]; rfl
  | n + 1 => by
      show K ^ (n + 1) * expect ((coin K).bind fun o => (match o with
        | none => (.stop none : Env L (Option α))
        | some _ => pad K n t).run H s) (lift F) = _
      rw [expect_bind]
      have e : (fun o : Option Unit => expect ((match o with
          | none => (.stop none : Env L (Option α))
          | some _ => pad K n t).run H s) (lift F)) = lift fun _ => expect ((pad K n t).run H s) (lift F) := by
        funext o
        cases o with
        | none => exact expect_pure _ _
        | some _ => rfl
      rw [e, pow_succ, mul_assoc, expect_coin h1 hK, expect_pad h1 hK H s F t n]

variable {AdL AdB KL KB}

/-- The factor. Under the hypotheses below, whatever is measured of the outputs of the pulled play
is KL^a · KB^b times the same measured of the outputs "some .." of the play against the object. -/
theorem expect_tr (W : Laws L) (W' : Laws (L.pull σT σL σB)) (hL1 : 1 ≤ KL) (hLt : KL ≠ ⊤)
    (hB1 : 1 ≤ KB) (hBt : KB ≠ ⊤) (hL : ∀ r r', Adapts (W.Lk r r') (W'.Lk r r') AdL KL)
    (hB : ∀ r J xs rest, Adapts (W.B r J xs rest) (W'.B r J xs rest) (AdB J) KB)
    (hy : ∀ r p, W'.y r p = W.y r p) (F : α → ℝ≥0∞) :
    ∀ (t : Env (L.pull σT σL σB) α) (a b : ℕ) (s : ℕ × (ℕ → L.EncodingRandomness)), RunsLe t a b →
      KL ^ a * KB ^ b * expect ((tr AdL AdB KL KB t a b).run W.host s) (lift F) =
        expect (t.run W'.host s) F := by
  intro t
  induction t with
  | stop x =>
    intro a b s _
    simp only [tr]
    rw [mul_comm (KL ^ a), mul_assoc, expect_pad hL1 hLt, expect_pad hB1 hBt, run_stop, expect_pure]
    exact (expect_pure x F).symm
  | fresh k ih =>
    intro a b s h
    obtain ⟨c, f⟩ := s
    cases a with
    | zero => exact h.elim
    | succ a =>
      simp only [tr]
      refine Eq.trans ?_ (congrArg (fun P => expect P F) (run_fresh W' k c f)).symm
      rw [run_fresh]
      simp only [run_draw, expect_bind]
      rw [← expect_const_mul]
      refine expect_congr _ fun r => ?_
      rw [show KL ^ (a + 1) * KB ^ b = KL * (KL ^ a * KB ^ b) by rw [pow_succ]; ring]
      exact (hL (f 0) r).use _ _ _ (expect_pure _ _) fun u' => ih u' a b _ (h u')
  | session e J xs rest k ih =>
    intro a b s h
    cases b with
    | zero => exact h.elim
    | succ b =>
      simp only [tr]
      refine Eq.trans ?_ (congrArg (fun P => expect P F) (run_session W' e J xs rest k s)).symm
      rw [run_session]
      simp only [run_draw, expect_bind]
      rw [show KL ^ a * KB ^ (b + 1) = KB * (KL ^ a * KB ^ b) by rw [pow_succ]; ring]
      exact (hB (s.2 e) J xs rest).use _ _ _ (expect_pure _ _) fun u' => ih u' a b _ (h u')
  | read e p k ih =>
    intro a b s h
    simp only [tr]
    refine Eq.trans ?_ (congrArg (fun P => expect P F) (run_read W' e p k s)).symm
    rw [run_read]
    show _ = expect ((k (W'.y (s.2 e) p)).run W'.host s) F
    rw [hy]
    exact ih _ a b s (h _)
  | draw β d k ih =>
    intro a b s h
    simp only [tr]
    refine Eq.trans ?_ (congrArg (fun P => expect P F) (run_draw W' β d k s)).symm
    rw [run_draw]
    simp only [expect_bind]
    rw [← expect_const_mul]
    exact expect_congr _ fun y => ih y a b s (h y)

end Env

/-! ## Part 3. The bounds are kept; the view; the distance -/

section Bounds
variable {I X : Type} {L : BatchProtocol I X} {σT : Samplers L.offline.shape} {σL : Samplers L.link.shape}
  {σB : Samplers L.onlineBatch.loc.shape} {α : Type} {B : Bounds} {ok : X → Prop}

theorem adm_pad (K : ℝ≥0∞) {c : ℕ} {us ur : ℕ → ℕ} :
    ∀ (n : ℕ) (t : Env L (Option α)), t.Adm B ok c us ur → (pad K n t).Adm B ok c us ur
  | 0, _, h => h
  | n + 1, t, h => fun o => by
      cases o with
      | none => trivial
      | some _ => exact adm_pad K n t h

variable (AdT : Sess L.offline → PMF (Option (Sess (L.pull σT σL σB).offline)))
  (AdL : Sess L.link → PMF (Option (Sess (L.pull σT σL σB).link)))
  (AdB : (J : Finset (Fin L.maxBatchSize)) → BSess L.onlineBatch J → PMF (Option (BSess (L.pull σT σL σB).onlineBatch J)))
  (KT KL KB : ℝ≥0∞)

/-- The new environment asks for the same runs, at the same places, so it keeps the bounds
(`Env.Adm`). -/
theorem adm_tr :
    ∀ (t : Env (L.pull σT σL σB) α) (a b c : ℕ) (us ur : ℕ → ℕ),
      t.Adm B ok c us ur → (tr AdL AdB KL KB t a b).Adm B ok c us ur := by
  intro t
  induction t with
  | stop x =>
    intro a b c us ur _
    simp only [tr]
    exact adm_pad _ _ _ (adm_pad _ _ _ trivial)
  | fresh k ih =>
    intro a b c us ur h
    cases a with
    | zero => trivial
    | succ a =>
      simp only [tr]
      refine ⟨h.1, fun u o => ?_⟩
      cases o with
      | none => trivial
      | some u' => exact ih u' a b _ _ _ (h.2 u')
  | session e J xs rest k ih =>
    intro a b c us ur h
    cases b with
    | zero => trivial
    | succ b =>
      simp only [tr]
      refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun u o => ?_⟩
      cases o with
      | none => trivial
      | some u' => exact ih u' a b _ _ _ (h.2.2.2.2.2 u')
  | read e p k ih =>
    intro a b c us ur h
    simp only [tr]
    exact ⟨h.1, h.2.1, fun y => ih y a b _ _ _ (h.2.2 y)⟩
  | draw β d k ih =>
    intro a b c us ur h
    simp only [tr]
    exact fun y => ih y a b _ _ _ (h y)

theorem runsLe_of_adm :
    ∀ (t : Env (L.pull σT σL σB) α) (c : ℕ) (us ur : ℕ → ℕ),
      t.Adm B ok c us ur → c ≤ B.nenc → RunsLe t (B.nenc - c) (left B us) := by
  intro t
  induction t with
  | stop x => intro _ _ _ _ _; trivial
  | fresh k ih =>
    intro c us ur h hc
    rw [show B.nenc - c = B.nenc - (c + 1) + 1 by have := h.1; omega]
    exact fun u => ih u (c + 1) us ur (h.2 u) h.1
  | session e J xs rest k ih =>
    intro c us ur h hc
    rw [left_step (h.1.trans hc) h.2.1]
    exact fun u => ih u c _ ur (h.2.2.2.2.2 u) hc
  | read e p k ih => exact fun c us ur h hc y => ih y c us _ (h.2.2 y) hc
  | draw β d k ih => exact fun c us ur h hc y => ih y c us ur (h y) hc

theorem left_zero (B : Bounds) : left B (fun _ => 0) = B.total := by
  unfold left Bounds.total
  simp

/-- the environment after the offline phase -/
def trE (E' : Sess (L.pull σT σL σB).offline → Env (L.pull σT σL σB) α) (a b : ℕ) :
    Sess L.offline → Env L (Option α) :=
  fun u => .draw _ (AdT u) fun o => match o with
    | none => .stop none
    | some u' => tr AdL AdB KL KB (E' u') a b

variable {AdT AdL AdB KT KL KB}

theorem expect_view (W : Laws L) (W' : Laws (L.pull σT σL σB)) (hL1 : 1 ≤ KL) (hLt : KL ≠ ⊤)
    (hB1 : 1 ≤ KB) (hBt : KB ≠ ⊤) (hT : ∀ r, Adapts (W.T r) (W'.T r) AdT KT)
    (hL : ∀ r r', Adapts (W.Lk r r') (W'.Lk r r') AdL KL)
    (hB : ∀ r J xs rest, Adapts (W.B r J xs rest) (W'.B r J xs rest) (AdB J) KB)
    (hy : ∀ r p, W'.y r p = W.y r p) (F : α → ℝ≥0∞)
    (E' : Sess (L.pull σT σL σB).offline → Env (L.pull σT σL σB) α) (a b : ℕ)
    (hE : ∀ u, RunsLe (E' u) a b) :
    KT * (KL ^ a * KB ^ b) * expect (W.host.view (trE AdT AdL AdB KL KB E' a b)) (lift F) =
      expect (W'.host.view E') F := by
  refine Eq.trans ?_ (congrArg (fun P => expect P F) (view_host W' E')).symm
  rw [view_host]
  unfold trE
  simp only [run_draw, expect_bind]
  rw [← expect_const_mul]
  refine expect_congr _ fun r => ?_
  exact (hT r).use _ _ _ (expect_pure _ _) fun u' =>
    expect_tr W W' hL1 hLt hB1 hBt hL hB hy F (E' u') a b _ (hE u')

/-- Under the hypotheses below, the distance of two pulled views is at most the factor times the
distance of the two views of the object, for the environment made from the pulled one. -/
theorem tv_view_pull (W V : Laws L) (W' V' : Laws (L.pull σT σL σB)) (hL1 : 1 ≤ KL) (hLt : KL ≠ ⊤)
    (hB1 : 1 ≤ KB) (hBt : KB ≠ ⊤) (hT : ∀ r, Adapts (W.T r) (W'.T r) AdT KT)
    (hL : ∀ r r', Adapts (W.Lk r r') (W'.Lk r r') AdL KL)
    (hB : ∀ r J xs rest, Adapts (W.B r J xs rest) (W'.B r J xs rest) (AdB J) KB)
    (hy : ∀ r p, W'.y r p = W.y r p) (gT : ∀ r, Adapts (V.T r) (V'.T r) AdT KT)
    (gL : ∀ r r', Adapts (V.Lk r r') (V'.Lk r r') AdL KL)
    (gB : ∀ r J xs rest, Adapts (V.B r J xs rest) (V'.B r J xs rest) (AdB J) KB)
    (gy : ∀ r p, V'.y r p = V.y r p) (E' : Sess (L.pull σT σL σB).offline → Env (L.pull σT σL σB) α)
    (a b : ℕ) (hE : ∀ u, RunsLe (E' u) a b) :
    tv (W'.host.view E') (V'.host.view E') ≤
      KT * (KL ^ a * KB ^ b) *
        tv (W.host.view (trE AdT AdL AdB KL KB E' a b))
          (V.host.view (trE AdT AdL AdB KL KB E' a b)) := by
  classical
  refine tv_le_of_forall_pr_le fun A => ?_
  rw [pr_eq_expect, pr_eq_expect, ← expect_view W W' hL1 hLt hB1 hBt hT hL hB hy _ E' a b hE,
    ← expect_view V V' hL1 hLt hB1 hBt gT gL gB gy _ E' a b hE, ← mul_add]
  refine mul_le_mul_right (expect_le_expect_add_tv _ _ fun o => ?_) _
  cases o with
  | none => exact zero_le _
  | some x =>
    show (if x ∈ A then (1 : ℝ≥0∞) else 0) ≤ 1
    split_ifs <;> simp

end Bounds

/-! ## Part 4. The adapters of the three kinds of runs -/

section Single
variable {Y : Type} {E : ExtSpec} {Q : InteractiveOracleProof Y E} {Wt : Type}

/-- the adapter of a run of one IOP -/
def adaptQ (Q : InteractiveOracleProof Y E) (σ : Samplers Q.shape) (K : ℝ≥0∞) :
    Sess Q → PMF (Option (Sess (Q.pull σ))) :=
  adapt (unif (Rho Q.shape))
    (unif (Rho (Q.shape.pull σ))) (Rho.push σ) K (Option.map (DView.pull σ))

theorem den_rho {σ : Samplers Q.shape} {κ K : ℝ≥0∞} (hσ : σ.Good κ K) (ρ : Rho Q.shape) :
    ((unif (Rho (Q.shape.pull σ))).map (Rho.push σ)) ρ ≤ K * (unif (Rho Q.shape)) ρ := by
  rw [← pr_singleton, ← pr_singleton, pr_map]
  exact prRho_preimage_le hσ {ρ}

theorem adapts_sess (H : Honest Q Wt) {σ : Samplers Q.shape} {κ K : ℝ≥0∞} (hσ : σ.Good κ K)
    (hK : K ≠ ⊤) (w : Wt) (y : Y) :
    Adapts (sess H w y) (sess (H.pull σ) w y) (adaptQ Q σ K) K := by
  have h := adapts_run hK (den_rho hσ) (H.output w y) (Option.map (DView.pull σ))
  have e : sess (H.pull σ) w y =
      (unif (Rho (Q.shape.pull σ))).bind fun ρ' =>
        (H.output w y (Rho.push σ ρ')).map fun o => (ρ', o.map (DView.pull σ)) := by
    unfold sess
    refine congrArg _ (funext fun ρ' => ?_)
    rw [Honest.output_pull, PMF.map_comp]
    rfl
  rw [e]
  exact h

theorem adapts_simSess (Sim : SimOf Q) {σ : Samplers Q.shape} {κ K : ℝ≥0∞} (hσ : σ.Good κ K)
    (hK : K ≠ ⊤) (y : Y) (str : E.Str) :
    Adapts (simSess Q Sim y str)
      (simSess (Q.pull σ) (Top.R0.simPull σ Sim) y str) (adaptQ Q σ K) K := by
  have h :=
    adapts_run hK (den_rho hσ) (fun ρ => Sim y ρ (Q.extAns y ρ str)) (Option.map (DView.pull σ))
  have e : simSess (Q.pull σ) (Top.R0.simPull σ Sim) y str =
      (unif (Rho (Q.shape.pull σ))).bind fun ρ' =>
        (Sim y (Rho.push σ ρ') (Q.extAns y (Rho.push σ ρ') str)).map fun o =>
            (ρ', o.map (DView.pull σ)) := by
    unfold simSess Top.R0.simPull
    refine congrArg _ (funext fun ρ' => ?_)
    rw [PMF.map_comp]
    rfl
  rw [e]
  exact h

end Single

section Batch
variable {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} {Wt : Type} {N : ℕ}

/-- the verifier messages of the slots of J -/
def vis (s : Shape) (A : RoundSplits s) (J : Finset (Fin N)) (ρ : BRho N s A) : J → Rho s := fun j =>
  ρ.slot j.1

/-- the adapter of a session in which the slots of J are shown -/
def adaptB (Q : BatchInteractiveOracleProof Y E) (σ : Samplers Q.loc.shape) (K : ℝ≥0∞) (J : Finset (Fin N)) :
    BSess Q J → PMF (Option (BSess (Q.pull σ) J)) :=
  adapt ((unif (BRho N Q.loc.shape Q.ann)).map (vis _ _ J))
    ((unif (BRho N (Q.loc.shape.pull σ) (Q.ann.pull σ))).map (vis _ _ J))
    (fun ρs j => Rho.push σ (ρs j)) K (fun f j => (f j).map (DView.pull σ))

theorem vis_push (σ : Samplers Q.loc.shape) (J : Finset (Fin N))
    (ρ' : BRho N (Q.loc.shape.pull σ) (Q.ann.pull σ)) :
    (fun j => Rho.push σ (vis _ _ J ρ' j)) = vis _ _ J (BRho.push σ ρ') :=
  funext fun j => (slot_push j.1 σ ρ').symm

theorem den_brho (hN : 0 < N) {σ : Samplers Q.loc.shape} {κ K : ℝ≥0∞} (hσ : σ.Good κ K)
    (J : Finset (Fin N)) (v : J → Rho Q.loc.shape) :
    (((unif (BRho N (Q.loc.shape.pull σ) (Q.ann.pull σ))).map (vis _ _ J)).map
        fun ρs j => Rho.push σ (ρs j)) v ≤
      K ^ N * ((unif (BRho N Q.loc.shape Q.ann)).map (vis _ _ J)) v := by
  rw [← pr_singleton, ← pr_singleton, pr_map, pr_map, pr_map]
  refine le_trans (le_of_eq ?_) (prBRho_preimage_le hN hσ (vis _ _ J ⁻¹' {v}))
  refine congrArg _ (Set.ext fun ρ' => ?_)
  show (fun j => Rho.push σ (vis _ _ J ρ' j)) = v ↔ vis _ _ J (BRho.push σ ρ') = v
  rw [vis_push]

theorem adapts_of_vis (hN : 0 < N) {σ : Samplers Q.loc.shape} {κ K : ℝ≥0∞} (hσ : σ.Good κ K)
    (hK : K ≠ ⊤) (J : Finset (Fin N))
    (ker : (J → Rho Q.loc.shape) → PMF (J → Option (DView Q.loc))) :
    Adapts ((unif (BRho N Q.loc.shape Q.ann)).bind fun ρ =>
        (ker (vis _ _ J ρ)).map fun o => (vis _ _ J ρ, o))
      ((unif (BRho N (Q.loc.shape.pull σ) (Q.ann.pull σ))).bind fun ρ' =>
        (ker (vis _ _ J (BRho.push σ ρ'))).map fun o =>
          (vis _ _ J ρ', fun j => (o j).map (DView.pull σ)))
      (adaptB Q σ (K ^ N) J) (K ^ N) := by
  have h :=
    adapts_run (ENNReal.pow_ne_top hK) (den_brho hN hσ J) ker (fun f j => (f j).map (DView.pull σ))
  rw [PMF.bind_map, PMF.bind_map] at h
  simp only [Function.comp_def, vis_push] at h
  exact h

theorem adapts_bsess (H : BatchHonestProver Q Wt) (hN : 0 < N) {σ : Samplers Q.loc.shape} {κ K : ℝ≥0∞}
    (hσ : σ.Good κ K) (hK : K ≠ ⊤) (w : Wt) (x : Fin N → Option Y) (J : Finset (Fin N)) :
    Adapts (bsess H w x J) (bsess (H.pull σ) w x J) (adaptB Q σ (K ^ N) J) (K ^ N) := by
  have h := adapts_of_vis hN hσ hK J fun ρs =>
    (unif (H.Coin0 × (Fin N → H.Coin))).map fun c =>
      fun j : J => slotOut H w (x j) (ρs j) (c.1, c.2 j)
  have e : bsess (H.pull σ) w x J = (unif (BRho N (Q.loc.shape.pull σ) (Q.ann.pull σ))).bind fun ρ' =>
      ((unif (H.Coin0 × (Fin N → H.Coin))).map fun c =>
            fun j : J => slotOut H w (x j) (vis _ _ J (BRho.push σ ρ') j) (c.1, c.2 j)).map
          fun o => (vis _ _ J ρ', fun j => (o j).map (DView.pull σ)) := by
    unfold bsess
    refine congrArg _ (funext fun ρ' => ?_)
    rw [output_pull, output_eq]
    refine ((congrArg _ (PMF.map_comp _ _ _)).trans (PMF.map_comp _ _ _)).trans ?_
    refine Eq.trans ?_ (PMF.map_comp _ _ _).symm
    rfl
  rw [e]
  exact h

theorem adapts_simBsess (Sim : BSimOf Q N) (hN : 0 < N) {σ : Samplers Q.loc.shape} {κ K : ℝ≥0∞}
    (hσ : σ.Good κ K) (hK : K ≠ ⊤) (J : Finset (Fin N)) (xs : J → Y) (str : E.Str) :
    Adapts (simBsess Q Sim J xs str) (simBsess (Q.pull σ) (simPullB σ Sim) J xs str)
      (adaptB Q σ (K ^ N) J) (K ^ N) := by
  have h := adapts_of_vis hN hσ hK J fun ρs => Sim J xs ρs (Q.extAnsJ J xs ρs str)
  have e : simBsess (Q.pull σ) (simPullB σ Sim) J xs str = (unif (BRho N (Q.loc.shape.pull σ) (Q.ann.pull σ))).bind fun ρ' =>
      (Sim J xs (vis _ _ J (BRho.push σ ρ')) (Q.extAnsJ J xs (vis _ _ J (BRho.push σ ρ')) str)).map
          fun o => (vis _ _ J ρ', fun j => (o j).map (DView.pull σ)) := by
    unfold simBsess simPullB
    refine congrArg _ (funext fun ρ' => ?_)
    rw [PMF.map_comp, ← vis_push]
    rfl
  rw [e]
  exact h

end Batch

/-! ## Part 5. The theorem -/

section Main
variable {I X : Type}

/-- the run simulators of the pulled interface: run the old ones at the pushed verifier messages
and carry their outputs over -/
def simsPull (L : BatchProtocol I X) (σT : Samplers L.offline.shape) (σL : Samplers L.link.shape)
    (σB : Samplers L.onlineBatch.loc.shape) (Sm : Sims L) : Sims (L.pull σT σL σB) :=
  ⟨Top.R0.simPull σT Sm.T, Top.R0.simPull σL Sm.Lk, simPullB σB Sm.B⟩

/-- the factor: one offline run, at most nenc links, at most Σ_j sess j sessions -/
def factor (B : Bounds) (N : ℕ) (KT KL KB : ℝ≥0∞) : ℝ≥0∞ := KT * (KL ^ B.nenc * (KB ^ N) ^ B.total)

namespace Spec

/-- Under the hypotheses below, honest-verifier zero knowledge of the whole object is kept when
verifier messages are made by samplers, as a black box: nothing is asked of L but HVZKWhole and
`0 < L.maxBatchSize`; the error z becomes `factor B L.maxBatchSize KT KL KB * z` (the head, Limits). -/
def hvzk_pull : Prop :=
  ∀ (I X : Type) (L : BatchProtocol I X) (σT : Samplers L.offline.shape) (σL : Samplers L.link.shape)
      (σB : Samplers L.onlineBatch.loc.shape) (κ KT KL KB : ℝ≥0∞),
    σT.Good κ KT → σL.Good κ KL → σB.Good κ KB → KT ≠ ⊤ → 1 ≤ KL → KL ≠ ⊤ →
    1 ≤ KB → KB ≠ ⊤ → 0 < L.maxBatchSize →
    ∀ (Ryes : I → X → Prop) (B : Bounds) (Sm : Sims L) (i₀ : I) (z : ℝ≥0∞),
      HVZKWhole L Ryes B (simWhole L Sm i₀) z →
      HVZKWhole (L.pull σT σL σB) Ryes B
        (simWhole (L.pull σT σL σB) (simsPull L σT σL σB Sm) i₀) (factor B L.maxBatchSize KT KL KB * z)

end Spec

theorem hvzk_pull : Spec.hvzk_pull := by
  intro I X L σT σL σB κ KT KL KB hT hL hB hTt hL1 hLt hB1 hBt hN Ryes B Sm i₀ z hz i α E' hE'
  have h := tv_view_pull (AdT := adaptQ L.offline σT KT) (AdL := adaptQ L.link σL KL)
    (AdB := fun J => adaptB L.onlineBatch σB (KB ^ L.maxBatchSize) J) (KT := KT) (KL := KL) (KB := KB ^ L.maxBatchSize)
    (realLaws L i) (simLaws L Sm i₀) (realLaws (L.pull σT σL σB) i)
    (simLaws (L.pull σT σL σB) (simsPull L σT σL σB Sm) i₀)
    hL1 hLt (one_le_pow₀ hB1) (ENNReal.pow_ne_top hBt)
    (fun r => adapts_sess L.honestOfflineProver hT hTt (i, r) ()) (fun r r' => adapts_sess L.honestLinkProver hL hLt (i, r, r') ())
    (fun r J xs rest => adapts_bsess L.honestOnlineBatchProver hN hB hBt (i, r) (vec J xs rest) J) (fun _ _ => rfl)
    (fun r => adapts_simSess Sm.T hT hTt () (L.encodeIndex i₀ r))
    (fun r r' => adapts_simSess Sm.Lk hL hLt () (L.encodeIndex i₀ r, L.encodeIndex i₀ r'))
    (fun r J xs _ => adapts_simBsess Sm.B hN hB hBt J xs (L.encodeIndex i₀ r)) (fun _ _ => rfl)
    E' B.nenc B.total (fun u => by
      have := runsLe_of_adm (E' u) 0 _ _ (hE' u) (Nat.zero_le _)
      rwa [Nat.sub_zero, left_zero] at this)
  have hadm : ∀ u,
      (trE (adaptQ L.offline σT KT) (adaptQ L.link σL KL) (fun J => adaptB L.onlineBatch σB (KB ^ L.maxBatchSize) J) KL
          (KB ^ L.maxBatchSize) E' B.nenc B.total u).Adm
        B (Ryes i) 0 (fun _ => 0) fun _ => 0 := by
    intro u
    unfold trE
    intro o
    cases o with
    | none => trivial
    | some u' => exact adm_tr _ _ _ _ (E' u') _ _ _ _ _ (hE' u')
  exact h.trans (mul_le_mul_right (hz i (Option α) _ hadm) _)

/-- The same for the interface whose verifier messages are made from λ-bit blocks (L.draws dr),
with the run simulators simsD of Top/ProgDraw.lean: K = κ₀^n, κ₀ the bias of a block and n a bound
on the blocks of all rounds of a protocol. (not all hypotheses are named here: see the statement
below) -/
theorem hvzk_draws (lam : ℕ) (L : BatchProtocol I X) (dr : L.Draws lam) (κ₀ : ℝ≥0∞) (n : ℕ) (h1 : 1 ≤ κ₀)
    (hκ : κ₀ ≠ ⊤) (hg : dr.Good κ₀) (hr : dr.TotLe n) (hN : 0 < L.maxBatchSize) (Ryes : I → X → Prop)
    (B : Bounds) (Sm : Sims L) (i₀ : I) (z : ℝ≥0∞) (hz : HVZKWhole L Ryes B (simWhole L Sm i₀) z) :
    HVZKWhole (L.draws dr) Ryes B (simWhole (L.draws dr) (Top.ProgDraw.simsD lam L dr Sm) i₀)
      (factor B L.maxBatchSize (κ₀ ^ n) (κ₀ ^ n) (κ₀ ^ n) * z) :=
  hvzk_pull I X L _ _ _ (κ₀ ^ dr.K) (κ₀ ^ n) (κ₀ ^ n) (κ₀ ^ n)
    (drawsGood lam κ₀ h1 _ dr.T hg.1 dr.K n (le_max_left _ _) hr.1)
    (drawsGood lam κ₀ h1 _ dr.Lk hg.2.1 dr.K n
      (le_trans (le_max_left _ _) (le_max_right _ _)) hr.2.1)
    (drawsGood lam κ₀ h1 _ dr.B hg.2.2 dr.K n
      (le_trans (le_max_right _ _) (le_max_right _ _)) hr.2.2)
    (ENNReal.pow_ne_top hκ) (one_le_pow₀ h1) (ENNReal.pow_ne_top hκ) (one_le_pow₀ h1)
    (ENNReal.pow_ne_top hκ) hN Ryes B Sm i₀ z hz

end Main

end Hiop.Pull
