-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/Seeded/GameProof.lean: proofs of the statements of Hiop/Seeded/Game.lean.

 Part 1: from an adversary against the game of a host to an environment of Hiop/Seeded/Form.lean:
   its coins and the lazily sampled oracle answers are coins of the environment; a call that the
   game refuses is skipped, by the game's own test (`envOf`; before the first encoded index:
   `preOf`).
 Part 2: the game with that adversary is the experiment with that environment: an equality of laws,
   for every host (`run_envOf`, `run_preOf`).
 Part 3: the environment keeps the bounds, since the test is in it (`adm_envOf`, `adm_preOf`).
   So `game_of_view`.
 Part 4: runs with an auxiliary value: a real run is near its simulated run (`tv_runAt_le`); how
   many positions a simulated run reads; so `lifeSeeded`, by `form_laws`
   (Hiop/Seeded/FormProof.lean).

Limits: see the heads of Hiop/Seeded/Game.lean and Hiop/Seeded/Whole.lean.
Terms: lean/GLOSSARY.md.

-/
import Hiop.Seeded.Game
import Hiop.Seeded.FormProof

set_option autoImplicit false

noncomputable section

namespace Hiop.Seeded
open Prob Iop Rom Compile.Lifetime
open scoped ENNReal

variable {I X : Type} {L : HolographicProtocol I X} {F : Form X} {S : OSpec} {α : Type}

/-! ## Part 1. From an adversary to an environment -/

open Classical in
/-- After the first encoded index. c, u: the game's counts; T: the table of the oracle answers given
so far. -/
def envOf (B : BoundsR) (Gs : L.OutOfDomainSeed → Prop) :
    Adv S (GOut L F) (GIn L F) α → ℕ → UsedR → Table S → EnvF L F α
  | .halt a, _, _, _ => .stop a
  | .sample n k, c, u, T =>
    .draw (Fin (n + 1)) (PMF.uniformOfFintype (Fin (n + 1))) fun r => envOf B Gs (k r) c u T
  | .query o q k, c, u, T =>
    .draw (S.Rng o × Table S) (lazyAnswer T o q) fun y => envOf B Gs (k y.1) c u y.2
  | .call (.table s) k, c, u, T =>
    if Gs s ∧ c < B.nenc then .fresh s fun a => envOf B Gs (k (.ood a)) (c + 1) u T
    else envOf B Gs (k .none) c u T
  | .call (.test e) k, c, u, T =>
    if e ≤ c ∧ u.tests e < B.tests e then
      .test e fun a => envOf B Gs (k (.test a)) c { u with tests := bump u.tests e } T
    else envOf B Gs (k .none) c u T
  | .call (.link e) k, c, u, T =>
    if 1 ≤ e ∧ e ≤ c ∧ u.links e < B.links e then
      .link e fun a => envOf B Gs (k (.link a)) c { u with links := bump u.links e } T
    else envOf B Gs (k .none) c u T
  | .call (.sess e q h) k, c, u, T =>
    if e ≤ c ∧ u.sess e < B.sess e ∧ F.wt q ≤ B.shown then
      .session e q h fun a => envOf B Gs (k (.sess q a)) c { u with sess := bump u.sess e } T
    else envOf B Gs (k .none) c u T
  | .call (.read e p) k, c, u, T =>
    if e ≤ c ∧ u.reads e < B.reads e then
      .read e p fun y => envOf B Gs (k (.sym y)) c { u with reads := bump u.reads e } T
    else envOf B Gs (k .none) c u T

open Classical in
/-- Before the first encoded index. -/
def preOf (B : BoundsR) (Gs : L.OutOfDomainSeed → Prop) :
    Adv S (GOut L F) (GIn L F) α → Table S → PreF L F α
  | .halt a, _ => .stop a
  | .sample n k, T =>
    .draw (Fin (n + 1)) (PMF.uniformOfFintype (Fin (n + 1))) fun r => preOf B Gs (k r) T
  | .query o q k, T =>
    .draw (S.Rng o × Table S) (lazyAnswer T o q) fun y => preOf B Gs (k y.1) y.2
  | .call (.table s) k, T =>
    if Gs s then .first s fun a => envOf B Gs (k (.ood a)) 0 UsedR.zero T
    else preOf B Gs (k .none) T
  | .call (.test _) k, T => preOf B Gs (k .none) T
  | .call (.link _) k, T => preOf B Gs (k .none) T
  | .call (.sess _ _ _) k, T => preOf B Gs (k .none) T
  | .call (.read _ _) k, T => preOf B Gs (k .none) T

/-! ## Part 2. The game is the experiment -/

section Run
variable (H : HostF L F) (B : BoundsR) (Gs : L.OutOfDomainSeed → Prop)

/-- one call of the game, then the rest -/
theorem interact_call (m : GOut L F) (k : GIn L F → Adv S (GOut L F) (GIn L F) α) (s : GSt H)
    (T : Table S) :
    (interact (gameW H B Gs S) (.call m k) (s, T)).map Prod.fst =
      (gameReply H B Gs s m).bind fun p =>
        (interact (gameW H B Gs S) (k p.1) (p.2, T)).map Prod.fst := by
  show (((gameReply H B Gs s m).map fun p => (p.1, (p.2, T))).bind fun p =>
    interact (gameW H B Gs S) (k p.1) p.2).map Prod.fst = _
  rw [PMF.map_bind, PMF.bind_map]
  rfl

theorem interact_query (o : S.ι) (q : S.Dom o) (k : S.Rng o → Adv S (GOut L F) (GIn L F) α)
    (s : GSt H) (T : Table S) :
    (interact (gameW H B Gs S) (.query o q k) (s, T)).map Prod.fst =
      (lazyAnswer T o q).bind fun y =>
        (interact (gameW H B Gs S) (k y.1) (s, y.2)).map Prod.fst := by
  show (((lazyAnswer T o q).map fun a => (a.1, (s, a.2))).bind fun p =>
    interact (gameW H B Gs S) (k p.1) p.2).map Prod.fst = _
  rw [PMF.map_bind, PMF.bind_map]
  rfl

theorem interact_sample (n : ℕ) (k : Fin (n + 1) → Adv S (GOut L F) (GIn L F) α) (s : GSt H)
    (T : Table S) :
    (interact (gameW H B Gs S) (.sample n k) (s, T)).map Prod.fst =
      (PMF.uniformOfFintype (Fin (n + 1))).bind fun r =>
        (interact (gameW H B Gs S) (k r) (s, T)).map Prod.fst := by
  show ((PMF.uniformOfFintype (Fin (n + 1))).bind fun r =>
    interact (gameW H B Gs S) (k r) (s, T)).map Prod.fst = _
  rw [PMF.map_bind]

theorem interact_halt (a : α) (s : GSt H) (T : Table S) :
    (interact (gameW H B Gs S) (.halt a : Adv S (GOut L F) (GIn L F) α) (s, T)).map Prod.fst =
      PMF.pure a := by
  show (PMF.pure (a, (s, T))).map Prod.fst = _
  rw [PMF.pure_map]

theorem run_envOf (A : Adv S (GOut L F) (GIn L F) α) :
    ∀ (c : ℕ) (u : UsedR) (st : H.σ) (T : Table S),
      (interact (gameW H B Gs S) A (some (c, u, st), T)).map Prod.fst =
        (envOf B Gs A c u T).run H st := by
  induction A with
  | halt a => intro c u st T; exact interact_halt H B Gs a _ T
  | sample n k ih =>
    intro c u st T
    rw [interact_sample]
    exact congrArg _ (funext fun r => ih r c u st T)
  | query o q k ih =>
    intro c u st T
    rw [interact_query]
    exact congrArg _ (funext fun y => ih y.1 c u st y.2)
  | call m k ih =>
    intro c u st T
    rw [interact_call]
    cases m with
    | table s =>
      by_cases h : Gs s ∧ c < B.nenc
      · simp only [gameReply, envOf, if_pos h, PMF.bind_map, Function.comp_def]
        exact congrArg _ (funext fun p => ih _ _ _ _ _)
      · simp only [gameReply, envOf, if_neg h, PMF.pure_bind]
        exact ih _ _ _ _ _
    | test e =>
      by_cases h : e ≤ c ∧ u.tests e < B.tests e
      · simp only [gameReply, envOf, if_pos h, PMF.bind_map, Function.comp_def]
        exact congrArg _ (funext fun p => ih _ _ _ _ _)
      · simp only [gameReply, envOf, if_neg h, PMF.pure_bind]
        exact ih _ _ _ _ _
    | link e =>
      by_cases h : 1 ≤ e ∧ e ≤ c ∧ u.links e < B.links e
      · simp only [gameReply, envOf, if_pos h, PMF.bind_map, Function.comp_def]
        exact congrArg _ (funext fun p => ih _ _ _ _ _)
      · simp only [gameReply, envOf, if_neg h, PMF.pure_bind]
        exact ih _ _ _ _ _
    | sess e q hq =>
      by_cases h : e ≤ c ∧ u.sess e < B.sess e ∧ F.wt q ≤ B.shown
      · simp only [gameReply, envOf, if_pos h, PMF.bind_map, Function.comp_def]
        exact congrArg _ (funext fun p => ih _ _ _ _ _)
      · simp only [gameReply, envOf, if_neg h, PMF.pure_bind]
        exact ih _ _ _ _ _
    | read e p =>
      by_cases h : e ≤ c ∧ u.reads e < B.reads e
      · simp only [gameReply, envOf, if_pos h, PMF.bind_map, Function.comp_def]
        exact congrArg _ (funext fun p => ih _ _ _ _ _)
      · simp only [gameReply, envOf, if_neg h, PMF.pure_bind]
        exact ih _ _ _ _ _

theorem run_preOf (A : Adv S (GOut L F) (GIn L F) α) :
    ∀ T : Table S,
      (interact (gameW H B Gs S) A (none, T)).map Prod.fst = (preOf B Gs A T).run H := by
  induction A with
  | halt a => intro T; exact interact_halt H B Gs a _ T
  | sample n k ih =>
    intro T
    rw [interact_sample]
    exact congrArg _ (funext fun r => ih r T)
  | query o q k ih =>
    intro T
    rw [interact_query]
    exact congrArg _ (funext fun y => ih y.1 y.2)
  | call m k ih =>
    intro T
    rw [interact_call]
    cases m with
    | table s =>
      by_cases h : Gs s
      · simp only [gameReply, preOf, if_pos h, PMF.bind_map, Function.comp_def]
        exact congrArg _ (funext fun p => run_envOf H B Gs _ _ _ _ _)
      · simp only [gameReply, preOf, if_neg h, PMF.pure_bind]
        exact ih _ _
    | test e =>
      simp only [gameReply, preOf, PMF.pure_bind]
      exact ih _ _
    | link e =>
      simp only [gameReply, preOf, PMF.pure_bind]
      exact ih _ _
    | sess e q hq =>
      simp only [gameReply, preOf, PMF.pure_bind]
      exact ih _ _
    | read e p =>
      simp only [gameReply, preOf, PMF.pure_bind]
      exact ih _ _

end Run

/-! ## Part 3. The environment keeps the bounds -/

section Adm
variable {B : BoundsR} {Gs : L.OutOfDomainSeed → Prop} {ok : X → Prop}

theorem adm_envOf (A : Adv S (GOut L F) (GIn L F) α) :
    ∀ (c : ℕ) (u : UsedR) (T : Table S), A.CallsOK (okCall ok) →
      (envOf B Gs A c u T).Adm B Gs ok c u := by
  induction A with
  | halt a => intro _ _ _ _; exact trivial
  | sample n k ih => intro c u T hA r; exact ih r c u T (hA r)
  | query o q k ih => intro c u T hA y; exact ih y.1 c u y.2 (hA y.1)
  | call m k ih =>
    intro c u T hA
    cases m with
    | table s =>
      by_cases h : Gs s ∧ c < B.nenc
      · simp only [envOf, if_pos h]
        exact ⟨h.1, h.2, fun a => ih _ _ _ _ (hA.2 _)⟩
      · simp only [envOf, if_neg h]
        exact ih _ _ _ _ (hA.2 _)
    | test e =>
      by_cases h : e ≤ c ∧ u.tests e < B.tests e
      · simp only [envOf, if_pos h]
        exact ⟨h.1, h.2, fun a => ih _ _ _ _ (hA.2 _)⟩
      · simp only [envOf, if_neg h]
        exact ih _ _ _ _ (hA.2 _)
    | link e =>
      by_cases h : 1 ≤ e ∧ e ≤ c ∧ u.links e < B.links e
      · simp only [envOf, if_pos h]
        exact ⟨h.1, h.2.1, h.2.2, fun a => ih _ _ _ _ (hA.2 _)⟩
      · simp only [envOf, if_neg h]
        exact ih _ _ _ _ (hA.2 _)
    | sess e q hq =>
      by_cases h : e ≤ c ∧ u.sess e < B.sess e ∧ F.wt q ≤ B.shown
      · simp only [envOf, if_pos h]
        exact ⟨h.1, h.2.1, h.2.2, hA.1, fun a => ih _ _ _ _ (hA.2 _)⟩
      · simp only [envOf, if_neg h]
        exact ih _ _ _ _ (hA.2 _)
    | read e p =>
      by_cases h : e ≤ c ∧ u.reads e < B.reads e
      · simp only [envOf, if_pos h]
        exact ⟨h.1, h.2, fun y => ih _ _ _ _ (hA.2 _)⟩
      · simp only [envOf, if_neg h]
        exact ih _ _ _ _ (hA.2 _)

theorem adm_preOf (A : Adv S (GOut L F) (GIn L F) α) :
    ∀ T : Table S, A.CallsOK (okCall ok) → (preOf B Gs A T).Adm B Gs ok := by
  induction A with
  | halt a => intro _ _; exact trivial
  | sample n k ih => intro T hA r; exact ih r T (hA r)
  | query o q k ih => intro T hA y; exact ih y.1 y.2 (hA y.1)
  | call m k ih =>
    intro T hA
    cases m with
    | table s =>
      by_cases h : Gs s
      · simp only [preOf, if_pos h]
        exact ⟨h, fun a => adm_envOf _ _ _ _ (hA.2 _)⟩
      · simp only [preOf, if_neg h]
        exact ih _ _ (hA.2 _)
    | test e => simp only [preOf]; exact ih _ _ (hA.2 _)
    | link e => simp only [preOf]; exact ih _ _ (hA.2 _)
    | sess e q hq => simp only [preOf]; exact ih _ _ (hA.2 _)
    | read e p => simp only [preOf]; exact ih _ _ (hA.2 _)

end Adm

/-- From the property to the two games. -/
theorem game_of_view : Spec.game_of_view := by
  intro S I X L F H Gs ok B Sim z hV α A hA
  rw [run_preOf, run_preOf]
  exact hV.pre _ (adm_preOf A _ hA)

/-! ## Part 4. Runs with an auxiliary value -/

section One
variable {Y : Type} {E : ExtSpec} {Q : InteractiveOracleProof Y E} {Wt A : Type}

open Classical in
/-- A run and its simulated counterpart are within the probability, over the auxiliary value, that
the verifier's randomness read off it is a value at which honest output and simulator differ. -/
theorem tv_runAt_le (H : Honest Q Wt) (Sim : SimOf Q) (μ : PMF A) (ρ : A → Option (Rho Q.shape))
    (w : Wt) (y : Y) {z : ℝ≥0∞}
    (h : pr μ {a | ∃ r, ρ a = some r ∧
      H.output w y r ≠ Sim y r (Q.extAns y r (H.ext w))} ≤ z) :
    tv (runAt H μ ρ w y) ((simAt Q Sim μ ρ y).law (E.rd (H.ext w))) ≤ z := by
  refine (tv_bind_right_le_pr_ne _ _ _).trans (le_trans (pr_mono _ ?_) h)
  intro a ha
  cases hρ : ρ a with
  | none =>
    refine absurd ?_ ha
    show showAt a (ρ a) _ = showAt a (ρ a) _
    rw [hρ]
    rfl
  | some r =>
    refine ⟨r, hρ, fun hEq => ha ?_⟩
    show showAt a (ρ a) _ = showAt a (ρ a) _
    rw [hρ]
    show (H.output w y r).map _ = PMF.map _ _
    rw [hEq]
    show _ = (Sim y r fun p =>
      if p ∈ (ρ a).elim ∅ (Q.extReads y) then some (E.rd (H.ext w) p) else none).map _
    rw [hρ]
    rfl

/-- What holds of the empty set and of every set of positions that the verifier reads holds of the
positions that the simulated run reads. -/
theorem reads_simAt (Sim : SimOf Q) (μ : PMF A) (ρ : A → Option (Rho Q.shape)) (y : Y)
    (P : Finset E.Pos → Prop) (h0 : P ∅) (h1 : ∀ r, P (Q.extReads y r)) (a : A) :
    P ((simAt Q Sim μ ρ y).reads a) := by
  show P ((ρ a).elim ∅ (Q.extReads y))
  cases ρ a with
  | none => exact h0
  | some r => exact h1 r

end One

theorem counts_simsFG {Gs : L.OutOfDomainSeed → Prop} {b qT qpar qch qon : ℕ}
    (hR : ReadsG L Gs b qT qpar qch qon) (K : Kit L) (Sm : SimsG L) :
    (simsFG L K Sm).Counts qT qpar qch qon where
  cntT := fun e x a =>
    reads_simAt (Sm.T e) (K.μT e x) K.ρT x (fun T => T.card ≤ qT) (Nat.zero_le _) (hR.cntT x) a
  cntLp := fun e x a =>
    reads_simAt (Sm.Lk e) (K.μL e x) K.ρL x (fun T => (T.filter fun p => p.isLeft).card ≤ qpar)
      (Nat.zero_le _) (hR.cntLp x) a
  cntLc := fun e x a =>
    reads_simAt (Sm.Lk e) (K.μL e x) K.ρL x (fun T => (T.filter fun p => p.isRight).card ≤ qch)
      (Nat.zero_le _) (hR.cntLc x) a
  cntB := fun e x rc a =>
    reads_simAt (Sm.B e) (K.μB e (x, rc)) K.ρB (x, rc) (fun T => T.card ≤ qon) (Nat.zero_le _)
      (hR.cntO (x, rc)) a

/-- The real side with the honest sides P is near simulators that are good for P. -/
theorem near_realG {K : Kit L} {Gs : L.OutOfDomainSeed → Prop} {Ryes : I → X → Prop} {zT zL zO : ℝ≥0∞}
    {P : RecsG L} (hX : P.Ext) {Sm : SimsG L} (hS : Sm.Good K P Gs Ryes zT zL zO) (i : I) :
    (realLawsG L K P i).Near (simsFG L K Sm) Gs i (Ryes i) zT zL zO where
  rc := fun _ => rfl
  y := fun _ _ => rfl
  T := fun e u hu => by
    have h0 := hS.goodT e i u.1 u.2 hu
    rw [← hX.extT e i u.1 u.2] at h0
    have h1 := tv_runAt_le (P.T e) (Sm.T e) (K.μT e (L.recOf i u.1 u.2)) K.ρT (i, u.1, u.2)
      (L.recOf i u.1 u.2) h0
    rw [hX.extT] at h1
    exact h1
  Lk := fun e u u' hu hu' => by
    obtain ⟨r, s⟩ := u
    obtain ⟨r', s'⟩ := u'
    have h0 := hS.goodL e i r s r' s' hu hu'
    rw [← hX.extL e i r s r' s'] at h0
    have h1 := tv_runAt_le (P.Lk e) (Sm.Lk e) (K.μL e (L.recOf i r s, L.recOf i r' s')) K.ρL
      (i, (r, s), (r', s')) (L.recOf i r s, L.recOf i r' s') h0
    rw [hX.extL] at h1
    exact h1
  B := fun e u x _ hu hx => by
    have h0 := hS.goodB e i u.1 u.2 x hu hx
    rw [← hX.extB e i u.1 u.2] at h0
    have h1 := tv_runAt_le (P.B e) (Sm.B e) (K.μB e (x, L.recOf i u.1 u.2)) K.ρB (i, u.1, u.2)
      (x, L.recOf i u.1 u.2) h0
    rw [hX.extB] at h1
    refine h1.trans (le_of_eq ?_)
    show zO = ((1 : ℕ) : ℝ≥0∞) * zO
    rw [Nat.cast_one, one_mul]

/-- The real game and the simulated game are within the error of the bounds. (not all hypotheses are
named here: see `Spec.lifeSeeded`) -/
theorem lifeSeeded : Spec.lifeSeeded := by
  intro S I X L K Gs Ryes b qT qpar qch qon zT zL zO hR P hX Sm hS B hB i i₀ α A hA
  exact game_of_view S I X L K.form (realLawsG L K P i).host Gs (Ryes i) B
    (simWholeF L K.form (simsFG L K Sm) i₀) (B.err zT zL zO)
    (form_laws I X L K.form Gs (Ryes i) b qT qpar qch qon zT zL zO hR.hidE (simsFG L K Sm)
      (counts_simsFG hR K Sm) (realLawsG L K P i) i (near_realG hX hS i) B hB i₀) α A hA

end Hiop.Seeded

#print axioms Hiop.Seeded.game_of_view
#print axioms Hiop.Seeded.lifeSeeded
