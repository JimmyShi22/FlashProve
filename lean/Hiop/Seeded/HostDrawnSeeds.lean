-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/Seeded/HostDrawnSeeds.lean: the experiment of Hiop/RecWhole.lean, in which the host draws each seed, as a
case of the experiment of Hiop/Seeded/Whole.lean, in which the environment names it.

Definitions, statements and proofs. Two guards: they show that the statements of
Hiop/Seeded/Whole.lean say no less than the older one.
  `rec_hvzk_whole_again`: a second proof of `Hiop.Spec.rec_hvzk_whole` (Hiop/RecWhole.lean), from
    `whole_provers`: the provers are the object's own fields at every number, the simulators of runs
    are the same at every number, Gs is the set of all seeds, and the environment draws a uniform
    seed by itself before each encoded index (`liftU`). Of `HolographicProtocol.WiredR` it uses the three clauses on
    external strings and not the clause on the index decoder.
  `whole_fixed`: for every fixed list of seeds σ and every environment of the older type: the
    encoded index number e is made at the seed σ e (`liftAt`).

Limits: see the head of Hiop/Seeded/Whole.lean.
Terms: lean/GLOSSARY.md.

-/
import Hiop.Seeded.WholeProof

set_option autoImplicit false

noncomputable section

namespace Hiop.Seeded
open Prob Iop Compile.Lifetime Compile.BatchLife
open scoped ENNReal

variable {I X : Type} {L : HolographicProtocol I X} {α : Type}

/-! ## 1. Uniform seeds -/

/-- An environment of Hiop/RecWhole.lean as an environment that names the seeds: before each further
encoded index it draws a uniform seed. -/
def liftU : EnvR L α → EnvS L α
  | .stop a => .stop a
  | .fresh k => .draw L.OutOfDomainSeed (unif L.OutOfDomainSeed) fun s => .fresh s fun a => liftU (k a)
  | .test e k => .test e fun a => liftU (k a)
  | .link e k => .link e fun a => liftU (k a)
  | .session e J xs rest k => .session e J xs rest fun a => liftU (k a)
  | .read e p k => .read e p fun y => liftU (k y)
  | .draw β d k => .draw β d fun y => liftU (k y)

/-- Laws that are not told the number of the encoded index. -/
def lawsOfR (W : LawsR L) : LawsS L := ⟨W.rc, fun _ => W.T, fun _ => W.Lk, fun _ => W.B, W.y⟩

/-- The same simulators of runs at every number. -/
def simsOfR (Sm : SimsR L) : SimsS L := ⟨fun _ => Sm.T, fun _ => Sm.Lk, fun _ => Sm.B⟩

theorem real_own (i : I) : realLawsS L (ProversS.own L) i = lawsOfR (realLawsR L i) := rfl
theorem sim_ofR (Sm : SimsR L) (i₀ : I) :
    simLawsS L (simsOfR Sm) i₀ = lawsOfR (simLawsR L Sm i₀) := rfl

/-- A uniform pair: first the seed, then the committer's randomness. -/
theorem unif_pair_bind {γ : Type} (F : L.EncodingRandomness × L.OutOfDomainSeed → PMF γ) :
    (unif (L.EncodingRandomness × L.OutOfDomainSeed)).bind F =
      (unif L.OutOfDomainSeed).bind fun s => (unif L.EncodingRandomness).bind fun r => F (r, s) := by
  calc
    (unif (L.EncodingRandomness × L.OutOfDomainSeed)).bind F =
        (Prob.prod (unif L.EncodingRandomness) (unif L.OutOfDomainSeed)).bind fun x => F (x.1, x.2) := by
      rw [unif_prod]
    _ = (unif L.EncodingRandomness).bind fun r => (unif L.OutOfDomainSeed).bind fun s => F (r, s) :=
      (bind_bind_eq_prod_bind _ _ fun r s => F (r, s)).symm
    _ = _ := Prob.bind_comm _ _ _

theorem run_liftU (W : LawsR L) (t : EnvR L α) :
    ∀ st : StR L, (liftU t).run (lawsOfR W).host st = t.run W.host st := by
  induction t with
  | stop a => intro st; rfl
  | draw β d k ih =>
    intro st
    show (d.bind fun y => (liftU (k y)).run (lawsOfR W).host st) =
      d.bind fun y => (k y).run W.host st
    exact congrArg _ (funext fun y => ih y st)
  | fresh k ih =>
    intro st
    obtain ⟨c, f⟩ := st
    rw [runR_fresh, unif_pair_bind]
    show ((unif L.OutOfDomainSeed).bind fun s =>
      (EnvS.fresh s fun a => liftU (k a)).run (lawsOfR W).host (c, f)) = _
    refine congrArg _ (funext fun s => ?_)
    rw [runS_fresh]
    exact congrArg _ (funext fun r => ih _ _)
  | test e k ih =>
    intro st
    rw [runR_test]
    show (EnvS.test e fun a => liftU (k a)).run (lawsOfR W).host st = _
    rw [runS_test]
    exact congrArg _ (funext fun a => ih a st)
  | link e k ih =>
    intro st
    rw [runR_link]
    show (EnvS.link e fun a => liftU (k a)).run (lawsOfR W).host st = _
    rw [runS_link]
    exact congrArg _ (funext fun a => ih a st)
  | session e J xs rest k ih =>
    intro st
    rw [runR_session]
    show (EnvS.session e J xs rest fun a => liftU (k a)).run (lawsOfR W).host st = _
    rw [runS_session]
    exact congrArg _ (funext fun a => ih a st)
  | read e p k ih =>
    intro st
    rw [runR_read]
    show (EnvS.read e p fun y => liftU (k y)).run (lawsOfR W).host st = _
    rw [runS_read]
    exact ih _ st

/-- The older experiment is the new one with a uniform first seed and the lifted environment. -/
theorem view_liftU (W : LawsR L) (E : L.Rec → EnvR L α) :
    W.host.view E =
      (unif L.OutOfDomainSeed).bind fun s₀ => (lawsOfR W).host.view s₀ fun a => liftU (E a) := by
  rw [viewR_host, unif_pair_bind]
  refine congrArg _ (funext fun s => ?_)
  rw [viewS_host]
  exact congrArg _ (funext fun r => (run_liftU W _ _).symm)

theorem adm_liftU {B : BoundsR} {ok : X → Prop} (t : EnvR L α) :
    ∀ (c : ℕ) (u : UsedR), t.Adm B ok c u → (liftU t).Adm B (fun _ => True) ok c u := by
  induction t with
  | stop a => intro _ _ _; exact trivial
  | draw β d k ih => intro c u h y; exact ih y c u (h y)
  | fresh k ih => intro c u h s; exact ⟨trivial, h.1, fun a => ih a (c + 1) u (h.2 a)⟩
  | test e k ih => intro c u h; exact ⟨h.1, h.2.1, fun a => ih a c _ (h.2.2 a)⟩
  | link e k ih => intro c u h; exact ⟨h.1, h.2.1, h.2.2.1, fun a => ih a c _ (h.2.2.2 a)⟩
  | session e J xs rest k ih =>
    intro c u h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun a => ih a c _ (h.2.2.2.2.2 a)⟩
  | read e p k ih => intro c u h; exact ⟨h.1, h.2.1, fun y => ih y c _ (h.2.2 y)⟩

/-- The statement `Hiop.Spec.rec_hvzk_whole`, from the one with named seeds. -/
theorem rec_hvzk_whole_again : Hiop.Spec.rec_hvzk_whole := by
  intro I X L Ryes b qT qpar qch qon zT zL zO hW hR Sm hS B hB i₀ i α E hE
  have hV := whole_provers I X L (fun _ => True) Ryes b qT qpar qch qon zT zL zO (readsS_iff.2 hR)
    (ProversS.own L) ⟨fun _ => hW.extT, fun _ => hW.extL, fun _ => hW.extB⟩ (simsOfR Sm)
    ⟨fun _ w x hv _ => hS.goodT w x hv, fun _ w x hv _ _ => hS.goodL w x hv,
      fun _ w x _ hv J xs hx => hS.goodB w x hv J xs hx⟩ B hB i₀ i
  rw [realHostR_eq, simHostR_eq, view_liftU, view_liftU, ← real_own, ← sim_ofR]
  exact tv_bind_right_le_of_forall _ _ _ fun s₀ _ =>
    hV α s₀ (fun a => liftU (E a)) trivial fun a => adm_liftU (E a) 0 _ (hE a)

/-! ## 2. A fixed list of seeds -/

/-- An environment of Hiop/RecWhole.lean, when c further encoded indices exist, as the environment
that names the seed σ e for the encoded index number e. -/
def liftAt (σ : ℕ → L.OutOfDomainSeed) : EnvR L α → ℕ → EnvS L α
  | .stop a, _ => .stop a
  | .fresh k, c => .fresh (σ (c + 1)) fun a => liftAt σ (k a) (c + 1)
  | .test e k, c => .test e fun a => liftAt σ (k a) c
  | .link e k, c => .link e fun a => liftAt σ (k a) c
  | .session e J xs rest k, c => .session e J xs rest fun a => liftAt σ (k a) c
  | .read e p k, c => .read e p fun y => liftAt σ (k y) c
  | .draw β d k, c => .draw β d fun y => liftAt σ (k y) c

theorem adm_liftAt {B : BoundsR} {Gs : L.OutOfDomainSeed → Prop} {ok : X → Prop} {σ : ℕ → L.OutOfDomainSeed}
    (hσ : ∀ e, Gs (σ e)) (t : EnvR L α) :
    ∀ (c : ℕ) (u : UsedR), t.Adm B ok c u → (liftAt σ t c).Adm B Gs ok c u := by
  induction t with
  | stop a => intro _ _ _; exact trivial
  | draw β d k ih => intro c u h y; exact ih y c u (h y)
  | fresh k ih => intro c u h; exact ⟨hσ _, h.1, fun a => ih a (c + 1) u (h.2 a)⟩
  | test e k ih => intro c u h; exact ⟨h.1, h.2.1, fun a => ih a c _ (h.2.2 a)⟩
  | link e k ih => intro c u h; exact ⟨h.1, h.2.1, h.2.2.1, fun a => ih a c _ (h.2.2.2 a)⟩
  | session e J xs rest k ih =>
    intro c u h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun a => ih a c _ (h.2.2.2.2.2 a)⟩
  | read e p k ih => intro c u h; exact ⟨h.1, h.2.1, fun y => ih y c _ (h.2.2 y)⟩

/-- For every fixed list of seeds (in Gs) and every environment of the older type within the bounds:
the same bound. -/
theorem whole_fixed {H : HostS L} {Gs : L.OutOfDomainSeed → Prop} {ok : X → Prop} {B : BoundsR}
    {S : SimulatorS L} {z : ℝ≥0∞} (h : ViewNear H Gs ok B S z) (σ : ℕ → L.OutOfDomainSeed)
    (hσ : ∀ e, Gs (σ e)) (E : L.Rec → EnvR L α) (hE : ∀ a, (E a).Adm B ok 0 UsedR.zero) :
    tv (H.view (σ 0) fun a => liftAt σ (E a) 0) (S.host.view (σ 0) fun a => liftAt σ (E a) 0) ≤ z :=
  h α (σ 0) (fun a => liftAt σ (E a) 0) (hσ 0) fun a => adm_liftAt hσ (E a) 0 _ (hE a)

end Hiop.Seeded

#print axioms Hiop.Seeded.rec_hvzk_whole_again
#print axioms Hiop.Seeded.whole_fixed
