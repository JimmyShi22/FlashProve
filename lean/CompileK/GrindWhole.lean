-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/GrindWhole.lean: honest-verifier zero knowledge of the whole object (`HVZKWhole`,
Hiop/Whole.lean) is kept by the step that adds tests (proof of work), with the same error. A black
box: nothing is asked of the interface but HVZKWhole.

Definitions, statements and proofs.
The step (`L.grind`, Iop/BatchGrind.lean): in a round with b test bits the verifier message holds b
further uniform bits, the prover's message a nonce. On the level of the interface the honest
provers send a fixed nonce and look at no test bit, and a failed test is not withheld. So what is
shown of a run of the object with tests is what is shown of a run of the object, with the fixed
nonces written in, and with verifier randomness whose test bits are fresh uniform bits.

Main names:
  `hvzkWhole_grind : Spec.hvzkWhole_grind`:
      HVZKWhole L Ryes B (simWhole L Sm i₀) z ⇒
      HVZKWhole (L.grind Nn gT gL gB) Ryes B (simWhole _ (Sm.grind gT gL gB) i₀) z.
    Same bounds B, same relation, same error z, for all lists of numbers of test bits; the run
    simulators are the old ones at the stripped verifier messages, with the fixed nonces written in
    (Compile/Batch/SimsGrind.lean). Nn is a type of nonces with a fixed element (`[Inhabited Nn]`),
    the fixed nonce.

How: as CompileK/WholePull.lean (verifier messages made by samplers): an environment (`Env`,
Hiop/Whole.lean) of the object with tests is played against the object; after each run it is shown
(ρ, o) with ρ uniform (exactly: `adaptQG`, `adaptBG`), and draws a point ρ' above ρ from the
conditional law. That file's adapter (`fib`, `adapt`, `Adapts`, `adapts_run`) is used as it stands,
at the factor K = 1: stripped uniform randomness is uniform (`Rho.map_strip_unif`,
Iop/GrindProofs.lean; `map_strip_unif`, Iop/BatchGrindProofs.lean), so nothing is rejected but on a
null set. Outputs stay in Option α and the coins of `pad` show "some" for sure: an idle remnant of
the general form.
  Part 1: the environment, the factor, the bounds, the view, the distance: the analogue of
    CompileK/WholePull.lean's Parts 2 and 3 with `L.grind ..` in the place of `L.pull ..`, names
    with G or grind (the two interfaces are different terms, and that file's lemmas are typed over
    `L.pull ..`). Part 2: the adapters of the three kinds of runs, real and simulated. Part 3: the
    theorem.

Limits: it is a statement on the interface, where the nonces are fixed. The compiled prover searches
for a nonce; that its search gives nothing away is part of the compiler's privacy theorem
(CompileK/PrivacyWhole.lean, for wires with tests) (in this sense:
`Gen.HasIndexPrivacyWith (relPair Ryes Rno hsub) (argBKE W WP p) B (simBKGr W p Sm i₀)`
`(fun t n => p.leaves * binTail n p.leaves p.s1 + hashTermsBGTot W p t n + z)`;
`privacyWholeTot`, under its hypotheses; `hashTerms_work`, CompileK/GrindCost.lean, under its
hypotheses), not of this file. This file says nothing on running time. The simulator is again the
named one (`simWhole`).

Terms: lean/GLOSSARY.md.
-/
import CompileK.WholePull
import Compile.Batch.SimsGrind

set_option autoImplicit false

noncomputable section

namespace Hiop.Grind
open Prob Iop Iop.BatchPull Compile.Lifetime Compile.BatchLife Hiop.Pull
open scoped ENNReal

/-! ## Part 1. An environment of the object with tests as an environment of the object -/

section Env
variable {I X : Type} {L : BatchProtocol I X} {Nn : Type} [Inhabited Nn] {gT : GBits L.offline.shape}
  {gL : GBits L.link.shape} {gB : GBits L.onlineBatch.loc.shape} {α : Type}

variable (AdL : Sess L.link → PMF (Option (Sess (L.grind Nn gT gL gB).link)))
  (AdB : (J : Finset (Fin L.maxBatchSize)) → BSess L.onlineBatch J → PMF (Option (BSess (L.grind Nn gT gL gB).onlineBatch J)))
  (KL KB : ℝ≥0∞)

/-- The environment t of the object with tests, played against the object. After each run it passes
what is shown through the adapter, and stops with none if that gives up. a, b: how many further
encoded indices and how many sessions it may still ask for; when t stops it tosses the coins of the
runs that it has not asked for, so that all paths carry the same factor. -/
def trG : Env (L.grind Nn gT gL gB) α → ℕ → ℕ → Env L (Option α)
  | .stop x, a, b => pad KL a (pad KB b (.stop (some x)))
  | .fresh _, 0, _ => .stop none
  | .fresh k, a + 1, b => .fresh fun u => .draw _ (AdL u) fun o => match o with
      | none => .stop none
      | some u' => trG (k u') a b
  | .session _ _ _ _ _, _, 0 => .stop none
  | .session e J xs rest k, a, b + 1 => .session e J xs rest fun u => .draw _ (AdB J u) fun o => match o with
      | none => .stop none
      | some u' => trG (k u') a b
  | .read e p k, a, b => .read e p fun y => trG (k y) a b
  | .draw β d k, a, b => .draw β d fun y => trG (k y) a b

/-- on every path at most a further encoded indices and at most b sessions -/
def RunsLeG : Env (L.grind Nn gT gL gB) α → ℕ → ℕ → Prop
  | .stop _, _, _ => True
  | .fresh _, 0, _ => False
  | .fresh k, a + 1, b => ∀ u, RunsLeG (k u) a b
  | .session _ _ _ _ _, _, 0 => False
  | .session _ _ _ _ k, a, b + 1 => ∀ u, RunsLeG (k u) a b
  | .read _ _ k, a, b => ∀ y, RunsLeG (k y) a b
  | .draw _ _ k, a, b => ∀ y, RunsLeG (k y) a b

variable {AdL AdB KL KB}

/-- The factor. Under the hypotheses below, whatever is measured of the outputs of the play with
tests is KL^a · KB^b times the same measured of the outputs "some .." of the play against the
object. -/
theorem expect_trG (W : Laws L) (W' : Laws (L.grind Nn gT gL gB)) (hL1 : 1 ≤ KL) (hLt : KL ≠ ⊤)
    (hB1 : 1 ≤ KB) (hBt : KB ≠ ⊤) (hL : ∀ r r', Adapts (W.Lk r r') (W'.Lk r r') AdL KL)
    (hB : ∀ r J xs rest, Adapts (W.B r J xs rest) (W'.B r J xs rest) (AdB J) KB)
    (hy : ∀ r p, W'.y r p = W.y r p) (F : α → ℝ≥0∞) :
    ∀ (t : Env (L.grind Nn gT gL gB) α) (a b : ℕ) (s : ℕ × (ℕ → L.EncodingRandomness)), RunsLeG t a b →
      KL ^ a * KB ^ b * expect ((trG AdL AdB KL KB t a b).run W.host s) (lift F) =
        expect (t.run W'.host s) F := by
  intro t
  induction t with
  | stop x =>
    intro a b s _
    simp only [trG]
    rw [mul_comm (KL ^ a), mul_assoc, expect_pad hL1 hLt, expect_pad hB1 hBt, run_stop, expect_pure]
    exact (expect_pure x F).symm
  | fresh k ih =>
    intro a b s h
    obtain ⟨c, f⟩ := s
    cases a with
    | zero => exact h.elim
    | succ a =>
      simp only [trG]
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
      simp only [trG]
      refine Eq.trans ?_ (congrArg (fun P => expect P F) (run_session W' e J xs rest k s)).symm
      rw [run_session]
      simp only [run_draw, expect_bind]
      rw [show KL ^ a * KB ^ (b + 1) = KB * (KL ^ a * KB ^ b) by rw [pow_succ]; ring]
      exact (hB (s.2 e) J xs rest).use _ _ _ (expect_pure _ _) fun u' => ih u' a b _ (h u')
  | read e p k ih =>
    intro a b s h
    simp only [trG]
    refine Eq.trans ?_ (congrArg (fun P => expect P F) (run_read W' e p k s)).symm
    rw [run_read]
    show _ = expect ((k (W'.y (s.2 e) p)).run W'.host s) F
    rw [hy]
    exact ih _ a b s (h _)
  | draw β d k ih =>
    intro a b s h
    simp only [trG]
    refine Eq.trans ?_ (congrArg (fun P => expect P F) (run_draw W' β d k s)).symm
    rw [run_draw]
    simp only [expect_bind]
    rw [← expect_const_mul]
    exact expect_congr _ fun y => ih y a b s (h y)

end Env

/-! ### The bounds are kept; the view; the distance -/

section Bounds
variable {I X : Type} {L : BatchProtocol I X} {Nn : Type} [Inhabited Nn] {gT : GBits L.offline.shape}
  {gL : GBits L.link.shape} {gB : GBits L.onlineBatch.loc.shape} {α : Type} {B : Bounds} {ok : X → Prop}

variable (AdT : Sess L.offline → PMF (Option (Sess (L.grind Nn gT gL gB).offline)))
  (AdL : Sess L.link → PMF (Option (Sess (L.grind Nn gT gL gB).link)))
  (AdB : (J : Finset (Fin L.maxBatchSize)) → BSess L.onlineBatch J → PMF (Option (BSess (L.grind Nn gT gL gB).onlineBatch J)))
  (KT KL KB : ℝ≥0∞)

/-- The new environment asks for the same runs, at the same places, so it keeps the bounds
(`Env.Adm`). -/
theorem adm_trG :
    ∀ (t : Env (L.grind Nn gT gL gB) α) (a b c : ℕ) (us ur : ℕ → ℕ),
      t.Adm B ok c us ur → (trG AdL AdB KL KB t a b).Adm B ok c us ur := by
  intro t
  induction t with
  | stop x =>
    intro a b c us ur _
    simp only [trG]
    exact adm_pad _ _ _ (adm_pad _ _ _ trivial)
  | fresh k ih =>
    intro a b c us ur h
    cases a with
    | zero => trivial
    | succ a =>
      simp only [trG]
      refine ⟨h.1, fun u o => ?_⟩
      cases o with
      | none => trivial
      | some u' => exact ih u' a b _ _ _ (h.2 u')
  | session e J xs rest k ih =>
    intro a b c us ur h
    cases b with
    | zero => trivial
    | succ b =>
      simp only [trG]
      refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun u o => ?_⟩
      cases o with
      | none => trivial
      | some u' => exact ih u' a b _ _ _ (h.2.2.2.2.2 u')
  | read e p k ih =>
    intro a b c us ur h
    simp only [trG]
    exact ⟨h.1, h.2.1, fun y => ih y a b _ _ _ (h.2.2 y)⟩
  | draw β d k ih =>
    intro a b c us ur h
    simp only [trG]
    exact fun y => ih y a b _ _ _ (h y)

theorem runsLeG_of_adm :
    ∀ (t : Env (L.grind Nn gT gL gB) α) (c : ℕ) (us ur : ℕ → ℕ),
      t.Adm B ok c us ur → c ≤ B.nenc → RunsLeG t (B.nenc - c) (left B us) := by
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

/-- the environment after the offline phase -/
def trEG (E' : Sess (L.grind Nn gT gL gB).offline → Env (L.grind Nn gT gL gB) α) (a b : ℕ) :
    Sess L.offline → Env L (Option α) :=
  fun u => .draw _ (AdT u) fun o => match o with
    | none => .stop none
    | some u' => trG AdL AdB KL KB (E' u') a b

variable {AdT AdL AdB KT KL KB}

theorem expect_viewG (W : Laws L) (W' : Laws (L.grind Nn gT gL gB)) (hL1 : 1 ≤ KL) (hLt : KL ≠ ⊤)
    (hB1 : 1 ≤ KB) (hBt : KB ≠ ⊤) (hT : ∀ r, Adapts (W.T r) (W'.T r) AdT KT)
    (hL : ∀ r r', Adapts (W.Lk r r') (W'.Lk r r') AdL KL)
    (hB : ∀ r J xs rest, Adapts (W.B r J xs rest) (W'.B r J xs rest) (AdB J) KB)
    (hy : ∀ r p, W'.y r p = W.y r p) (F : α → ℝ≥0∞)
    (E' : Sess (L.grind Nn gT gL gB).offline → Env (L.grind Nn gT gL gB) α) (a b : ℕ)
    (hE : ∀ u, RunsLeG (E' u) a b) :
    KT * (KL ^ a * KB ^ b) * expect (W.host.view (trEG AdT AdL AdB KL KB E' a b)) (lift F) =
      expect (W'.host.view E') F := by
  refine Eq.trans ?_ (congrArg (fun P => expect P F) (view_host W' E')).symm
  rw [view_host]
  unfold trEG
  simp only [run_draw, expect_bind]
  rw [← expect_const_mul]
  refine expect_congr _ fun r => ?_
  exact (hT r).use _ _ _ (expect_pure _ _) fun u' =>
    expect_trG W W' hL1 hLt hB1 hBt hL hB hy F (E' u') a b _ (hE u')

/-- Under the hypotheses below, the distance of two views with tests is at most the factor times
the distance of the two views of the object, for the environment made from the one with tests. -/
theorem tv_view_grind (W V : Laws L) (W' V' : Laws (L.grind Nn gT gL gB)) (hL1 : 1 ≤ KL)
    (hLt : KL ≠ ⊤) (hB1 : 1 ≤ KB) (hBt : KB ≠ ⊤) (hT : ∀ r, Adapts (W.T r) (W'.T r) AdT KT)
    (hL : ∀ r r', Adapts (W.Lk r r') (W'.Lk r r') AdL KL)
    (hB : ∀ r J xs rest, Adapts (W.B r J xs rest) (W'.B r J xs rest) (AdB J) KB)
    (hy : ∀ r p, W'.y r p = W.y r p) (vT : ∀ r, Adapts (V.T r) (V'.T r) AdT KT)
    (vL : ∀ r r', Adapts (V.Lk r r') (V'.Lk r r') AdL KL)
    (vB : ∀ r J xs rest, Adapts (V.B r J xs rest) (V'.B r J xs rest) (AdB J) KB)
    (vy : ∀ r p, V'.y r p = V.y r p)
    (E' : Sess (L.grind Nn gT gL gB).offline → Env (L.grind Nn gT gL gB) α) (a b : ℕ)
    (hE : ∀ u, RunsLeG (E' u) a b) :
    tv (W'.host.view E') (V'.host.view E') ≤
      KT * (KL ^ a * KB ^ b) *
        tv (W.host.view (trEG AdT AdL AdB KL KB E' a b))
          (V.host.view (trEG AdT AdL AdB KL KB E' a b)) := by
  classical
  refine tv_le_of_forall_pr_le fun A => ?_
  rw [pr_eq_expect, pr_eq_expect, ← expect_viewG W W' hL1 hLt hB1 hBt hT hL hB hy _ E' a b hE,
    ← expect_viewG V V' hL1 hLt hB1 hBt vT vL vB vy _ E' a b hE, ← mul_add]
  refine mul_le_mul_right (expect_le_expect_add_tv _ _ fun o => ?_) _
  cases o with
  | none => exact zero_le _
  | some x =>
    show (if x ∈ A then (1 : ℝ≥0∞) else 0) ≤ 1
    split_ifs <;> simp

end Bounds

/-! ## Part 2. The adapters of the three kinds of runs -/

section Single
variable {Y : Type} {E : ExtSpec} {Q : InteractiveOracleProof Y E} {Wt : Type} {Nn : Type} [Inhabited Nn]

/-- the adapter of a run of one IOP: fresh test bits, the fixed nonces -/
def adaptQG (Q : InteractiveOracleProof Y E) (g : GBits Q.shape) (ν : GNon Nn Q.shape) :
    Sess Q → PMF (Option (Sess (Q.grind Nn g))) :=
  adapt (unif (Rho Q.shape))
    (unif (Rho (Q.shape.grind Nn g))) (Rho.strip g) 1 (Option.map (DView.fill g ν))

theorem den_rhoG (g : GBits Q.shape) (ρ : Rho Q.shape) :
    ((unif (Rho (Q.shape.grind Nn g))).map (Rho.strip g)) ρ ≤ 1 * (unif (Rho Q.shape)) ρ := by
  rw [Rho.map_strip_unif, one_mul]

theorem adapts_sessG (H : Honest Q Wt) (g : GBits Q.shape) (ν : GNon Nn Q.shape) (w : Wt) (y : Y) :
    Adapts (sess H w y) (sess (H.grind g ν) w y) (adaptQG Q g ν) 1 := by
  have h := adapts_run ENNReal.one_ne_top (den_rhoG (Nn := Nn) g)
    (H.output w y) (Option.map (DView.fill g ν))
  have e : sess (H.grind g ν) w y =
      (unif (Rho (Q.shape.grind Nn g))).bind fun ρ' =>
        (H.output w y (Rho.strip g ρ')).map fun o => (ρ', o.map (DView.fill g ν)) := by
    unfold sess
    refine congrArg _ (funext fun ρ' => ?_)
    rw [Honest.output_grind, PMF.map_comp]
    rfl
  rw [e]
  exact h

theorem adapts_simSessG (Sim : SimOf Q) (g : GBits Q.shape)
    (ν : GNon Nn Q.shape) (y : Y) (str : E.Str) :
    Adapts (simSess Q Sim y str)
      (simSess (Q.grind Nn g) (simGrind g ν Sim) y str) (adaptQG Q g ν) 1 := by
  have h := adapts_run ENNReal.one_ne_top (den_rhoG (Nn := Nn) g)
    (fun ρ => Sim y ρ (Q.extAns y ρ str)) (Option.map (DView.fill g ν))
  have e : simSess (Q.grind Nn g) (simGrind g ν Sim) y str =
      (unif (Rho (Q.shape.grind Nn g))).bind fun ρ' =>
        (Sim y (Rho.strip g ρ') (Q.extAns y (Rho.strip g ρ') str)).map fun o =>
            (ρ', o.map (DView.fill g ν)) := by
    unfold simSess simGrind
    refine congrArg _ (funext fun ρ' => ?_)
    rw [PMF.map_comp]
    rfl
  rw [e]
  exact h

end Single

section Batch
variable {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} {Wt : Type} {N : ℕ}
  {Nn : Type} [Inhabited Nn]

/-- the adapter of a session in which the slots of J are shown -/
def adaptBG (Q : BatchInteractiveOracleProof Y E) (g : GBits Q.loc.shape)
    (ν : GNon Nn Q.loc.shape) (J : Finset (Fin N)) :
    BSess Q J → PMF (Option (BSess (Q.grind Nn g) J)) :=
  adapt ((unif (BRho N Q.loc.shape Q.ann)).map (vis _ _ J))
    ((unif (BRho N (Q.loc.shape.grind Nn g) (Q.ann.grind Nn g))).map (vis _ _ J))
    (fun ρs j => Rho.strip g (ρs j)) 1 (DView.fillJ g fun _ => ν)

theorem vis_strip (g : GBits Q.loc.shape) (J : Finset (Fin N))
    (ρ' : BRho N (Q.loc.shape.grind Nn g) (Q.ann.grind Nn g)) :
    (fun j => Rho.strip g (vis _ _ J ρ' j)) = vis _ _ J (BRho.strip g ρ') :=
  funext fun j => (BatchGrind.slot_strip j.1 g ρ').symm

theorem den_brhoG (g : GBits Q.loc.shape) (J : Finset (Fin N)) (v : J → Rho Q.loc.shape) :
    (((unif (BRho N (Q.loc.shape.grind Nn g) (Q.ann.grind Nn g))).map (vis _ _ J)).map
        fun ρs j => Rho.strip g (ρs j)) v ≤
      1 * ((unif (BRho N Q.loc.shape Q.ann)).map (vis _ _ J)) v := by
  have e : (fun ρs : J → Rho (Q.loc.shape.grind Nn g) => fun j => Rho.strip g (ρs j)) ∘ vis _ _ J =
      vis _ _ J ∘ BRho.strip (N := N) (A := Q.ann) g :=
    funext fun ρ' => vis_strip g J ρ'
  rw [PMF.map_comp, e, ← PMF.map_comp, BatchGrind.map_strip_unif, one_mul]

theorem adapts_of_visG (g : GBits Q.loc.shape) (ν : GNon Nn Q.loc.shape) (J : Finset (Fin N))
    (ker : (J → Rho Q.loc.shape) → PMF (J → Option (DView Q.loc))) :
    Adapts ((unif (BRho N Q.loc.shape Q.ann)).bind fun ρ =>
        (ker (vis _ _ J ρ)).map fun o => (vis _ _ J ρ, o))
      ((unif (BRho N (Q.loc.shape.grind Nn g) (Q.ann.grind Nn g))).bind fun ρ' =>
        (ker (vis _ _ J (BRho.strip g ρ'))).map fun o =>
          (vis _ _ J ρ', DView.fillJ g (fun _ => ν) o))
      (adaptBG Q g ν J) 1 := by
  have h := adapts_run ENNReal.one_ne_top (den_brhoG (Nn := Nn) g J) ker (DView.fillJ g fun _ => ν)
  rw [PMF.bind_map, PMF.bind_map] at h
  simp only [Function.comp_def, vis_strip] at h
  exact h

theorem adapts_bsessG (H : BatchHonestProver Q Wt) (g : GBits Q.loc.shape) (ν : GNon Nn Q.loc.shape) (w : Wt)
    (x : Fin N → Option Y) (J : Finset (Fin N)) :
    Adapts (bsess H w x J) (bsess (H.grind g ν) w x J) (adaptBG Q g ν J) 1 := by
  have h := adapts_of_visG g ν J fun ρs =>
    (unif (H.Coin0 × (Fin N → H.Coin))).map fun c =>
      fun j : J => slotOut H w (x j) (ρs j) (c.1, c.2 j)
  have e : bsess (H.grind g ν) w x J = (unif (BRho N (Q.loc.shape.grind Nn g) (Q.ann.grind Nn g))).bind fun ρ' =>
      ((unif (H.Coin0 × (Fin N → H.Coin))).map fun c =>
            fun j : J => slotOut H w (x j) (vis _ _ J (BRho.strip g ρ') j) (c.1, c.2 j)).map
          fun o => (vis _ _ J ρ', DView.fillJ g (fun _ => ν) o) := by
    unfold bsess
    refine congrArg _ (funext fun ρ' => ?_)
    rw [BatchGrind.output_grind, output_eq]
    refine (PMF.map_comp _ _ _).trans ?_
    rfl
  rw [e]
  exact h

theorem adapts_simBsessG (Sim : BSimOf Q N) (g : GBits Q.loc.shape) (ν : GNon Nn Q.loc.shape)
    (J : Finset (Fin N)) (xs : J → Y) (str : E.Str) :
    Adapts (simBsess Q Sim J xs str)
      (simBsess (Q.grind Nn g) (simGrindB g (fun _ _ => ν) Sim) J xs str) (adaptBG Q g ν J) 1 := by
  have h := adapts_of_visG g ν J fun ρs => Sim J xs ρs (Q.extAnsJ J xs ρs str)
  have e : simBsess (Q.grind Nn g) (simGrindB g (fun _ _ => ν) Sim) J xs str = (unif (BRho N (Q.loc.shape.grind Nn g) (Q.ann.grind Nn g))).bind fun ρ' =>
      (Sim J xs (vis _ _ J (BRho.strip g ρ'))
            (Q.extAnsJ J xs (vis _ _ J (BRho.strip g ρ')) str)).map
          fun o => (vis _ _ J ρ', DView.fillJ g (fun _ => ν) o) := by
    unfold simBsess simGrindB
    refine congrArg _ (funext fun ρ' => ?_)
    rw [PMF.map_comp, ← vis_strip]
    rfl
  rw [e]
  exact h

end Batch

/-! ## Part 3. The theorem -/

section Main
variable {I X : Type}

namespace Spec

/-- Honest-verifier zero knowledge of the whole object is kept by the step that adds tests, with
the same error, as a black box: nothing is asked of L but HVZKWhole. Limits: the head. -/
def hvzkWhole_grind : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (I X : Type) (L : BatchProtocol I X) (gT : GBits L.offline.shape)
      (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) (Ryes : I → X → Prop) (B : Bounds)
      (Sm : Sims L) (i₀ : I) (z : ℝ≥0∞),
    HVZKWhole L Ryes B (simWhole L Sm i₀) z →
    HVZKWhole (L.grind Nn gT gL gB) Ryes B (simWhole (L.grind Nn gT gL gB) (Sm.grind gT gL gB) i₀) z

end Spec

theorem hvzkWhole_grind : Spec.hvzkWhole_grind := by
  intro Nn _ I X L gT gL gB Ryes B Sm i₀ z hz i α E' hE'
  have h := tv_view_grind (AdT := adaptQG L.offline gT (GNon.nil Nn _))
    (AdL := adaptQG L.link gL (GNon.nil Nn _)) (AdB := fun J => adaptBG L.onlineBatch gB (GNon.nil Nn _) J)
    (KT := 1) (KL := 1) (KB := 1)
    (realLaws L i) (simLaws L Sm i₀) (realLaws (L.grind Nn gT gL gB) i)
    (simLaws (L.grind Nn gT gL gB) (Sm.grind gT gL gB) i₀)
    le_rfl ENNReal.one_ne_top le_rfl ENNReal.one_ne_top
    (fun r => adapts_sessG L.honestOfflineProver gT _ (i, r) ()) (fun r r' => adapts_sessG L.honestLinkProver gL _ (i, r, r') ())
    (fun r J xs rest => adapts_bsessG L.honestOnlineBatchProver gB _ (i, r) (vec J xs rest) J) (fun _ _ => rfl)
    (fun r => adapts_simSessG Sm.T gT _ () (L.encodeIndex i₀ r))
    (fun r r' => adapts_simSessG Sm.Lk gL _ () (L.encodeIndex i₀ r, L.encodeIndex i₀ r'))
    (fun r J xs _ => adapts_simBsessG Sm.B gB _ J xs (L.encodeIndex i₀ r)) (fun _ _ => rfl)
    E' B.nenc B.total (fun u => by
      have := runsLeG_of_adm (E' u) 0 _ _ (hE' u) (Nat.zero_le _)
      rwa [Nat.sub_zero, left_zero] at this)
  have hadm : ∀ u,
      (trEG (adaptQG L.offline gT (GNon.nil Nn _)) (adaptQG L.link gL (GNon.nil Nn _))
          (fun J => adaptBG L.onlineBatch gB (GNon.nil Nn _) J) 1 1 E' B.nenc B.total u).Adm
        B (Ryes i) 0 (fun _ => 0) fun _ => 0 := by
    intro u
    unfold trEG
    intro o
    cases o with
    | none => trivial
    | some u' => exact adm_trG _ _ _ _ (E' u') _ _ _ _ _ (hE' u')
  rw [one_pow, one_pow, one_mul, one_mul, one_mul] at h
  exact h.trans (hz i (Option α) _ hadm)

end Main

end Hiop.Grind
