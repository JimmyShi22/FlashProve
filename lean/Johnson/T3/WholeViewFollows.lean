-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/T3/WholeViewFollows.lean: the whole view from a fixed index follows from the runs, from the
counts of the columns read and from the hiding of the encoding: WholeViewFollows of
VerifiableInference/Final/ZeroKnowledgeBeforeHashing.lean as a theorem, for any protocol of the
interface's type.

  tv_run_cleared   one run: exact outside a set of measure at most h: the real run is within h of the
                   simulated run
  near_realSide    the real side on an index in range is near the simulated runs
  counts_simulatedRuns   the simulated runs read what the verifiers read; a refused session nothing
  wholeViewFollows the statement

By form_laws (Hiop/Seeded/FormProof.lean), general in the form of runs. It spends neither the range's
two indices nor that the maps only clear bits. Not claimed: anything of a particular protocol.
-/
import VerifiableInference.Final.ZeroKnowledgeLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Compilation
open Iop Prob Hiop.Seeded
open Hiop (BoundsR)

section One
variable {Y : Type} {E : ExtSpec} {Q : InteractiveOracleProof Y E} {Wt : Type}

/-- **One run.** Exact outside a set whose measure is at most h, over uniform messages read through c:
the real run is within h of the simulated run. -/
theorem tv_run_cleared (H : Honest Q Wt) (sim : Compile.Lifetime.SimOf Q)
    (c : Rho Q.shape → Rho Q.shape) (w : Wt) (y : Y) (T : Set (Rho Q.shape)) {h : ℝ≥0∞}
    (hE : ∀ ρ, c ρ ∉ T → H.output w y (c ρ) = sim y (c ρ) (Q.extAns y (c ρ) (H.ext w)))
    (hS : pr (unif (Rho Q.shape)) {ρ | c ρ ∈ T} ≤ h) :
    tv (runAt H ((unif (Rho Q.shape)).map c) some w y)
      ((simAt Q sim ((unif (Rho Q.shape)).map c) some y).law (E.rd (H.ext w))) ≤ h := by
  refine tv_runAt_le H sim _ some w y ?_
  rw [pr_map]
  refine (pr_mono _ ?_).trans hS
  rintro ρ ⟨r, h1, h2⟩
  have e := Option.some.inj h1
  subst e
  by_contra hn
  exact h2 (hE ρ hn)

end One

section Object
variable {I X : Type} {L : HolographicProtocol I X}

/-- **The real side on an index in range is near the simulated runs.** -/
theorem near_realSide {work : PartsWork L} {provers : HonestProvers L} {simulators : RunSimulators L}
    {inRange : I → Prop} {Served : I → X → Prop} {N : Budget}
    (hRun : RunByRun work provers simulators inRange Served N) (copyOf : ℕ → ℕ) {i : I}
    (hi : inRange i) :
    (realSide L work (proversByTable provers copyOf) i).Near
      (simulatedRuns L work (simulatorsByTable simulators copyOf)) (fun _ => True) i (Served i)
      N.offlineStops N.linkStops N.onlineStops where
  rc := fun _ => rfl
  y := fun _ _ => rfl
  T := fun e u _ => by
    have h1 := tv_run_cleared provers.offlineProver simulators.offline work.offline.cleared (i, u.1, u.2)
      (L.recOf i u.1 u.2) (provers.offlineProver.Hid (i, u.1, u.2) (L.recOf i u.1 u.2))
      (fun ρ hρ => hRun.offline (i, u.1, u.2) _ ⟨hi, rfl⟩ ρ hρ)
      (hRun.offlineStops (i, u.1, u.2) _ ⟨hi, rfl⟩)
    rw [hRun.tables.offline] at h1
    exact h1
  Lk := fun e u u' _ _ => by
    obtain ⟨r, s⟩ := u
    obtain ⟨r', s'⟩ := u'
    have h1 := tv_run_cleared provers.linkProver simulators.link work.link.cleared (i, (r, s), (r', s'))
      (L.recOf i r s, L.recOf i r' s')
      (provers.linkProver.Hid (i, (r, s), (r', s')) (L.recOf i r s, L.recOf i r' s'))
      (fun ρ hρ => hRun.link (i, (r, s), (r', s')) _ ⟨hi, rfl⟩ ρ hρ)
      (hRun.linkStops (i, (r, s), (r', s')) _ ⟨hi, rfl⟩)
    rw [hRun.tables.link] at h1
    exact h1
  B := fun e u q h _ hq => by
    have e1 : (((everyRequest L).wt q : ℕ) : ℝ≥0∞) * N.onlineStops = N.onlineStops := by
      show ((1 : ℕ) : ℝ≥0∞) * N.onlineStops = N.onlineStops
      rw [Nat.cast_one, one_mul]
    show tv (runAt (provers.onlineAtCopy (copyOf e)) ((unif (Rho L.onlineBatch.loc.shape)).map work.online.cleared) some
        (i, u.1, u.2) (q.1, L.recOf i u.1 u.2))
      ((simAt L.onlineBatch.loc (simulators.online (copyOf e)) ((unif (Rho L.onlineBatch.loc.shape)).map work.online.cleared)
        (fun ρ => if q.2 = true then some ρ else none) (q.1, L.recOf i u.1 u.2)).law (L.encodeIndex i u.1)) ≤ _
    rw [e1]
    by_cases h2 : q.2 = true
    · have hs : Served i q.1 := hq.2 h2
      have h1 := tv_run_cleared (provers.onlineAtCopy (copyOf e)) (simulators.online (copyOf e))
        work.online.cleared (i, u.1, u.2) (q.1, L.recOf i u.1 u.2)
        ((provers.onlineAtCopy (copyOf e)).Hid (i, u.1, u.2) (q.1, L.recOf i u.1 u.2))
        (fun ρ hρ => hRun.online (copyOf e) (i, u.1, u.2) _ ⟨hi, rfl, hs⟩ ρ hρ)
        (hRun.onlineStops (copyOf e) (i, u.1, u.2) _ ⟨hi, rfl, hs⟩)
      have hx : (provers.onlineAtCopy (copyOf e)).ext (i, u.1, u.2) = L.encodeIndex i u.1 :=
        hRun.tables.online i u.1 u.2 (copyOf e)
      rw [hx] at h1
      simp only [h2, if_true]
      exact h1
    · have hs : ¬ Served i q.1 := fun hS => h2 (hq.1 hS)
      have eW : runAt (provers.onlineAtCopy (copyOf e)) ((unif (Rho L.onlineBatch.loc.shape)).map work.online.cleared)
          some (i, u.1, u.2) (q.1, L.recOf i u.1 u.2) =
          ((unif (Rho L.onlineBatch.loc.shape)).map work.online.cleared).bind fun a => PMF.pure (a, none) := by
        unfold runAt
        congr 1
        funext a
        show (((provers.onlineAtCopy (copyOf e)).output (i, u.1, u.2) (q.1, L.recOf i u.1 u.2) a).map
          fun o => (a, o)) = _
        rw [refused_output hRun (copyOf e) _ _ hi rfl hs, PMF.pure_map]
      have eS : (simAt L.onlineBatch.loc (simulators.online (copyOf e))
          ((unif (Rho L.onlineBatch.loc.shape)).map work.online.cleared)
          (fun ρ => if q.2 = true then some ρ else none) (q.1, L.recOf i u.1 u.2)).law (L.encodeIndex i u.1) =
          ((unif (Rho L.onlineBatch.loc.shape)).map work.online.cleared).bind fun a => PMF.pure (a, none) := by
        unfold RunSim.law
        simp only [simAt, h2, if_false, showAt]
        rfl
      rw [eW, eS, tv_self]
      exact zero_le _

/-- **The simulated runs read what the verifiers read**; a refused session reads nothing. -/
theorem counts_simulatedRuns {Gs : L.OutOfDomainSeed → Prop} {b qT qpar qch qon : ℕ}
    (hR : ReadsG L Gs b qT qpar qch qon) (work : PartsWork L) (Sm : SimsG L) :
    (simulatedRuns L work Sm).Counts qT qpar qch qon where
  cntT := fun e x a =>
    reads_simAt (Sm.T e) _ some x (fun T => T.card ≤ qT) (Nat.zero_le _) (hR.cntT x) a
  cntLp := fun e x a =>
    reads_simAt (Sm.Lk e) _ some x (fun T => (T.filter fun p => p.isLeft).card ≤ qpar)
      (Nat.zero_le _) (hR.cntLp x) a
  cntLc := fun e x a =>
    reads_simAt (Sm.Lk e) _ some x (fun T => (T.filter fun p => p.isRight).card ≤ qch)
      (Nat.zero_le _) (hR.cntLc x) a
  cntB := fun e q x a =>
    reads_simAt (Sm.B e) _ (fun ρ => if q.2 = true then some ρ else none) (q.1, x)
      (fun T => T.card ≤ qon) (Nat.zero_le _) (hR.cntO (q.1, x)) a

/-- **The whole view follows.** -/
theorem wholeViewFollows (work : PartsWork L) (provers : HonestProvers L)
    (simulators : RunSimulators L) (inRange : I → Prop) (Served : I → X → Prop) (N : Budget) :
    WholeViewFollows work provers simulators inRange Served N := by
  intro hR hRun copyOf B hB i i₀ hi
  exact form_laws I X L (everyRequest L) (fun _ => True) (Served i) N.columns N.offlineReads
    N.linkReadsFirst N.linkReadsCopy N.onlineReads N.offlineStops N.linkStops N.onlineStops
    hR.hidE (simulatedRuns L work (simulatorsByTable simulators copyOf))
    (counts_simulatedRuns hR work _) (realSide L work (proversByTable provers copyOf) i) i
    (near_realSide hRun copyOf hi) B hB i₀

theorem sum_links (copies sessionsPerCopy : ℕ) :
    (commitmentLife copies sessionsPerCopy).sum (commitmentLife copies sessionsPerCopy).links =
      copies := by
  show ∑ j ∈ Finset.range (copies + 1), (if j = 0 then 0 else 1) = copies
  rw [Finset.sum_range_succ']
  simp

theorem sum_tests (copies sessionsPerCopy : ℕ) :
    (commitmentLife copies sessionsPerCopy).sum (commitmentLife copies sessionsPerCopy).tests =
      1 := by
  show ∑ j ∈ Finset.range (copies + 1), (if j = 0 then 1 else 0) = 1
  rw [Finset.sum_range_succ']
  simp

theorem sum_sess (copies sessionsPerCopy : ℕ) :
    (commitmentLife copies sessionsPerCopy).sum (commitmentLife copies sessionsPerCopy).sess =
      copies * sessionsPerCopy := by
  show ∑ j ∈ Finset.range (copies + 1), (if j = 0 then 0 else sessionsPerCopy) = _
  rw [Finset.sum_range_succ']
  simp

/-- **The error of a commitment's life**: one offline run, a link for each copy, the sessions of each
copy. -/
theorem err_commitmentLife (copies sessionsPerCopy : ℕ) (zT zL zO : ℝ≥0∞) :
    (commitmentLife copies sessionsPerCopy).err zT zL zO =
      zT + copies * zL + (copies * sessionsPerCopy : ℕ) * zO := by
  unfold BoundsR.err
  rw [sum_tests, sum_links, sum_sess]
  show ((1 : ℕ) : ℝ≥0∞) * zT + copies * zL +
    ((copies * sessionsPerCopy : ℕ) : ℝ≥0∞) * (((1 : ℕ) : ℝ≥0∞) * zO) = _
  simp only [Nat.cast_one, one_mul]

/-- The budgets of a commitment's life fit. -/
theorem fits_commitmentLife (N : Budget) (copies sessionsPerCopy : ℕ)
    (h1 : N.offlineReads + copies * N.linkReadsFirst ≤ N.columns)
    (h2 : N.linkReadsCopy + sessionsPerCopy * N.onlineReads ≤ N.columns) :
    (commitmentLife copies sessionsPerCopy).Fits N.columns N.offlineReads N.linkReadsFirst
      N.linkReadsCopy N.onlineReads := by
  intro e _
  rw [sum_links]
  by_cases he : e = 0
  · subst he
    show (if (0 : ℕ) = 0 then 1 else 0) * N.offlineReads +
        (if (0 : ℕ) = 0 then copies * N.linkReadsFirst else 0) +
        (if (0 : ℕ) = 0 then 0 else 1) * N.linkReadsCopy +
        (if (0 : ℕ) = 0 then 0 else sessionsPerCopy) * N.onlineReads + 0 ≤ N.columns
    simpa using h1
  · show (if e = 0 then 1 else 0) * N.offlineReads +
        (if e = 0 then copies * N.linkReadsFirst else 0) +
        (if e = 0 then 0 else 1) * N.linkReadsCopy +
        (if e = 0 then 0 else sessionsPerCopy) * N.onlineReads + 0 ≤ N.columns
    simp only [he, if_false]
    omega

/-- **The whole view over the life of a commitment**: a corollary of the whole view, where the two budgets
hold. -/
theorem wholeLife_of_wholeView {work : PartsWork L} {provers : HonestProvers L}
    {simulators : RunSimulators L} {inRange : I → Prop} {Served : I → X → Prop} {N : Budget}
    (h : WholeView work provers simulators inRange Served N) (copyNumber : ℕ → ℕ)
    (copies sessionsPerCopy : ℕ)
    (h1 : N.offlineReads + copies * N.linkReadsFirst ≤ N.columns)
    (h2 : N.linkReadsCopy + sessionsPerCopy * N.onlineReads ≤ N.columns) :
    WholeLife work provers simulators inRange Served N copyNumber copies sessionsPerCopy :=
  fun i i₀ hi => h (fun e => copyNumber (e - 1)) (commitmentLife copies sessionsPerCopy)
    (fits_commitmentLife N copies sessionsPerCopy h1 h2) i i₀ hi

end Object

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.wholeViewFollows
#print axioms VerifiableInference.Compilation.err_commitmentLife
#print axioms VerifiableInference.Compilation.wholeLife_of_wholeView
