-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/PublicRead/Privacy.lean: A SCHEME WHOSE LETTERS ARE READ OFF THE HASH FUNCTION: INDEX PRIVACY:
the proofs of Spec.privacy_pub and Spec.privacy_pub_on (ZKCP/PublicRead/Spec.lean). Definitions for
these proofs alone, and theorems with their proofs.

General theorems, over one hash function. This file states no goal of the release.

HOW IT GOES. Call "the path" the list of (string, answer) of one run of the public reading.
  REAL. Under a fixed hash function g the glued experiment is the experiment at the value that the
  reading has at g (realExp_at). The average over g of a quantity at that value is the average over
  the paths, drawn with fresh uniform answers, of the average over g WITH THE PATH LAID OVER IT
  (lintegral_path: one string at a time, by Rom.lintegral_U_resample). At a fixed path and its d the
  committer and the prover ask no string of the path, so they do not see what is laid over
  (runEager_over); the verifier does, and its view is the wired verifier's, replayed (realExp_over,
  by loop_list, ZKCP/PublicRead/Wire.lean).
  IDEAL. The glued simulator draws the path with the same law; from there on the verifier against it
  is the wired verifier against the simulator at d, replayed (idealExp_glueSim, idealExp_listSim, by
  the same loop_list).
  So both views are one mixture over paths of the replayed views at d, at the environment behind the
  replay, which is valid since validity is asked at every view. The distance of two mixtures is at
  most the average of the distances (Prob.sd_expect_le).

THE PREMISE AT d IS USED AT ADVERSARIES THAT ARE WIRED AT ARBITRARY CONSTANTS: the wired verifier
carries the path's answers as numbers of its own, whatever the simulator's own table would say at
these strings. So a simulator whose key or proofs are right only at its own answer at a public
string is shut out by the premise at d already, and nothing further is asked of the simulators (in
Spec.privacy_pub_on: but for the property's second clause at the d that are set aside).

Main names (namespace ZKCP.PublicRead).
  over, over_nil, over_cons, runEager_over   a hash function with a list laid over it.
  runPathC, runPub_eq, path_in   the public reading's paths.
  lintegral_path   the average over the hash function as an average over paths.
  realLoop_glueArg, realExp_at, eagerWorld_over, replayViewL, realExp_over   the real side.
  listSim, idealLoop_glueSim, idealExp_glueSim, idealExp_listSim   the ideal side.
  privacy_core   the two clauses for one index and one environment.
  privacy_pub_on, privacy_pub_of_on, privacy_pub   THE THEOREMS: the form with some d set aside; the
      plain form is that form at Dok := all, β := 0.

It follows the pattern of Rom/ExitPriv.lean (realExp_glue, idealExp_simOne, privacy_overOne). The
proof of realLoop_glueArg is, line for line, that of realLoop_range (ZKCP/OnRange.lean), which is
that of realLoop_withC (Rom/Blocks.lean).

Limits. Those of the head of ZKCP/PublicRead/Spec.lean.
Terms: lean/GLOSSARY.md.

-/
import ZKCP.PublicRead.Wire
import ZKCP.PublicRead.Complete

set_option autoImplicit false

noncomputable section

open scoped ENNReal
open MeasureTheory

namespace ZKCP.PublicRead
open Rom Prob
open TypedOracleCompiler.Compile.Batch.Cms (NoRepeat)

variable {lam : ℕ} {I X W PP IVK ISK Pf D : Type}

/-! ## A hash function with a list laid over it -/

/-- The hash function g with the list l laid over it. -/
def over (g : Fam (rom lam)) (l : Path lam) : Fam (rom lam) :=
  fun u s => (l.lookup s).getD (g u s)

theorem over_nil (g : Fam (rom lam)) : over g [] = g := rfl

theorem lookup_self (s : (rom lam).Dom ()) (r : (rom lam).Rng ()) (l : Path lam) :
    List.lookup s ((s, r) :: l) = some r := by
  have e : (s == s) = true := decide_eq_true rfl
  show (match s == s with
    | true => some r
    | false => List.lookup s l) = some r
  rw [e]

theorem lookup_ne {s s' : (rom lam).Dom ()} (h : s' ≠ s) (r : (rom lam).Rng ()) (l : Path lam) :
    List.lookup s' ((s, r) :: l) = List.lookup s' l := by
  have e : (s' == s) = false := decide_eq_false h
  show (match s' == s with
    | true => some r
    | false => List.lookup s' l) = List.lookup s' l
  rw [e]

theorem over_cons (g : Fam (rom lam)) (s : (rom lam).Dom ()) (r : (rom lam).Rng ())
    (l : Path lam) : over g ((s, r) :: l) = (over g l).set () s r := by
  funext u s'
  cases u
  by_cases h : s' = s
  · subst h
    show (List.lookup s' ((s', r) :: l)).getD (g () s') = (over g l).set () s' r () s'
    rw [Fam.set_self, lookup_self]
    rfl
  · show (List.lookup s' ((s, r) :: l)).getD (g () s') = (over g l).set () s r () s'
    rw [Fam.set_of_ne_point (over g l) () h r, lookup_ne h]
    rfl

/-- An algorithm that asks no string of the list does not see what is laid over. -/
theorem runEager_over {α : Type} (g : Fam (rom lam)) (l : Path lam) :
    ∀ c : Rom.OComp (rom lam) α, (c.AsksIn fun _ s => l.lookup s = none) →
      c.runEager (over g l) = c.runEager g := by
  intro c
  induction c with
  | pure a => intro _; rfl
  | sample n k ih =>
    intro h
    simp only [Rom.OComp.runEager]
    exact congrArg _ (funext fun x => ih x (h x))
  | query u q k ih =>
    intro h
    have e : over g l u q = g u q := by
      show (l.lookup q).getD (g u q) = g u q
      rw [h.1]
      rfl
    simp only [Rom.OComp.runEager, e]
    exact ih _ (h.2 _)

/-! ## The public reading's paths -/

/-- The public reading with fresh uniform answers: its value and its path. -/
def runPathC : Rom.OComp (rom lam) D → PMF (D × Path lam)
  | .pure d => PMF.pure (d, [])
  | .sample n k => (unif (Fin (n + 1))).bind fun x => runPathC (k x)
  | .query _ s k => (unif (Fin lam → Bool)).bind fun r =>
      (runPathC (k r)).map fun p => (p.1, ((show List Bool from s), r) :: p.2)

theorem runPub_eq : ∀ (Pub : Rom.OComp (rom lam) D) (l₀ : Path lam),
    runPub Pub l₀ = (runPathC Pub).map fun p => (p.1, l₀ ++ p.2) := by
  intro Pub
  induction Pub with
  | pure d =>
    intro l₀
    show PMF.pure (d, l₀) = (PMF.pure (d, [])).map _
    rw [PMF.pure_map, List.append_nil]
  | sample n k ih =>
    intro l₀
    show (unif (Fin (n + 1))).bind (fun x => runPub (k x) l₀) = ((unif (Fin (n + 1))).bind _).map _
    rw [PMF.map_bind]
    exact congrArg _ (funext fun x => ih x l₀)
  | query u s k ih =>
    intro l₀
    show (unif (Fin lam → Bool)).bind
        (fun r => runPub (k r) (l₀ ++ [((show List Bool from s), r)])) =
      ((unif (Fin lam → Bool)).bind _).map _
    rw [PMF.map_bind]
    refine congrArg _ (funext fun r => ?_)
    rw [ih r, PMF.map_comp]
    refine congrArg (fun f => PMF.map f (runPathC (k r))) (funext fun p => ?_)
    show (p.1, (l₀ ++ [((show List Bool from s), r)]) ++ p.2) = (p.1, l₀ ++ (_ :: p.2))
    rw [List.append_assoc]
    rfl

theorem runPub_nil (Pub : Rom.OComp (rom lam) D) : runPub Pub [] = runPathC Pub := by
  rw [runPub_eq]
  exact PMF.map_id _

/-- Every string of a path is a public string. -/
theorem path_in (Pt : List Bool → Prop) : ∀ Pub : Rom.OComp (rom lam) D,
    (Pub.AsksIn fun _ s => Pt s) → ∀ p ∈ (runPathC Pub).support,
      ∀ (s : (rom lam).Dom ()) (r : (rom lam).Rng ()), p.2.lookup s = some r → Pt s := by
  intro Pub
  induction Pub with
  | pure d =>
    intro _ p hp s r h
    rw [(PMF.mem_support_pure_iff _ _).mp hp] at h
    cases h
  | sample n k ih =>
    intro ha p hp
    obtain ⟨x, _, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
    exact ih x (ha x) p hx
  | query u s₀ k ih =>
    intro ha p hp s r h
    cases u
    obtain ⟨r₀, _, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
    obtain ⟨p', hp', rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    by_cases e : s = s₀
    · rw [e]
      exact ha.1
    · refine ih r₀ (ha.2 r₀) p' hp' s r ?_
      have h' : List.lookup s ((s₀, r₀) :: p'.2) = some r := h
      exact (lookup_ne e r₀ p'.2).symm.trans h'

/-- **The average over the hash function of a quantity at the reading's value is the average over
the paths of the average over the hash function with the path laid over it.** -/
theorem lintegral_path : ∀ (Pub : Rom.OComp (rom lam) D) (Φ : D → Fam (rom lam) → ℝ≥0∞),
    (∀ d l, Measurable fun g => Φ d (over g l)) → Pub.NoCoin → NoRepeat Pub →
    ∫⁻ g, Φ (Pub.det g) g ∂(Rom.U (rom lam)) =
      Prob.expect (runPathC Pub) fun p => ∫⁻ g, Φ p.1 (over g p.2) ∂(Rom.U (rom lam)) := by
  intro Pub
  induction Pub with
  | pure d =>
    intro Φ _ _ _
    show _ = Prob.expect (PMF.pure (d, [])) _
    rw [Prob.expect_pure]
    rfl
  | sample n k _ => exact fun _ _ hc => hc.elim
  | query u s k ih =>
    intro Φ hΦ hc hr
    cases u
    rw [Rom.lintegral_U_resample () s (measurable_det Φ (fun d => hΦ d []) (.query () s k))]
    show _ = Prob.expect ((unif (Fin lam → Bool)).bind fun r =>
      (runPathC (k r)).map fun p => (p.1, ((show List Bool from s), r) :: p.2)) _
    rw [Prob.expect_bind]
    refine congrArg _ (funext fun r => ?_)
    rw [Prob.expect_map]
    have h1 := ih r (fun d g => Φ d (g.set () s r))
      (fun d l => by
        have := hΦ d ((s, r) :: l)
        simpa only [over_cons] using this) (hc r) (hr r).2
    refine Eq.trans (lintegral_congr fun g => ?_) (h1.trans ?_)
    · show Φ ((k ((g.set () s r) () s)).det (g.set () s r)) (g.set () s r) = _
      rw [Fam.set_self, det_set s r g (k r) (hr r).1]
    · refine congrArg _ (funext fun p => lintegral_congr fun g => ?_)
      show Φ p.1 ((over g p.2).set () s r) = Φ p.1 (over g ((s, r) :: p.2))
      rw [over_cons]

/-! ## The real side -/

/-- Behind the key the glued scheme's loop is the loop at the d that the prover's key keeps. -/
theorem realLoop_glueArg (Pub : Rom.OComp (rom lam) D)
    (A : D → Gen.Arg (rom lam) I X W IVK ISK Pf) (Z : Gen.ViewEnv (rom lam) IVK X W Pf) (d : D)
    (isk : ISK) (V : Gen.AdvVerifier (rom lam) X Pf) : ∀ (n : ℕ) (v : Gen.View (rom lam) IVK X Pf),
    Gen.realLoop (glueArg Pub A) Z (d, isk) V n v = Gen.realLoop (A d) Z isk V n v := by
  induction V with
  | halt => intro n v; rfl
  | query o q k ih =>
    intro n v
    simp only [Gen.realLoop]
    exact congrArg _ (funext fun r => ih r n _)
  | sample m k ih =>
    intro n v
    simp only [Gen.realLoop]
    exact congrArg _ (funext fun r => ih r n _)
  | request k ih =>
    intro n v
    cases n with
    | zero => rfl
    | succ n =>
      simp only [Gen.realLoop]
      cases Z v with
      | none => rfl
      | some b => exact congrArg _ (funext fun πs => ih _ n _)

/-- **Under a fixed hash function the glued real experiment is the real experiment at the one
value.** -/
theorem realExp_at {Pub : Rom.OComp (rom lam) D} (hc : Pub.NoCoin)
    (A : D → Gen.Arg (rom lam) I X W IVK ISK Pf) (Vt : IVK → Gen.AdvVerifier (rom lam) X Pf)
    (Z : Gen.ViewEnv (rom lam) IVK X W Pf) (i : I) (N : ℕ) (g : Fam (rom lam)) :
    (Gen.realExp (glueArg Pub A) Vt Z i N).runEager g =
      (Gen.realExp (A (Pub.det g)) Vt Z i N).runEager g := by
  show (((glueArg Pub A).C i).bind fun key =>
      Gen.realLoop (glueArg Pub A) Z key.2 (Vt key.1) N ⟨key.1, [], [], []⟩).runEager g =
    (((A (Pub.det g)).C i).bind fun key =>
      Gen.realLoop (A (Pub.det g)) Z key.2 (Vt key.1) N ⟨key.1, [], [], []⟩).runEager g
  rw [Rom.OComp.runEager_bind, Rom.OComp.runEager_bind, commit_at hc A i g, PMF.bind_map]
  refine congrArg _ (funext fun key => ?_)
  show (Gen.realLoop (glueArg Pub A) Z (Pub.det g, key.2) (Vt key.1) N ⟨key.1, [], [], []⟩).runEager
    g = _
  rw [realLoop_glueArg]

/-- The real challenger under a hash function with a list laid over it is the real challenger with
the list in front, if the prover asks no string of the list. -/
theorem eagerWorld_over (A : Gen.Arg (rom lam) I X W IVK ISK Pf) (isk : ISK) (g : Fam (rom lam))
    (l : Path lam) (hP : ∀ b, (A.P isk b).AsksIn fun _ s => l.lookup s = none) :
    eagerWorld A isk (over g l) = listWorld l (eagerWorld A isk g) := by
  have ha : (fun (_ : Unit) (o : (rom lam).ι) (q : (rom lam).Dom o) =>
        (PMF.pure (over g l o q, ()) : PMF ((rom lam).Rng o × Unit))) =
      fun (st : Unit) (u : (rom lam).ι) (s : (rom lam).Dom u) =>
        match l.lookup s with
        | some r => PMF.pure (r, st)
        | none => PMF.pure (g u s, ()) := by
    funext st u s
    cases st
    show PMF.pure ((l.lookup s).getD (g u s), ()) = _
    cases l.lookup s <;> rfl
  have hs : (fun (_ : Unit) (b : Gen.Batch X W) =>
        ((A.P isk b.pairs).runEager (over g l)).map fun πs => (b.released πs.val, ())) =
      fun _ b => ((A.P isk b.pairs).runEager g).map fun πs => (b.released πs.val, ()) := by
    funext _ b
    rw [runEager_over g l _ (hP b.pairs)]
  exact congrArg₂ (GWorld.mk Unit) ha hs

/-- The verifier's view, recovered from the wired verifier's view. -/
def replayViewL (l : Path lam) (Vt : IVK → Gen.AdvVerifier (rom lam) X Pf) (N : ℕ)
    (v : Gen.View (rom lam) IVK X Pf) : Gen.View (rom lam) IVK X Pf :=
  (replayL l (Vt v.ivk) N (Log.ofView v)).view v.ivk

/-- **The real experiment under a hash function with a list laid over it** is the real experiment of
the wired verifier, replayed, if the committer and the prover ask no string of the list. -/
theorem realExp_over (A : Gen.Arg (rom lam) I X W IVK ISK Pf)
    (Vt : IVK → Gen.AdvVerifier (rom lam) X Pf) (Z : Gen.ViewEnv (rom lam) IVK X W Pf) (i : I)
    (N : ℕ) (g : Fam (rom lam)) (l : Path lam)
    (hC : (A.C i).AsksIn fun _ s => l.lookup s = none)
    (hP : ∀ isk b, (A.P isk b).AsksIn fun _ s => l.lookup s = none) :
    (Gen.realExp A Vt Z i N).runEager (over g l) =
      ((Gen.realExp A (fun ivk => wireV l (Vt ivk)) (fun v => Z (replayViewL l Vt N v)) i
        N).runEager g).map (replayViewL l Vt N) := by
  have e1 : Gen.realExp A Vt Z i N = (A.C i).bind fun key =>
      Gen.realLoop A Z key.2 (Vt key.1) N ((Log.nil : Log (rom lam) X Pf).view key.1) := rfl
  have e2 : Gen.realExp A (fun ivk => wireV l (Vt ivk)) (fun v => Z (replayViewL l Vt N v)) i N =
      (A.C i).bind fun key =>
        Gen.realLoop A (fun v => Z (replayViewL l Vt N v)) key.2 (wireV l (Vt key.1)) N
          ((Log.nil : Log (rom lam) X Pf).view key.1) := rfl
  rw [e1, e2]
  simp only [Rom.OComp.runEager_bind, runEager_over g l _ hC, PMF.map_bind]
  refine congrArg _ (funext fun key => ?_)
  rw [realLoop_eq, realLoop_eq, lLoop_congr (eagerWorld_over A key.2 g l (hP key.2)), loop_list,
    PMF.map_comp, PMF.map_comp]
  rfl

/-! ## The ideal side -/

/-- A simulator with the list in front. -/
def listSim (l : Path lam) (Sim : Gen.Simulator (rom lam) PP IVK X Pf) :
    Gen.Simulator (rom lam) PP IVK X Pf where
  St := Sim.St
  init := Sim.init
  answer := fun st u s =>
    match l.lookup s with
    | some r => PMF.pure (r, st)
    | none => Sim.answer st u s
  prove := Sim.prove

theorem simWorld_listSim (l : Path lam) (Sim : Gen.Simulator (rom lam) PP IVK X Pf) :
    (simWorld (listSim l Sim) : GWorld (rom lam) X W Pf) = listWorld l (simWorld Sim) := rfl

/-- Behind its first move the glued simulator is the simulator at d with the list in front. -/
theorem idealLoop_glueSim (Pub : Rom.OComp (rom lam) D)
    (Sm : D → Gen.Simulator (rom lam) PP IVK X Pf) (Z : Gen.ViewEnv (rom lam) IVK X W Pf) (d : D)
    (l : Path lam) (V : Gen.AdvVerifier (rom lam) X Pf) :
    ∀ (n : ℕ) (v : Gen.View (rom lam) IVK X Pf) (st : (Sm d).St),
      Gen.idealLoop (glueSim Pub Sm) Z V n v ⟨d, l, st⟩ =
        Gen.idealLoop (listSim l (Sm d)) Z V n v st := by
  induction V with
  | halt => intro n v st; rfl
  | sample m k ih =>
    intro n v st
    simp only [Gen.idealLoop]
    exact congrArg _ (funext fun r => ih r n _ st)
  | query u s k ih =>
    intro n v st
    simp only [Gen.idealLoop]
    cases hl : l.lookup s with
    | some r =>
      have e1 : (glueSim Pub Sm).answer ⟨d, l, st⟩ u s =
          PMF.pure (r, (⟨d, l, st⟩ : (glueSim Pub Sm).St)) := by
        simp only [glueSim, hl]
        rfl
      have e2 : (listSim l (Sm d)).answer st u s = PMF.pure (r, st) := by
        simp only [listSim, hl]
        rfl
      rw [e1, e2]
      refine (PMF.pure_bind _ _).trans (Eq.trans ?_ (PMF.pure_bind _ _).symm)
      exact ih r n _ st
    | none =>
      have e1 : (glueSim Pub Sm).answer ⟨d, l, st⟩ u s =
          ((Sm d).answer st u s).map fun a : (rom lam).Rng u × (Sm d).St =>
            (a.1, (⟨d, l, a.2⟩ : (glueSim Pub Sm).St)) := by
        simp only [glueSim, hl]
      have e2 : (listSim l (Sm d)).answer st u s = (Sm d).answer st u s := by
        simp only [listSim, hl]
      rw [e1, e2]
      refine (PMF.bind_map _ _ _).trans ?_
      exact congrArg _ (funext fun a : (rom lam).Rng u × (Sm d).St => ih a.1 n _ a.2)
  | request k ih =>
    intro n v st
    cases n with
    | zero => rfl
    | succ n =>
      simp only [Gen.idealLoop]
      cases Z v with
      | none => rfl
      | some b =>
        show (((Sm d).prove st b.ownX).map fun a =>
          (a.1, (⟨d, l, a.2⟩ : (glueSim Pub Sm).St))).bind _ = _
        rw [PMF.bind_map]
        exact congrArg _ (funext fun a => ih _ n _ a.2)

/-- **The glued ideal experiment is a mixture over paths.** -/
theorem idealExp_glueSim (R : Gen.RelPair I X W PP) (Pub : Rom.OComp (rom lam) D)
    (Sm : D → Gen.Simulator (rom lam) PP IVK X Pf) (Vt : IVK → Gen.AdvVerifier (rom lam) X Pf)
    (Z : Gen.ViewEnv (rom lam) IVK X W Pf) (i : I) (N : ℕ) :
    Gen.idealExp R (glueSim Pub Sm) Vt Z i N =
      (runPathC Pub).bind fun p => Gen.idealExp R (listSim p.2 (Sm p.1)) Vt Z i N := by
  show ((runPub Pub []).bind fun p => ((Sm p.1).init (R.pp i) N).map fun o =>
      (o.1, (⟨p.1, p.2, o.2⟩ : (glueSim Pub Sm).St))).bind (fun out =>
        Gen.idealLoop (glueSim Pub Sm) Z (Vt out.1) N ⟨out.1, [], [], []⟩ out.2) = _
  rw [runPub_nil, PMF.bind_bind]
  refine congrArg _ (funext fun p => ?_)
  rw [PMF.bind_map]
  exact congrArg _ (funext fun o => idealLoop_glueSim Pub Sm Z p.1 p.2 _ N _ o.2)

/-- The ideal experiment with the list in front is the ideal experiment of the wired verifier,
replayed. -/
theorem idealExp_listSim (R : Gen.RelPair I X W PP) (l : Path lam)
    (Sim : Gen.Simulator (rom lam) PP IVK X Pf) (Vt : IVK → Gen.AdvVerifier (rom lam) X Pf)
    (Z : Gen.ViewEnv (rom lam) IVK X W Pf) (i : I) (N : ℕ) :
    Gen.idealExp R (listSim l Sim) Vt Z i N =
      (Gen.idealExp R Sim (fun ivk => wireV l (Vt ivk)) (fun v => Z (replayViewL l Vt N v)) i N).map
        (replayViewL l Vt N) := by
  have e1 : Gen.idealExp R (listSim l Sim) Vt Z i N = (Sim.init (R.pp i) N).bind fun out =>
      Gen.idealLoop (listSim l Sim) Z (Vt out.1) N ((Log.nil : Log (rom lam) X Pf).view out.1)
        out.2 := rfl
  have e2 : Gen.idealExp R Sim (fun ivk => wireV l (Vt ivk)) (fun v => Z (replayViewL l Vt N v)) i N
      = (Sim.init (R.pp i) N).bind fun out =>
        Gen.idealLoop Sim (fun v => Z (replayViewL l Vt N v)) (wireV l (Vt out.1)) N
          ((Log.nil : Log (rom lam) X Pf).view out.1) out.2 := rfl
  rw [e1, e2, PMF.map_bind]
  refine congrArg _ (funext fun out => ?_)
  rw [idealLoop_eq, idealLoop_eq]
  have hl := loop_list l (simWorld (W := W) Sim) (Vt out.1) (fun lg => Z (Log.view out.1 lg)) N
    out.2
  change PMF.map _ (lLoop (listWorld l (simWorld Sim)) _ _ _ _ _) = _
  rw [hl, PMF.map_comp, PMF.map_comp]
  rfl

/-! ## The two clauses -/

open Classical in
/-- **The two clauses for one index and one environment.** Dok: the values at which privacy is
known; β bounds the probability that the reading's value lies outside. -/
theorem privacy_core (R : Gen.RelPair I X W PP) (A : D → Gen.Arg (rom lam) I X W IVK ISK Pf)
    (Sm : D → Gen.Simulator (rom lam) PP IVK X Pf) (B : ℕ) (ζ : ℕ → ℕ → ℝ≥0∞) (β : ℝ≥0∞)
    (Pt : List Bool → Prop) (Dok : D → Prop) (Pub : Rom.OComp (rom lam) D) (hc : Pub.NoCoin)
    (hp : Pub.AsksIn fun _ s => Pt s) (hr : NoRepeat Pub) (i : I)
    (hC : ∀ d, Dok d → ((A d).C i).AsksIn fun _ s => ¬ Pt s)
    (hP : ∀ d, Dok d → ∀ isk b, ((A d).P isk b).AsksIn fun _ s => ¬ Pt s)
    (hA : ∀ d, Dok d → ∀ Z' : Gen.ViewEnv (rom lam) IVK X W Pf, Z'.IsValid R B i →
      Gen.PrivacyFor R (A d) (Sm d) ζ i Z')
    (tV : ℕ)
    (hcons : ∀ d (Vt' : IVK → Gen.AdvVerifier (rom lam) X Pf)
      (Z' : Gen.ViewEnv (rom lam) IVK X W Pf) (N : ℕ), Z'.IsValid R B i →
      (∀ ivk, (Vt' ivk).QueryBound tV) →
      pr (Gen.idealExp R (Sm d) Vt' Z' i N) {v | ¬ Gen.TraceConsistent v.trace} = 0)
    (hβ : pr (runPub Pub []) {p | ¬ Dok p.1} ≤ β)
    (Z : Gen.ViewEnv (rom lam) IVK X W Pf) (hZ : Z.IsValid R B i)
    (Vt : IVK → Gen.AdvVerifier (rom lam) X Pf) (N : ℕ) (hb : ∀ ivk, (Vt ivk).QueryBound tV) :
    sd (fun T => Rom.Pr (Gen.realExp (glueArg Pub A) Vt Z i N) (fun _ => T))
        (fun T => pr (Gen.idealExp R (glueSim Pub Sm) Vt Z i N) T) ≤ ζ tV N + β ∧
      pr (Gen.idealExp R (glueSim Pub Sm) Vt Z i N) {v | ¬ Gen.TraceConsistent v.trace} = 0 := by
  have hZ' : ∀ l : Path lam, Gen.ViewEnv.IsValid R B (fun v => Z (replayViewL l Vt N v)) i :=
    fun l v b hv => hZ _ b hv
  have hb' : ∀ (l : Path lam) ivk, (wireV l (Vt ivk)).QueryBound tV :=
    fun l ivk => queryBound_wireV l (Vt ivk) tV (hb ivk)
  have hover : ∀ l : Path lam, Measurable fun g : Fam (rom lam) => over g l := fun l =>
    measurable_pi_iff.2 fun u => measurable_pi_iff.2 fun q => by
      have e : (fun g : Fam (rom lam) => over g l u q) = fun g => (l.lookup q).getD (g u q) := rfl
      rw [e]
      cases l.lookup q with
      | some r => exact measurable_const
      | none => exact (measurable_pi_apply q).comp (measurable_pi_apply u)
  -- the real side as a mixture over paths
  have hreal : ∀ T, Rom.Pr (Gen.realExp (glueArg Pub A) Vt Z i N) (fun _ => T) =
      Prob.expect (runPathC Pub) fun p =>
        ∫⁻ g, Rom.PrCoins (over g p.2) (Gen.realExp (A p.1) Vt Z i N) T ∂(Rom.U (rom lam)) := by
    intro T
    unfold Rom.Pr
    rw [← lintegral_path Pub (fun d g => Rom.PrCoins g (Gen.realExp (A d) Vt Z i N) T) ?_ hc hr]
    · refine lintegral_congr fun g => ?_
      unfold Rom.PrCoins
      rw [realExp_at hc A Vt Z i N g]
    · exact fun d l => (Rom.measurable_PrCoins _ _).comp (hover l)
  -- the ideal side as a mixture over paths
  have hideal : ∀ T, pr (Gen.idealExp R (glueSim Pub Sm) Vt Z i N) T =
      Prob.expect (runPathC Pub) fun p =>
        pr (Gen.idealExp R (listSim p.2 (Sm p.1)) Vt Z i N) T := by
    intro T
    rw [idealExp_glueSim, pr_bind]
  constructor
  · simp only [hreal, hideal]
    refine le_trans (sd_expect_le (runPathC Pub)
      (fun p T => ∫⁻ g, Rom.PrCoins (over g p.2) (Gen.realExp (A p.1) Vt Z i N) T
        ∂(Rom.U (rom lam)))
      (fun p T => pr (Gen.idealExp R (listSim p.2 (Sm p.1)) Vt Z i N) T)) ?_
    refine le_trans (expect_le_pr_add (runPathC Pub) _ {p | ¬ Dok p.1} (ε := ζ tV N)
      (fun p => sd_le_one
        (fun T => (lintegral_mono fun g => pr_le_one _ _).trans (by simp))
        (fun T => pr_le_one _ _)) fun p hps hpd => ?_) ?_
    · have hd : Dok p.1 := by
        by_contra hn
        exact hpd hn
      have hoff : ∀ (o : (rom lam).ι) (q : (rom lam).Dom o), ¬ Pt q → p.2.lookup q = none := by
        intro o q hq
        cases o
        cases hl : p.2.lookup q with
        | none => rfl
        | some r => exact absurd (path_in Pt Pub hp p hps q r hl) hq
      have hX : ∀ T, ∫⁻ g, Rom.PrCoins (over g p.2) (Gen.realExp (A p.1) Vt Z i N) T
          ∂(Rom.U (rom lam)) =
          Rom.Pr (Gen.realExp (A p.1) (fun ivk => wireV p.2 (Vt ivk))
            (fun v => Z (replayViewL p.2 Vt N v)) i N)
            (fun _ => replayViewL p.2 Vt N ⁻¹' T) := by
        intro T
        unfold Rom.Pr Rom.PrCoins
        refine lintegral_congr fun g => ?_
        rw [realExp_over (A p.1) Vt Z i N g p.2 (Rom.OComp.AsksIn.mono hoff (hC p.1 hd))
          (fun isk b => Rom.OComp.AsksIn.mono hoff (hP p.1 hd isk b)), pr_map]
      have hY : ∀ T, pr (Gen.idealExp R (listSim p.2 (Sm p.1)) Vt Z i N) T =
          pr (Gen.idealExp R (Sm p.1) (fun ivk => wireV p.2 (Vt ivk))
            (fun v => Z (replayViewL p.2 Vt N v)) i N) (replayViewL p.2 Vt N ⁻¹' T) := by
        intro T
        rw [idealExp_listSim, pr_map]
      simp only [hX, hY]
      exact (sd_comap_le _ _ (replayViewL p.2 Vt N)).trans
        (hA p.1 hd _ (hZ' p.2) tV _ N (hb' p.2)).1
    · rw [runPub_nil] at hβ
      rw [add_comm]
      exact add_le_add le_rfl hβ
  · rw [hideal]
    refine le_antisymm (expect_le_of_forall_le _ fun p _ => ?_) (zero_le _)
    rw [idealExp_listSim, pr_map]
    refine le_trans (pr_mono _ ?_) (le_of_eq (hcons p.1 _ _ N (hZ' p.2) (hb' p.2)))
    intro v hv hcv
    exact hv (consistent_replayL p.2 (Vt v.ivk) N (Log.ofView v) hcv)

/-! ## The theorems -/

/-- **Index privacy, where it is known at the d of Dok alone.** -/
theorem privacy_pub_on : Spec.privacy_pub_on := by
  intro lam I X W PP IVK ISK Pf D R A Sm B ζ β ok Pt Dok Pub hc hp hr hC hP hA hS hβ i hi Z hZ tV Vt
    N hb
  refine privacy_core R A Sm B ζ β Pt Dok Pub hc hp hr i (fun d hd => hC d hd i) hP
    (fun d hd Z' hZ' => hA d hd i hi Z' hZ') tV (fun d Vt' Z' N' hZ' hb' => ?_)
    (le_of_eq_of_le (reading_law lam D Pub hc hr {d | ¬ Dok d}).symm hβ) Z hZ Vt N hb
  by_cases hd : Dok d
  · exact (hA d hd i hi Z' hZ' tV Vt' N' hb').2
  · exact hS d hd i hi Z' hZ' tV Vt' N' hb'

/-- **The plain form is the form _on at Dok := all, β := 0.** -/
theorem privacy_pub_of_on : Spec.privacy_pub_on → Spec.privacy_pub := by
  intro H lam I X W PP IVK ISK Pf D R A Sm B ζ ok Pt Pub hc hp hr hC hP hA
  have h := H lam I X W PP IVK ISK Pf D R A Sm B ζ 0 ok Pt (fun _ => True) Pub hc hp hr
    (fun d _ => hC d) (fun d _ => hP d) (fun d _ => hA d) (fun d hd => absurd trivial hd)
    (le_of_eq (by
      rw [reading_law lam D Pub hc hr]
      exact pr_eq_zero_of_forall_not_mem _ fun _ _ h => h trivial))
  simpa only [add_zero] using h

/-- **Index privacy on a range passes to the glued scheme, with the glued simulator, at the same
bound.** -/
theorem privacy_pub : Spec.privacy_pub := privacy_pub_of_on privacy_pub_on

end ZKCP.PublicRead

#print axioms ZKCP.PublicRead.privacy_pub_on
#print axioms ZKCP.PublicRead.privacy_pub_of_on
#print axioms ZKCP.PublicRead.privacy_pub
