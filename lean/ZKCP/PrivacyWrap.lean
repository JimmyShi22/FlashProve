-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/PrivacyWrap.lean: the step by which strong index privacy (ZKCP/Defs.lean) survives a re-packing
of the honest committer's and prover's outputs.
The outer scheme is made from an inner one (`Wrap` holds the maps; `PrivacyFor.wrap` takes any `Arg`
with the output distributions of such a scheme: hB, hP): the committer makes at most one more query
to the hash function, at a string computed from the inner key; the outer key is computed from the
inner key and the answer; each outer proof from the inner key and an inner proof; instances and
witnesses are mapped. "Key" is the verifier's key (`IVK`, ZKCP/Defs.lean).
`PrivacyFor.wrap`: under the hypotheses of its statement, if the inner scheme has privacy with the
simulator S and the bound ζ, at an inner index and at the environment `Wrap.env Z`, then the outer
one has it at an outer index and at the environment Z with the simulator `Wrap.sim` and the bound
ζ (t + 1) N. The one query more is the one that the reduction's verifier makes in the committer's
place. Whoever uses the step for all environments has to show that `Wrap.env Z` is valid where Z
is.
The hypotheses on the committers and provers are about output distributions under each fixed hash
function: both committers are functions of one random element. Nothing here is about a particular
scheme.
-/
import ZKCP.KeyTag
import ZKCP.SameRun
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP

variable {lam : ℕ} {I X W PP IVK ISK Pf : Type} {I' X' W' PP' IVK' ISK' Pf' : Type}

/-- How the outer scheme's keys, proofs and instances are made from the inner scheme's. -/
structure Wrap (lam : ℕ) (IVK X W Pf IVK' X' W' Pf' : Type) where
  /-- the committer's further query, if any, from the inner key -/
  ask : IVK → Option Str
  /-- the outer key, from the inner key and the answer to that query -/
  key : IVK → Option (Digest lam) → IVK'
  /-- an outer proof, from the inner key and an inner proof -/
  proof : IVK → Pf → Pf'
  /-- an outer instance as an inner one -/
  inst : X' → X
  /-- an outer witness as an inner one -/
  wit : W' → W
  /-- an inner instance as an outer one -/
  back : X → X'

namespace Wrap

variable (w : Wrap lam IVK X W Pf IVK' X' W' Pf')

/-- The outer view, from the view of the reduction's verifier, whose first query is the committer's
further query. -/
def view (v : View lam IVK X Pf) : View lam IVK' X' Pf' :=
  ⟨w.key v.ivk (if (w.ask v.ivk).isSome then v.trace.head?.map Prod.snd else none),
   v.sessions.map fun s => (w.back s.1, w.proof v.ivk s.2),
   if (w.ask v.ivk).isSome then v.trace.tail else v.trace, v.coins⟩

/-- The first query has been made, if there is one. -/
def Good (v : View lam IVK X Pf) : Prop := (w.ask v.ivk).isSome = true → v.trace ≠ []

theorem view_trace {v : View lam IVK X Pf} (hv : w.Good v) (e : Str × Digest lam) :
    w.view { v with trace := v.trace ++ [e] }
      = { w.view v with trace := (w.view v).trace ++ [e] } := by
  by_cases h : (w.ask v.ivk).isSome = true
  · have hne := hv h
    cases ht : v.trace with
    | nil => exact absurd ht hne
    | cons a t => simp [view, h, ht]
  · simp [view, h]

theorem good_trace {v : View lam IVK X Pf} (e : Str × Digest lam) :
    w.Good { v with trace := v.trace ++ [e] } := fun _ => by simp

theorem view_coins (v : View lam IVK X Pf) (r : ℕ) :
    w.view { v with coins := v.coins ++ [r] }
      = { w.view v with coins := (w.view v).coins ++ [r] } := rfl

theorem view_sessions (v : View lam IVK X Pf) (x : X) (π : Pf) :
    w.view { v with sessions := v.sessions ++ [(x, π)] }
      = { w.view v with sessions := (w.view v).sessions ++ [(w.back x, w.proof v.ivk π)] } := by
  simp [view]

/-- An outer verifier, after its key, as an inner one. -/
def pull (ivk : IVK) : AdvVerifier lam X' Pf' → AdvVerifier lam X Pf
  | .halt => .halt
  | .query q k => .query q fun r => pull ivk (k r)
  | .sample n k => .sample n fun r => pull ivk (k r)
  | .request k => .request fun x π => pull ivk (k (w.back x) (w.proof ivk π))

theorem queryBound_pull (ivk : IVK) : ∀ (a : AdvVerifier lam X' Pf') (n : ℕ), a.QueryBound n →
    (w.pull ivk a).QueryBound n
  | .halt, _, _ => trivial
  | .query _ _, 0, h => h.elim
  | .query _ k, n + 1, h => fun r => queryBound_pull ivk (k r) n (h r)
  | .sample _ k, n, h => fun r => queryBound_pull ivk (k r) n (h r)
  | .request k, n, h => fun x π => queryBound_pull ivk (k (w.back x) (w.proof ivk π)) n
      (h (w.back x) (w.proof ivk π))

theorem queryBound_succ :
    ∀ (a : AdvVerifier lam X Pf) (n : ℕ), a.QueryBound n → a.QueryBound (n + 1)
  | .halt, _, _ => trivial
  | .query _ _, 0, h => h.elim
  | .query _ k, n + 1, h => fun r => queryBound_succ (k r) n (h r)
  | .sample _ k, n, h => fun r => queryBound_succ (k r) n (h r)
  | .request k, n, h => fun x π => queryBound_succ (k x π) n (h x π)

/-- The reduction's verifier: it makes the committer's further query itself, computes the outer key,
and goes on as the outer verifier. -/
def verifier (Vt : IVK' → AdvVerifier lam X' Pf') (ivk : IVK) : AdvVerifier lam X Pf :=
  match w.ask ivk with
  | some s => .query s fun r => w.pull ivk (Vt (w.key ivk (some r)))
  | none => w.pull ivk (Vt (w.key ivk none))

theorem queryBound_verifier {Vt : IVK' → AdvVerifier lam X' Pf'} {t : ℕ}
    (h : ∀ k, (Vt k).QueryBound t) (ivk : IVK) : (w.verifier Vt ivk).QueryBound (t + 1) := by
  unfold verifier
  cases w.ask ivk with
  | none => exact queryBound_succ _ _ (w.queryBound_pull ivk _ _ (h _))
  | some s => exact fun r => w.queryBound_pull ivk _ _ (h _)

/-- The reduction's environment. -/
def env (Z : ViewEnv lam IVK' X' W' Pf') : ViewEnv lam IVK X W Pf :=
  fun v => (Z (w.view v)).map fun xw => (w.inst xw.1, w.wit xw.2)

/-- The outer simulator: the inner one, which also answers the committer's further query; its state
keeps the inner key. -/
def sim (S : Simulator lam PP IVK X Pf) (h : PP' → PP) : Simulator lam PP' IVK' X' Pf'
    where
  St := S.St × IVK
  init p n := (S.init (h p) n).bind fun o =>
    match w.ask o.1 with
    | some s => (S.answer o.2 s).map fun a => (w.key o.1 (some a.1), (a.2, o.1))
    | none => PMF.pure (w.key o.1 none, (o.2, o.1))
  answer st q := (S.answer st.1 q).map fun a => (a.1, (a.2, st.2))
  prove st x := (S.prove st.1 (w.inst x)).map fun o => (w.proof st.2 o.1, (o.2, st.2))

/-! ## The real experiment, under a fixed hash function -/

section Real
variable {A : Arg lam I X W IVK ISK Pf} {B : Arg lam I' X' W' IVK' ISK' Pf'}
    (Z : ViewEnv lam IVK' X' W' Pf') (f : Oracle lam) (ivk : IVK) (isk : ISK) (isk' : ISK')
  (hP : ∀ v x' w', Z v = some (x', w') → (B.P isk' x' w').run f =
      ((A.P isk (w.inst x') (w.wit w')).run f).map (w.proof ivk))
  (hb : ∀ v x' w', Z v = some (x', w') → w.back (w.inst x') = x')
include hP hb

theorem realLoop_run :
    ∀ (a : AdvVerifier lam X' Pf') (n : ℕ) (v : View lam IVK X Pf), v.ivk = ivk → w.Good v →
      (realLoop B Z isk' a n (w.view v)).run f
        = ((realLoop A (w.env Z) isk (w.pull ivk a) n v).run f).map w.view
  | .halt, _, _, _, _ => (PMF.pure_map _ _).symm
  | .query q k, n, v, hi, hv => by
      show (realLoop B Z isk' (k (f q)) n { w.view v with trace := (w.view v).trace ++ [(q, f q)]
          }).run f
        = ((realLoop A (w.env Z) isk (w.pull ivk (k (f q))) n
            { v with trace := v.trace ++ [(q, f q)] }).run f).map w.view
      rw [← w.view_trace hv]
      exact realLoop_run (k (f q)) n _ hi (w.good_trace _)
  | .sample m k, n, v, hi, hv => by
      show (PMF.uniformOfFintype (Fin (m + 1))).bind (fun r =>
          (realLoop B Z isk' (k r) n { w.view v with coins := (w.view v).coins ++ [r.val] }).run f)
        = ((PMF.uniformOfFintype (Fin (m + 1))).bind fun r =>
            (realLoop A (w.env Z) isk (w.pull ivk (k r)) n
            { v with coins := v.coins ++ [r.val] }).run f).map w.view
      rw [PMF.map_bind]
      exact congrArg _ (funext fun r => realLoop_run (k r) n { v with coins := v.coins ++ [r.val] }
          hi hv)
  | .request _, 0, _, _, _ => (PMF.pure_map _ _).symm
  | .request k, n + 1, v, hi, hv => by
      simp only [realLoop, pull, env]
      cases hz : Z (w.view v) with
      | none => exact (PMF.pure_map _ _).symm
      | some xw =>
          show ((B.P isk' xw.1 xw.2).bind fun π => realLoop B Z isk' (k xw.1 π) n
              { w.view v with sessions := (w.view v).sessions ++ [(xw.1, π)] }).run f
            = (((A.P isk (w.inst xw.1) (w.wit xw.2)).bind fun π => realLoop A (w.env Z) isk
                (w.pull ivk (k (w.back (w.inst xw.1)) (w.proof ivk π))) n
                { v with sessions := v.sessions ++ [(w.inst xw.1, π)] }).run f).map w.view
          rw [run_bind, run_bind, hP (w.view v) xw.1 xw.2 hz, PMF.bind_map, PMF.map_bind,
            hb (w.view v) xw.1 xw.2 hz]
          refine congrArg _ (funext fun π => ?_)
          have e : ({ w.view v with sessions := (w.view v).sessions ++ [(xw.1, w.proof ivk π)] } :
              View lam IVK' X' Pf')
              = w.view { v with sessions := v.sessions ++ [(w.inst xw.1, π)] } := by
            rw [w.view_sessions, hb (w.view v) xw.1 xw.2 hz, hi]
          show (realLoop B Z isk' (k xw.1 (w.proof ivk π)) n
              { w.view v with sessions := (w.view v).sessions ++ [(xw.1, w.proof ivk π)] }).run f
            = _
          rw [e]
          exact realLoop_run (k xw.1 (w.proof ivk π)) n _ hi hv

/-- From the key on, under hP and hb of this section and under the hash function f: the reduction's
verifier makes the further query, then the loops agree. -/
theorem realStart_run (Vt : IVK' → AdvVerifier lam X' Pf') (N : ℕ) :
    (realLoop B Z isk' (Vt (w.key ivk ((w.ask ivk).map f))) N
        ⟨w.key ivk ((w.ask ivk).map f), [], [], []⟩).run f
      = ((realLoop A (w.env Z) isk (w.verifier Vt ivk) N ⟨ivk, [], [], []⟩).run f).map w.view := by
  unfold verifier
  cases hq : w.ask ivk with
  | none =>
      have e : (⟨w.key ivk none, [], [], []⟩ : View lam IVK' X' Pf') = w.view ⟨ivk, [], [], []⟩ :=
          by simp [view, hq]
      show (realLoop B Z isk' (Vt (w.key ivk none)) N ⟨w.key ivk none, [], [], []⟩).run f = _
      rw [e]
      exact w.realLoop_run Z f ivk isk isk' hP hb _ N ⟨ivk, [], [], []⟩ rfl
          (fun h => by simp [hq] at h)
  | some s =>
      have e : (⟨w.key ivk (some (f s)), [], [], []⟩ : View lam IVK' X' Pf') = w.view
          ⟨ivk, [], [(s, f s)], []⟩ := by simp [view, hq]
      show (realLoop B Z isk' (Vt (w.key ivk (some (f s)))) N
          ⟨w.key ivk (some (f s)), [], [], []⟩).run f
        = ((realLoop A (w.env Z) isk (w.pull ivk (Vt (w.key ivk (some (f s))))) N
            ⟨ivk, [], [] ++ [(s, f s)], []⟩).run f).map w.view
      rw [e]
      exact w.realLoop_run Z f ivk isk isk' hP hb _ N ⟨ivk, [], [(s, f s)], []⟩ rfl
          (fun _ => by simp)

end Real

/-! ## The ideal experiment -/

section Ideal
variable (S : Simulator lam PP IVK X Pf) (h : PP' → PP) (Z : ViewEnv lam IVK' X' W' Pf') (ivk : IVK)
  (hb : ∀ v x' w', Z v = some (x', w') → w.back (w.inst x') = x')
include hb

theorem idealLoop_eq : ∀ (a : AdvVerifier lam X' Pf') (n : ℕ) (v : View lam IVK X Pf) (s : S.St),
    v.ivk = ivk → w.Good v →
    idealLoop (w.sim S h) Z a n (w.view v) (s, ivk) = (idealLoop S (w.env Z) (w.pull ivk a) n v
        s).map w.view
  | .halt, _, _, _, _, _ => (PMF.pure_map _ _).symm
  | .query q k, n, v, s, hi, hv => by
      simp only [idealLoop, pull, PMF.map_bind]
      show ((S.answer s q).map fun a => (a.1, (a.2, ivk))).bind _ = _
      rw [PMF.bind_map]
      refine congrArg _ (funext fun out => ?_)
      show idealLoop (w.sim S h) Z (k out.1) n { w.view v with trace := (w.view v).trace ++
          [(q, out.1)] } (out.2, ivk) = _
      rw [← w.view_trace hv]
      exact idealLoop_eq (k out.1) n _ out.2 hi (w.good_trace _)
  | .sample m k, n, v, s, hi, hv => by
      simp only [idealLoop, pull, PMF.map_bind]
      exact congrArg _ (funext fun r => idealLoop_eq (k r) n { v with coins := v.coins ++ [r.val] }
          s hi hv)
  | .request _, 0, _, _, _, _ => (PMF.pure_map _ _).symm
  | .request k, n + 1, v, s, hi, hv => by
      simp only [idealLoop, pull, env]
      cases hz : Z (w.view v) with
      | none => exact (PMF.pure_map _ _).symm
      | some xw =>
          show ((S.prove s (w.inst xw.1)).map fun o => (w.proof ivk o.1, (o.2, ivk))).bind
              (fun out => idealLoop (w.sim S h) Z (k xw.1 out.1) n
              { w.view v with sessions := (w.view v).sessions ++ [(xw.1, out.1)] } out.2)
            = ((S.prove s (w.inst xw.1)).bind fun out => idealLoop S (w.env Z)
                (w.pull ivk (k (w.back (w.inst xw.1)) (w.proof ivk out.1))) n
                { v with sessions := v.sessions ++ [(w.inst xw.1, out.1)] } out.2).map w.view
          rw [PMF.bind_map, PMF.map_bind, hb (w.view v) xw.1 xw.2 hz]
          refine congrArg _ (funext fun out => ?_)
          have e : ({ w.view v with sessions := (w.view v).sessions ++ [(xw.1, w.proof ivk out.1)] }
              : View lam IVK' X' Pf') = w.view { v with sessions := v.sessions ++
              [(w.inst xw.1, out.1)] } := by
            rw [w.view_sessions, hb (w.view v) xw.1 xw.2 hz, hi]
          show idealLoop (w.sim S h) Z (k xw.1 (w.proof ivk out.1)) n
              { w.view v with sessions := (w.view v).sessions ++ [(xw.1, w.proof ivk out.1)] }
              (out.2, ivk) = _
          rw [e]
          exact idealLoop_eq (k xw.1 (w.proof ivk out.1)) n _ out.2 hi hv

end Ideal

theorem idealExp_eq (R : IndexedRelation I X W PP) (R' : IndexedRelation I' X' W' PP')
    (S : Simulator lam PP IVK X Pf) (h : PP' → PP) (Z : ViewEnv lam IVK' X' W' Pf')
    (hb : ∀ v x' w', Z v = some (x', w') → w.back (w.inst x') = x')
    (Vt : IVK' → AdvVerifier lam X' Pf') (i : I) (i' : I') (hpp : R.pp i = h (R'.pp i'))
    (N : ℕ) :
    idealExp R' (w.sim S h) Vt Z i' N
      = (idealExp R S (w.verifier Vt) (w.env Z) i N).map w.view := by
  show ((S.init (h (R'.pp i')) N).bind fun o =>
        match w.ask o.1 with
        | some s => (S.answer o.2 s).map fun a => (w.key o.1 (some a.1), (a.2, o.1))
        | none => PMF.pure (w.key o.1 none, (o.2, o.1))).bind
            (fun out => idealLoop (w.sim S h) Z (Vt out.1) N ⟨out.1, [], [], []⟩ out.2)
    = ((S.init (R.pp i) N).bind fun out => idealLoop S (w.env Z) (w.verifier Vt out.1) N
        ⟨out.1, [], [], []⟩ out.2).map w.view
  rw [hpp, PMF.bind_bind, PMF.map_bind]
  refine congrArg _ (funext fun o => ?_)
  unfold verifier
  cases hq : w.ask o.1 with
  | none =>
      have e : (⟨w.key o.1 none, [], [], []⟩ : View lam IVK' X' Pf') = w.view ⟨o.1, [], [], []⟩ :=
          by simp [view, hq]
      show (PMF.pure (w.key o.1 none, (o.2, o.1))).bind (fun out => idealLoop (w.sim S h) Z
          (Vt out.1) N ⟨out.1, [], [], []⟩ out.2) = _
      rw [PMF.pure_bind]
      show idealLoop (w.sim S h) Z (Vt (w.key o.1 none)) N ⟨w.key o.1 none, [], [], []⟩ (o.2, o.1)
        = _
      rw [e]
      exact w.idealLoop_eq S h Z o.1 hb _ N ⟨o.1, [], [], []⟩ o.2 rfl (fun hh => by simp [hq] at hh)
  | some s =>
      show ((S.answer o.2 s).map fun a => (w.key o.1 (some a.1), (a.2, o.1))).bind
          (fun out => idealLoop (w.sim S h) Z (Vt out.1) N ⟨out.1, [], [], []⟩ out.2)
        = ((S.answer o.2 s).bind fun out => idealLoop S (w.env Z)
            (w.pull o.1 (Vt (w.key o.1 (some out.1)))) N ⟨o.1, [], [] ++ [(s, out.1)], []⟩
            out.2).map w.view
      rw [PMF.bind_map, PMF.map_bind]
      refine congrArg _ (funext fun a => ?_)
      have e : (⟨w.key o.1 (some a.1), [], [], []⟩ : View lam IVK' X' Pf') = w.view
          ⟨o.1, [], [(s, a.1)], []⟩ := by simp [view, hq]
      show idealLoop (w.sim S h) Z (Vt (w.key o.1 (some a.1))) N ⟨w.key o.1 (some a.1), [], [], []⟩
          (a.2, o.1) = _
      rw [e]
      exact w.idealLoop_eq S h Z o.1 hb _ N ⟨o.1, [], [(s, a.1)], []⟩ a.2 rfl (fun _ => by simp)

/-- If the inner view's trace is consistent, so is the outer view's: the outer view's queries are
among the inner view's. -/
theorem consistent_view {v : View lam IVK X Pf} (hc : v.trace.Consistent) :
    (w.view v).trace.Consistent := by
  intro q r r' h1 h2
  have sub : ∀ e, e ∈ (w.view v).trace → e ∈ v.trace := by
    intro e he
    by_cases hq : (w.ask v.ivk).isSome = true
    · have he' : e ∈ v.trace.tail := by simpa [view, hq] using he
      exact List.mem_of_mem_tail he'
    · simpa [view, hq] using he
  exact hc q r r' (sub _ h1) (sub _ h2)

end Wrap

/-- Privacy survives the re-packing, at an outer index i' and an inner index i. Hypotheses: Under
each hash function f both committers are functions of one random element s with the distribution
`μ f`. The inner committer outputs `c f s`. The verifier's key of the outer committer is made from
`(c f s).1` and the further query's answer, and its prover's key is `σ f s`. The outer prover at
`σ f s` has the output distribution of the inner prover at `(c f s).2`, mapped; this is asked for
the instances that the environment can choose, and on these `back` undoes `inst`. The public
parameters (`pp`) of the inner index are h of those of the outer index. The inner scheme's privacy
is asked at the environment `w.env Z`. Then the bound is the inner one at one query more. -/
theorem PrivacyFor.wrap (w : Wrap lam IVK X W Pf IVK' X' W' Pf') {R : IndexedRelation I X W PP}
    {R' : IndexedRelation I' X' W' PP'}
    {A : Arg lam I X W IVK ISK Pf} {B : Arg lam I' X' W' IVK' ISK' Pf'}
    {S : Simulator lam PP IVK X Pf} {ζ : ℕ → ℕ → ℝ≥0∞} (h : PP' → PP) {i : I} {i' : I'}
    {Z : ViewEnv lam IVK' X' W' Pf'} (hpp : R.pp i = h (R'.pp i')) {Ω : Type}
    (μ : Oracle lam → PMF Ω) (c : Oracle lam → Ω → IVK × ISK) (σ : Oracle lam → Ω → ISK')
    (hA : ∀ f, (A.C i).run f = (μ f).map (c f))
    (hB : ∀ f, (B.C i').run f = (μ f).map fun s =>
        (w.key (c f s).1 ((w.ask (c f s).1).map f), σ f s))
    (hP : ∀ f s v x' w', Z v = some (x', w') → (B.P (σ f s) x' w').run f =
        ((A.P (c f s).2 (w.inst x') (w.wit w')).run f).map (w.proof (c f s).1))
    (hb : ∀ v x' w', Z v = some (x', w') → w.back (w.inst x') = x')
    (hp : PrivacyFor R A S ζ i (w.env Z)) :
    PrivacyFor R' B (w.sim S h) (fun t N => ζ (t + 1) N) i' Z := by
  intro tV Vt N hV
  have b := hp (tV + 1) (w.verifier Vt) N (w.queryBound_verifier hV)
  have hreal : ∀ f, (realExp B Vt Z i' N).run f = ((realExp A (w.verifier Vt) (w.env Z) i N).mapO
      w.view).run f := by
    intro f
    rw [OComp.run_mapO]
    show ((B.C i').bind fun key => realLoop B Z key.2 (Vt key.1) N ⟨key.1, [], [], []⟩).run f
      = (((A.C i).bind fun key => realLoop A (w.env Z) key.2 (w.verifier Vt key.1) N
          ⟨key.1, [], [], []⟩).run f).map w.view
    rw [run_bind, run_bind, hA f, hB f, PMF.bind_map, PMF.bind_map, PMF.map_bind]
    exact congrArg _ (funext fun s =>
      w.realStart_run Z f (c f s).1 (c f s).2 (σ f s) (hP f s) hb Vt N)
  have e1 : ∀ T : Set (View lam IVK' X' Pf'), Pr (realExp B Vt Z i' N) (fun _ => T) = Pr
      (realExp A (w.verifier Vt) (w.env Z) i N) (fun _ => w.view ⁻¹' T) := fun T => by
    rw [Pr_congr hreal, Pr_mapO]
  have e2 : ∀ T : Set (View lam IVK' X' Pf'), prob (idealExp R' (w.sim S h) Vt Z i' N) T = prob
      (idealExp R S (w.verifier Vt) (w.env Z) i N) (w.view ⁻¹' T) := fun T => by
    rw [w.idealExp_eq R R' S h Z hb Vt i i' hpp N, prob_map]
  simp only [e1, e2]
  refine ⟨le_trans (SD_preimage_le w.view _ _) b.1, le_antisymm
      (le_trans (prob_mono _ fun v hv => ?_) (le_of_eq b.2)) (zero_le _)⟩
  exact fun hc => hv (w.consistent_view hc)

end ZKCP
