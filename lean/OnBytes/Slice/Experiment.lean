-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/Experiment.lean: the compiler's conclusion on Link as an experiment in one world.

OnBytes/Slice/LinkClause.lean speaks of an event on traces. This file turns it into a bound on a
probability. One algorithm A, which may ask the random oracles t times, puts out two roots and a
Link string. Then the compiled Link verifier, with the strict format, is run under the same oracles.
A wins if the verifier accepts and the two strings that are read off the joint trace (A's queries,
then the verifier's) under the two roots are outside the language.

Main definitions: `linkExp`, `linkWin`, `trail`.
Main theorems.
 `vL_of_vLS`        what the Link verifier with the strict format accepts, the plain Link verifier
                    accepts on a string with other paths, within the same trace.
 `link_experiment`  from `LinkAt W Lg e`: A wins with probability at most
                    (t + tV) * e + 2 (t + tV + 1)^2 / 2^lam, where tV bounds the verifier's queries.
 `runsIn_trail`     an algorithm without coins runs, within the list of its own queries and answers
                    under fixed oracle functions, to its result under these functions.
 `linkBad_run`      for a run of the verifier under any fixed oracle functions: if a trace holds the
                    run's queries and shows none of the three events of the named set `linkBad`,
                    the language holds of what is read off it. No probability is in it.

Not claimed. The oracles are the typed random oracles of the library's compiler, not one oracle on
strings and not a hash function. The bound says nothing once it reaches 1.
-/
import OnBytes.Slice.LinkClause
import Compile.Batch.ForestSound
import Compile.Batch.GlueBinding
import Rom.Cache

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob Compile Compile.Batch
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- What the Link verifier with the strict format accepts, the plain Link verifier accepts on a
string with other paths, within the same trace. -/
theorem vL_of_vLS (W : QueryLayout lam L) (hW : W.OKG) {sMT sFS : ℕ} {cm cm' : Dig lam}
    {π : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)} {tr : Tc W}
    (h : RunsIn tr (vLS W sMT sFS cm cm' π) true) : ∃ π', RunsIn tr (vL W cm cm' π') true :=
  let ⟨P1, P2, h'⟩ := runsIn_verifyB_of_strict hW.Lk h
  ⟨π.withPaths P1 P2, h'⟩

/-- What a cheating maker of a Link string puts out: two roots and the string. -/
abbrev LinkOut (lam : ℕ) (L : BatchProtocol I X) : Type :=
  Dig lam × Dig lam × OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)

/-- **The experiment**: the maker, then the compiled Link verifier, under the same oracles. -/
def linkExp (W : QueryLayout lam L) (sMT sFS : ℕ) (A : TypedOracleComputation lam W.K L (LinkOut lam L)) :
    TypedOracleComputation lam W.K L (LinkOut lam L × Bool) :=
  A.bind fun o => (vLS W sMT sFS o.1 o.2.1 o.2.2).bind fun b => OComp.pure (o, b)

/-- **The maker wins**: the verifier has accepted, and the two strings that are read off the joint
trace under the two roots are outside the language. -/
def linkWin (W : QueryLayout lam L) (Lg : Unit → (twoExternalStrings L.wordLength L.Symbol).Str → Prop) :
    Set ((LinkOut lam L × Bool) × Tc W) :=
  {x | x.1.2 = true ∧ ¬ Lg () (extEnc W x.2 x.1.1.1, extEnc W x.2 x.1.1.2.1)}

theorem linkExp_queryBound (W : QueryLayout lam L) (sMT sFS : ℕ) {A : TypedOracleComputation lam W.K L (LinkOut lam L)}
    {t : ℕ} (hA : A.QueryBound t) :
    (linkExp W sMT sFS A).QueryBound (t + tVQB W.Lk W.depthReq) := by
  have h : (linkExp W sMT sFS A).QueryBound (t + (tVQB W.Lk W.depthReq + 0)) :=
    hA.bind fun o => (detBound_vLS W sMT sFS o.1 o.2.1 o.2.2).queryBound.bind fun _ => trivial
  exact h.mono (by omega)

/-- **The bound on the experiment.** -/
theorem link_experiment (W : QueryLayout lam L) (hW : W.OKG)
    (Lg : Unit → (twoExternalStrings L.wordLength L.Symbol).Str → Prop) (εs : ℝ≥0∞) (h : LinkAt W Lg εs) (sMT sFS : ℕ)
    (A : TypedOracleComputation lam W.K L (LinkOut lam L)) (t : ℕ) (hA : A.QueryBound t) :
    pr (linkExp W sMT sFS A).withTrace.law (linkWin W Lg) ≤
      ((t + tVQB W.Lk W.depthReq : ℕ) : ℝ≥0∞) * εs +
        2 * ((t + tVQB W.Lk W.depthReq + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  obtain ⟨Bad, hrare, -, hL, -⟩ := h
  refine le_trans ?_ (hrare _ (linkExp W sMT sFS A) _ (linkExp_queryBound W sMT sFS hA))
  rw [← Pr_eq_law, ← Pr_eq_law]
  refine MeasureTheory.lintegral_mono fun f => ?_
  unfold PrCoins
  simp only [linkExp, Compile.withTrace_bind, OComp.bind_assoc, OComp.withTrace, OComp.bind,
    OComp.runEager_bind, OComp.runEager]
  refine pr_bind_le_bind _ _ _ _ _ fun a _ => pr_bind_le_bind _ _ _ _ _ fun c hc =>
    pr_pure_le_pure ?_
  rintro ⟨hacc, hbad⟩
  by_contra hnb
  have hrun : RunsIn c.2 (vLS W sMT sFS a.1.1 a.1.2.1 a.1.2.2) true := by
    have := runsIn_of_mem_support (detBound_vLS W sMT sFS a.1.1 a.1.2.1 a.1.2.2) f c hc
    have hc1 : c.1 = true := hacc
    rwa [hc1] at this
  obtain ⟨π', hπ'⟩ := vL_of_vLS W hW
    (hrun.mono (fun e he => List.mem_append_right a.2 (List.mem_append_left [] he)))
  exact hbad (hL _ _ _ π' hnb hπ')

/-! ## A run under fixed oracle functions -/

section
variable {S : OSpec} {α : Type}

/-- The queries and answers of the run under the oracle functions g, in their order. A coin is read
as 0. -/
def trail (g : Fam S) : OComp S α → Trace S
  | .pure _ => []
  | .query o q k => ⟨o, q, g o q⟩ :: trail g (k (g o q))
  | .sample _ k => trail g (k 0)

/-- An algorithm without coins runs to its result within its own trail. -/
theorem runsIn_trail (g : Fam S) (c : OComp S α) (t : ℕ) (h : DetBound c t) :
    RunsIn (trail g c) c (c.det g) := by
  induction c generalizing t with
  | pure a => exact RunsIn.pure a
  | query o q k ih =>
    cases t with
    | zero => exact h.elim
    | succ t =>
      exact RunsIn.query o q k (g o q) _ List.mem_cons_self
        ((ih (g o q) t (h (g o q))).mono (List.subset_cons_self _ _))
  | sample n k _ => exact h.elim

end

/-- **A run under any fixed oracle functions, and the named set.** If the verifier with the strict
format says yes under the oracle functions g, then for every trace that holds the verifier's queries
with g's answers and shows none of the three events of `linkBad`, the two strings that are read off
the trace under the two roots are in the language. Asked: Link is round-by-round sound for the
language with the error counts εL that the set is made from. It says something only together with
`linkBad_rare` at the same counts and a small e (see `linkBad_lang`). -/
theorem linkBad_run (W : QueryLayout lam L) (hW : W.OKG) (Lg : Unit → (twoExternalStrings L.wordLength L.Symbol).Str → Prop)
    (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape)
    (State : (Fin L.wordLength → L.Symbol) → X → PTr L.onlineBatch.loc.shape → Bool)
    (hsL : L.link.Sound Lg εL) (hlL : L.link.IsLocal)
    (g : Fam (spec lam W.K L)) (sMT sFS : ℕ) (cm cm' : Dig lam)
    (π : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)) (hv : (vLS W sMT sFS cm cm' π).det g = true)
    (tr : Tc W) (hsub : trail g (vLS W sMT sFS cm cm' π) ⊆ tr)
    (hB : ¬ linkBad W εT εL εB State tr) : Lg () (extEnc W tr cm, extEnc W tr cm') := by
  have hrun := runsIn_trail g (vLS W sMT sFS cm cm' π) _ (detBound_vLS W sMT sFS cm cm' π)
  rw [hv] at hrun
  obtain ⟨π', hπ'⟩ := vL_of_vLS W hW (hrun.mono hsub)
  exact linkBad_lang W εT εL εB State Lg hsL hlL hW tr _ _ π' hB hπ'

end OnBytes.Slice

#print axioms OnBytes.Slice.link_experiment
#print axioms OnBytes.Slice.runsIn_trail
#print axioms OnBytes.Slice.linkBad_run
