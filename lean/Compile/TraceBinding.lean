-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Compile/TraceBinding.lean: index binding by an event that happens at a query. Generic in the
  family of oracles and in the scheme.
  Why. Index binding (ZKCP/Gen.lean) is a bound for every pair of algorithms with given numbers of
  queries. That form cannot be added up over many schemes that an adversary attacks at once,
  choosing late. The proofs of layer 1 have more: an event on traces that is caused by the answer to
  one new query with small chance, and outside which an accepted proof is right for the extracted
  index, with certainty. This file gives that form a name.
    TraceBinding R A E an tV step ε      V draws no coin and asks at most tV queries; step is an
                           event at a query (Rom/OneCount.lean) that an old entry never causes and a
                           new query causes with chance at most ε (number of entries before it); and
                           the core: if V runs to "accept" within a trace trV, and the event has not
                           happened in (the committer's trace, the entry of the query an v, the
                           prover's trace, trV), then the instance is in the language of the
                           extracted index, with the extracted witness. an v: one query that is put
                           behind the committer's (layer 1: the announcement of the root in the key)
    TraceBinding.binding         index binding with ε' tC tP = ε 0 + .. + ε (tC + tP + tV)
    TraceBinding.mono      larger tV, larger ε
    TraceBinding.map       it passes along maps back on keys and proofs, if the old verifier accepts
                           whenever the new one does (Compile/GenLe.lean: AccLe, pullEK) and the new
                           one draws no coin and asks at most tV' queries. (Used nowhere. It does
                           not cover a map on proofs that reads the key.)
  What it does not say.  No scheme is shown to have it here.
  Terms: lean/GLOSSARY.md.
-/
import Compile.GlueBinding
import Compile.GenLe
import Rom.OneCount

noncomputable section

namespace Compile
open Rom Prob ZKCP.Gen
open scoped ENNReal

variable {S : OSpec} {I X W PP IVK ISK Pf : Type}

/-- Index binding by an event that happens at a query. -/
structure TraceBinding (R : RelPair I X W PP) (A : Arg S I X W IVK ISK Pf)
    (E : Extractor S I X W IVK Pf) (an : IVK → Σ o : S.ι, S.Dom o) (tV : ℕ)
    (step : Trace S → QA S → Prop) (ε : ℕ → ℝ≥0∞) : Prop where
  det : ∀ v x π, DetBound (A.V v x π) tV
  hold : ∀ (pre : Trace S) (e : QA S), e ∈ pre → ¬ step pre e
  hnew : ∀ (pre : Trace S) (o : S.ι) (q : S.Dom o),
    (∀ r, (⟨o, q, r⟩ : QA S) ∉ pre) → pr (unif (S.Rng o)) {r | step pre ⟨o, q, r⟩} ≤ ε pre.length
  core : ∀ v x π (trC : Trace S) (r : S.Rng (an v).1) (trP trV : Trace S),
    RunsIn trV (A.V v x π) true →
    ¬ StepEvent step (trC ++ ⟨(an v).1, (an v).2, r⟩ :: (trP ++ trV)) →
    x ∈ R.L (E.Ei v trC) ∧ R.no' (E.Ei v trC) x (E.Ew v trC x π trP)

namespace TraceBinding
variable {R : RelPair I X W PP} {A : Arg S I X W IVK ISK Pf} {E : Extractor S I X W IVK Pf}
  {an : IVK → Σ o : S.ι, S.Dom o} {tV : ℕ} {step : Trace S → QA S → Prop} {ε : ℕ → ℝ≥0∞}

/-- the cheating committer, the query an v, the cheating prover and V, as one algorithm -/
def committerProverAndVerifierRun (A : Arg S I X W IVK ISK Pf) (an : IVK → Σ o : S.ι, S.Dom o) {St : Type}
    (Ct : OComp S (IVK × St)) (Pt : St → OComp S (X × Pf)) : OComp S Unit :=
  Ct.bind fun a =>
    (OComp.ask (an a.1).1 (an a.1).2).bind fun _ =>
      (Pt a.2).bind fun xp => (A.V a.1 xp.1 xp.2).bind fun _ => OComp.pure ()

theorem committerProverAndVerifierRun_queryBound (h : TraceBinding R A E an tV step ε) {St : Type}
    {Ct : OComp S (IVK × St)} {Pt : St → OComp S (X × Pf)} {tC tP : ℕ}
    (hC : Ct.QueryBound tC) (hP : ∀ st, (Pt st).QueryBound tP) :
    (committerProverAndVerifierRun A an Ct Pt).QueryBound (tC + tP + tV + 1) := by
  have h' : (committerProverAndVerifierRun A an Ct Pt).QueryBound (tC + (1 + (tP + (tV + 0)))) := by
    unfold committerProverAndVerifierRun
    exact hC.bind fun a =>
      (detBound_ask (S := S) (an a.1).1 (an a.1).2).queryBound.bind fun _ =>
        (hP a.2).bind fun xp => (h.det a.1 xp.1 xp.2).queryBound.bind fun _ => trivial
  exact h'.mono (by omega)

/-- Index binding. -/
theorem binding (h : TraceBinding R A E an tV step ε) :
    HasIndexBindingWith R A E fun tC tP => ∑ v ∈ Finset.range (tC + tP + tV + 1), ε v := by
  intro tC tP St Ct Pt hC hP
  have hpt : ∀ f : Fam S, Rom.PrCoins f (bindingExp A E Ct Pt) (bindingBad R) ≤
      Rom.PrCoins f (committerProverAndVerifierRun A an Ct Pt).withTrace {o | StepEvent step o.2} := by
    intro f
    unfold Rom.PrCoins
    simp only [bindingExp, bind_eq, pure_eq, committerProverAndVerifierRun, withTrace_bind, OComp.bind_assoc, OComp.ask,
      OComp.withTrace, OComp.bind, OComp.runEager_bind, OComp.runEager]
    refine pr_bind_le_bind _ _ _ _ _ fun a _ => pr_bind_le_bind _ _ _ _ _ fun b _ => ?_
    have e1 : (A.V a.1.1 b.1.1 b.1.2).runEager f =
        ((A.V a.1.1 b.1.1 b.1.2).withTrace.runEager f).map Prod.fst :=
      (runEager_withTrace_fst f _).symm
    rw [e1, PMF.bind_map]
    refine pr_bind_le_bind _ _ _ _ _ fun c hc => pr_pure_le_pure ?_
    rintro ⟨hacc, hbad⟩
    by_contra hnb
    have hrun : RunsIn c.2 (A.V a.1.1 b.1.1 b.1.2) true := by
      have := runsIn_of_mem_support (h.det a.1.1 b.1.1 b.1.2) f c hc
      have hc1 : c.1 = true := hacc
      rwa [hc1] at this
    have hnb' : ¬ StepEvent step
        (a.2 ++ ⟨(an a.1.1).1, (an a.1.1).2, f (an a.1.1).1 (an a.1.1).2⟩ :: (b.2 ++ c.2)) := by
      simpa using hnb
    obtain ⟨h1, h2⟩ := h.core a.1.1 b.1.1 b.1.2 a.2 _ b.2 c.2 hrun hnb'
    rcases hbad with hb | hb
    · exact hb h1
    · exact hb h2
  calc
    Rom.Pr (bindingExp A E Ct Pt) (fun _ => bindingBad R) ≤
        Rom.Pr (committerProverAndVerifierRun A an Ct Pt).withTrace (fun _ => {o | StepEvent step o.2}) :=
      MeasureTheory.lintegral_mono hpt
    _ = pr (committerProverAndVerifierRun A an Ct Pt).withTrace.law {o | StepEvent step o.2} := Pr_eq_law _ _
    _ ≤ ∑ v ∈ Finset.range (tC + tP + tV + 1), ε v :=
      pr_stepEvent_le step ε h.hold h.hnew _ _ (h.committerProverAndVerifierRun_queryBound hC hP)

/-- larger numbers -/
theorem mono (h : TraceBinding R A E an tV step ε) {tV' : ℕ} {ε' : ℕ → ℝ≥0∞}
    (ht : tV ≤ tV') (he : ∀ n, ε n ≤ ε' n) :
    TraceBinding R A E an tV' step ε' where
  det v x π := (h.det v x π).mono ht
  hold := h.hold
  hnew pre o q hq := le_trans (h.hnew pre o q hq) (he _)
  core := h.core

/-- Under the hypotheses below, it passes along maps back on keys and proofs. -/
theorem map {IVK' Pf' : Type} (h : TraceBinding R A E an tV step ε) {κ : IVK → IVK'} {τ : Pf → Pf'}
    {V' : IVK' → X → Pf' → OComp S Bool} {κ' : IVK' → IVK} {σ : Pf' → Pf} {tV' : ℕ}
    (hdown : ∀ v x π, GenLe.AccLe (V' v x π) (A.V (κ' v) x (σ π)))
    (hdet : ∀ v x π, DetBound (V' v x π) tV') :
    TraceBinding R (GenLe.mapArg A κ τ V') (GenLe.pullEK κ' σ E)
      (fun v => an (κ' v)) tV' step ε where
  det := hdet
  hold := h.hold
  hnew := h.hnew
  core v x π trC r trP trV hrun hnb :=
    h.core (κ' v) x (σ π) trC r trP trV ((hdown v x π).2 trV hrun) hnb

end TraceBinding
end Compile
