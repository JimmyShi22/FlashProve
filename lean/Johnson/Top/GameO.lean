-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/GameO.lean: index binding with an extractor that may query the hash function, and the
steps that carry it up to a scheme on prompts and output tokens.

What this file states. Definitions and theorems with their proofs, in the terms of ZKCP/Defs.lean.
`HasIndexBinding` hands the extractor of the index the key and the committer's query
log. Here the extractor of the index is an oracle algorithm without coins: it is handed the same two
things and may also query the hash function, at most q times. Its queries enter nobody's log. All
else of the experiment and the bad event are `HasIndexBinding`'s. `ExtractorO`, `ExtractorO.Within`,
`bindingExpO`, `HasIndexBindingWithO`: the extractor, its budget of queries, the experiment, the
bound. They are placed here so that files that know nothing of a compiled verifier can name them.
The theorems: an `Extractor` is one that asks nothing, and for it the two bounds are
one statement; the bound is about the verifier alone; the step of ZKCP/BuildInstance.lean.

Under which hypotheses. Those in the statements: `of_sameV` takes two schemes with one verifier;
`HasIndexBindingWithO.buildInstance` takes the bound before the step and the premise `sound` on the
builder.

What it does not show. The bound names the number q of the extractor's queries, not the strings at
which it asks: the larger q, the less the notion says of what the committer knew. A statement that
uses the notion has to say at which strings its extractor asks. The part of an extractor that gives
a witness is handed the two logs alone, as in `Extractor`; all uses here are at relations without
witnesses.

-/
import ZKCP.Main
import ZKCP.BuildInstance

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace ZKCP

variable {lam : ℕ} {I X W IVK ISK Pf PP : Type}

/-- An extractor whose index is the output of an oracle algorithm. -/
structure ExtractorO (lam : ℕ) (I X W IVK Pf : Type) where
  Ei : IVK → Trace lam → OComp lam (Option I)
  Ew : IVK → Trace lam → X → Pf → Trace lam → W

/-- The experiment of `HasIndexBinding` with such an extractor. Its queries enter no trace. -/
def bindingExpO {St : Type} (A : Arg lam I X W IVK ISK Pf) (E : ExtractorO lam I X W IVK Pf)
    (Ct : OComp lam (IVK × St)) (Pt : St → OComp lam (X × Pf)) :
    OComp lam (BindingOutcome I X W) :=
  Ct.withTrace.bind fun o => (E.Ei o.1.1 o.2).bind fun iStar =>
    (Pt o.1.2).withTrace.bind fun o' => (A.V o.1.1 o'.1.1 o'.1.2).bind fun b =>
      .pure ⟨b, iStar, o'.1.1, E.Ew o.1.1 o.2 o'.1.1 o'.1.2 o'.2⟩

/-- The extractor of the index asks the hash function at most q queries and draws no coin, at every
key and log. -/
def ExtractorO.Within (E : ExtractorO lam I X W IVK Pf) (q : ℕ) : Prop :=
  ∀ k tr, (E.Ei k tr).QueryBound q ∧ (E.Ei k tr).DrawsNoCoin

/-- `HasIndexBindingWith`'s bound in that experiment, for an extractor with at most q queries and no
coin. -/
def HasIndexBindingWithO (R : IndexedRelation I X W PP) (A : Arg lam I X W IVK ISK Pf)
    (E : ExtractorO lam I X W IVK Pf) (q : ℕ) (ε : ℕ → ℕ → ℝ≥0∞) : Prop :=
  E.Within q ∧
    ∀ (tC tP : ℕ) (St : Type) (Ct : OComp lam (IVK × St)) (Pt : St → OComp lam (X × Pf)),
      Ct.QueryBound tC → (∀ st, (Pt st).QueryBound tP) →
        Pr (bindingExpO A E Ct Pt) (fun _ => bindingBad R) ≤ ε tC tP

/-- An `Extractor`, as one that asks nothing. -/
def Extractor.toO (E : Extractor lam I X W IVK Pf) : ExtractorO lam I X W IVK Pf :=
  ⟨fun k tr => .pure (E.Ei k tr), E.Ew⟩

/-- For an extractor that asks nothing the bound is `HasIndexBindingWith`'s. -/
theorem hasIndexBindingWithO_toO_iff (R : IndexedRelation I X W PP)
    (A : Arg lam I X W IVK ISK Pf) (E : Extractor lam I X W IVK Pf) (ε : ℕ → ℕ → ℝ≥0∞) :
    HasIndexBindingWithO R A E.toO 0 ε ↔ HasIndexBindingWith R A E ε :=
  ⟨fun h => h.2, fun h => ⟨fun _ _ => ⟨trivial, trivial⟩, h⟩⟩

/-- The bound is about the verifier alone. -/
theorem HasIndexBindingWithO.of_sameV {ISK' : Type} {R : IndexedRelation I X W PP}
    {A : Arg lam I X W IVK ISK Pf} {A' : Arg lam I X W IVK ISK' Pf}
    {E : ExtractorO lam I X W IVK Pf} {q : ℕ} {ε : ℕ → ℕ → ℝ≥0∞} (hV : A'.V = A.V)
    (h : HasIndexBindingWithO R A E q ε) : HasIndexBindingWithO R A' E q ε := by
  refine ⟨h.1, ?_⟩
  intro tC tP St Ct Pt hC hP
  have e : bindingExpO A' E Ct Pt = bindingExpO A E Ct Pt := by
    unfold bindingExpO
    rw [hV]
  rw [e]
  exact h.2 tC tP St Ct Pt hC hP

variable {X' Aux : Type}

/-- The extractor on the new types, for relations without witnesses: the index part of E. -/
def ExtractorO.buildInstance (E : ExtractorO lam I X Unit IVK Pf) :
    ExtractorO lam I X' Unit IVK (Aux × Pf) :=
  ⟨E.Ei, fun _ _ _ _ _ => ()⟩

/-- `HasIndexBindingWith.buildInstance` (ZKCP/BuildInstance.lean) for an extractor that may query
the hash function: that theorem's proof with one step more. -/
theorem HasIndexBindingWithO.buildInstance {build : X' → Aux → Option X} {aux : X' → Aux}
    {π₀ : Pf} {IsTrue : I → X → Prop} {IsTrue' : I → X' → Prop} {A : Arg lam I X Unit IVK ISK Pf}
    {E : ExtractorO lam I X Unit IVK Pf} {q : ℕ} {ε : ℕ → ℕ → ℝ≥0∞} (x₀ : X)
    (sound : ∀ i x' a x, build x' a = some x → IsTrue i x → IsTrue' i x')
    (h : HasIndexBindingWithO (languageRelation IsTrue) A E q ε) :
    HasIndexBindingWithO (languageRelation IsTrue') (A.buildInstance build aux π₀)
      E.buildInstance q ε := by
  refine ⟨h.1, ?_⟩
  intro tC tP St Ct Pt hC hP
  refine le_trans ?_ (h.2 tC tP St Ct (fun st => (Pt st).mapO (builtOutput build x₀)) hC
    fun st => OComp.QueryBound.mapO _ _ tP (hP st))
  refine MeasureTheory.lintegral_mono fun f => ?_
  show prob ((Ct.withTrace.bind fun o => (E.Ei o.1.1 o.2).bind fun s =>
      (Pt o.1.2).withTrace.bind fun o' =>
        ((A.buildInstance build aux π₀).V o.1.1 o'.1.1 o'.1.2).bind fun b =>
          .pure (⟨b, s, o'.1.1, ()⟩ : BindingOutcome I X' Unit)).run f)
      (bindingBad (languageRelation IsTrue'))
    ≤ prob ((Ct.withTrace.bind fun o => (E.Ei o.1.1 o.2).bind fun s =>
      ((Pt o.1.2).mapO (builtOutput build x₀)).withTrace.bind fun o' =>
        (A.V o.1.1 o'.1.1 o'.1.2).bind fun b =>
          .pure (⟨b, s, o'.1.1, ()⟩ : BindingOutcome I X Unit)).run f)
      (bindingBad (languageRelation IsTrue))
  rw [run_bind, run_bind, prob_bind, prob_bind]
  refine expect_mono _ fun o => ?_
  rw [run_bind, run_bind, prob_bind, prob_bind]
  refine expect_mono _ fun s => ?_
  rw [OComp.withTrace_mapO, OComp.mapO_bind, run_bind, run_bind, prob_bind, prob_bind]
  refine expect_mono _ fun o' => ?_
  exact prob_V_buildInstance_le A build aux π₀ f o.1.1 o'.1.1 o'.1.2 x₀
    (fun b => (⟨b, s, o'.1.1, ()⟩ : BindingOutcome I X' Unit))
    (fun x b => (⟨b, s, x, ()⟩ : BindingOutcome I X Unit))
    (bindingBad (languageRelation IsTrue')) (bindingBad (languageRelation IsTrue))
    (fun hb => Bool.false_ne_true hb.1) fun x hx b hb => bindingBad_buildInstance sound hx b _ hb

end ZKCP

#print axioms ZKCP.hasIndexBindingWithO_toO_iff
#print axioms ZKCP.HasIndexBindingWithO.of_sameV
#print axioms ZKCP.HasIndexBindingWithO.buildInstance
