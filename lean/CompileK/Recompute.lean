-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Recompute.lean: a yardstick: where a witness can be recomputed, the witness clause of index
binding is free.

One definition, two statements, their proofs.
Index binding with E at ε (`HasIndexBindingWith`, ZKCP/Gen.lean): for all cheating committers and
provers with at most tC and tP queries, Pr[ V accepts, and x is not in the language of the extracted
index or the extracted witness is not valid ] ≤ ε tC tP.

Main names:
  `Spec.binding_by_recompute`: let A be any scheme without witnesses, E an extractor (of the index
    alone) with which A has index binding for the language of a relation, with the bound ε. Let
    tr i x be a function of the index and the instance such that, whenever x has some witness in
    R_no for i, tr i x is one. Then A, read in the syntax with witnesses (`withW`,
    CompileK/GenWit.lean), has index binding with witnesses for R_no, with the same ε, and with the
    witness extractor `recompute`. This extractor reads neither the proof nor the prover's trace.
  `Spec.binding_by_choice`: see "For which relations" below.

Limits: what follows for the reading of a witness clause. In the definition (ZKCP/Gen.lean) the
witness extractor is handed the key and the committer's trace, so it can extract the index; no
running time is modelled. So for a relation in which a valid witness is a function of (index,
instance) the witness clause is no stronger a security statement than binding for the language, and
a theorem with witnesses must not be read as "more secure" than the theorem for languages on
such a relation.
A configuration of Hiop/RecConf.lean is of this kind, with tr = trace, as soon as every instance
with a witness in Rno has one in Ryes (then trace i x is a witness in Ryes by `ConfigurationWithOutOfDomainSample.Props.admits`,
hence in Rno by `ConfigurationWithOutOfDomainSample.Props.sub`). This file does not show that the relation of the integer model
with its cells, at exact match, is of this kind.
What `extractorK` of CompileK/Main.lean adds is of another kind: it does not recompute; it
reads the witness out of what the prover committed to (roots in the proof, Merkle extraction,
decoding), so a theorem on it says that a valid witness STANDS in the committed oracles (for what
that is worth without time, see Ior/KnowBlind.lean);
and it gives a protocol the structure (round-by-round knowledge soundness of each block, compiled)
that was asked for (lean/CREDITS.md).
For which relations. In Lean's terms, for every relation with a non-empty witness type
(`binding_by_choice`): tr i x := some witness of x for i, by choice, meets the hypothesis. The
difference between relations lies in what tr costs, which Lean does not see. For the integer model
tr is a forward pass, so even a reader who counts time calls the clause free.
For other relations tr is a choice or a search, and the clause is free only because no time is
modelled; a definition with efficient extractors would give it content there.
This file says nothing on running times.
-/
import CompileK.GenWit
import Rom.EagerLazy
import Rom.Bridge

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP.Gen
open Rom

variable {S : OSpec} {I X W PP IVK ISK Pf : Type}

/-- The extractor that recomputes: the index as E extracts it; the witness is tr (the extracted
index) x, and a fixed value if no index is extracted. It reads neither the proof nor the prover's
trace. -/
def recompute (E : Extractor S I X Unit IVK Pf) (tr : I → X → W) (w0 : W) :
    Extractor S I X W IVK Pf where
  Ei := E.Ei
  Ew := fun v trC x _ _ => match E.Ei v trC with
    | some i => tr i x
    | none => w0

namespace Spec

/-- States: binding for the language gives binding with witnesses, same bound, as soon as a valid
witness is a function of (index, instance). -/
def binding_by_recompute : Prop :=
  ∀ (S : OSpec) (I X W PP IVK ISK Pf : Type) (R : RelPair I X W PP) (R₀ : RelPair I X Unit PP)
      (A : Arg S I X Unit IVK ISK Pf) (E : Extractor S I X Unit IVK Pf) (tr : I → X → W)
      (w0 : W) (ε : ℕ → ℕ → ℝ≥0∞),
    (∀ i x, R₀.no i x () → ∃ w, R.no i x w) → (∀ i x w, R.no i x w → R.no i x (tr i x)) →
    HasIndexBindingWith R₀ A E ε → HasIndexBindingWith R (withW W A) (recompute E tr w0) ε

/-- `binding_by_recompute` for every relation with a non-empty witness type, without the hypothesis
on tr: the function "some witness, by choice" recomputes. -/
def binding_by_choice : Prop :=
  ∀ (S : OSpec) (I X W PP IVK ISK Pf : Type) [Nonempty W] (R : RelPair I X W PP)
      (R₀ : RelPair I X Unit PP) (A : Arg S I X Unit IVK ISK Pf) (E : Extractor S I X Unit IVK Pf)
      (w0 : W) (ε : ℕ → ℕ → ℝ≥0∞),
    (∀ i x, R₀.no i x () → ∃ w, R.no i x w) → HasIndexBindingWith R₀ A E ε →
    HasIndexBindingWith R (withW W A) (recompute E (fun i x => Classical.epsilon (R.no i x)) w0) ε

end Spec

theorem binding_by_recompute : Spec.binding_by_recompute := by
  intro S I X W PP IVK ISK Pf R R₀ A E tr w0 ε hL htr h tC tP St Ct Pt hC hP
  refine le_trans ?_ (h tC tP St Ct Pt hC hP)
  -- the experiment with witnesses is the experiment without, with the recomputed witness written
  -- into its outcome
  have e : bindingExp (withW W A) (recompute E tr w0) Ct Pt =
      (bindingExp A E Ct Pt).bind fun o => .pure (⟨o.accept, o.iStar, o.x, (match o.iStar with
        | some i => tr i o.x
        | none => w0)⟩ : BindingOutcome I X W) := by
    unfold bindingExp
    simp only [bind, OComp.bind_assoc]
    rfl
  rw [e, Pr_bind_pure]
  refine Pr_mono _ fun _ o ho => ?_
  obtain ⟨acc, is, x, u⟩ := o
  obtain ⟨h1, h2⟩ := ho
  refine ⟨h1, Or.inl ?_⟩
  cases is with
  | none => exact fun hx => hx
  | some i =>
      rintro ⟨u', hu⟩
      obtain ⟨w, hw⟩ := hL i x (by cases u'; exact hu)
      exact h2.elim (fun hn => hn ⟨w, hw⟩) (fun hn => hn (htr i x w hw))

theorem binding_by_choice :
    Spec.binding_by_choice := fun S I X W PP IVK ISK Pf _ R R₀ A E w0 ε hL h =>
  binding_by_recompute S I X W PP IVK ISK Pf R R₀ A E _ w0 ε hL
    (fun _ _ w hw => Classical.epsilon_spec ⟨w, hw⟩) h

end ZKCP.Gen
