-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/TotalExt.lean: from an extractor that may say "none" to a total one.

Definitions, a statement and its proof. Generic: any family of oracles, any scheme whose prover
ignores its witness (`withW`, CompileK/GenWit.lean). Terms (lean/GLOSSARY.md): chain query.
CompileK/KnowExtT.lean and CompileK/KnowExtTo.lean define witness extractors with answers in
`Option Wn`, and state index binding for the relation `optR Rno` (some w: Rno i x w; none: a witness
exists). The definition of a commit-and-prove argument needs a total extractor (`Extractor`,
ZKCP/Gen.lean, after ZKCP/Defs.lean) and the relation Rno itself.

Main names:
  `MissLe A₀ E κ`: the hypothesis, named. In the experiment of index binding (`bindingExp`,
    ZKCP/Gen.lean), for all cheating committers and provers with at most tC and tP queries,
    Pr[ the verifier accepts and E says none ] ≤ κ tC tP.
  `Spec.binding_total`: for Ry ⊆ Rno, index binding for `optR Rno` with E at ε, and `MissLe` at κ,
    give index binding for Rno with `totalE w0 E` (E with the fixed value w0 in the place of none)
    at ε + κ.

Limits: this file says nothing on whether `MissLe` holds for any κ below 1. `MissLe` is a hypothesis
on the compiled scheme, not a property of the interface; for the extractors that follow a chain it
says that an accepted proof's chain queries, as far as they are followed, stand in the two traces
but for κ.
Status beside the compilation of this protocol's technical report (lean/CREDITS.md; a comparison by
reading, of one of its prints, not held against the report's latest edition; that report is
unrefereed): its witness extractor recomputes the witness from the extracted
index and the instance, so this file renders no step of it. Here a
witness is read out of what the prover sent (exactly: `E : Extractor S I X (Option Wn) IVK Pf`;
CompileK/KnowExtT.lean, CompileK/KnowExtTo.lean).
-/
import CompileK.KnowExtT

set_option autoImplicit false

noncomputable section

namespace ZKCP.Gen
open Rom Prob Compile.Batch
open scoped ENNReal

variable {S : OSpec} {I X Wn IVK ISK Pf : Type}

/-- The total extractor. -/
def totalE (w0 : Wn) (E : Extractor S I X (Option Wn) IVK Pf) : Extractor S I X Wn IVK Pf where
  Ei := E.Ei
  Ew := fun v trC x π trP => (E.Ew v trC x π trP).getD w0

/-- The verifier accepts and the extractor says none: at most κ. -/
def MissLe (A₀ : Arg S I X Unit IVK ISK Pf)
    (E : Extractor S I X (Option Wn) IVK Pf) (κ : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (tC tP : ℕ) (St : Type) (Ct : Rom.OComp S (IVK × St)) (Pt : St → Rom.OComp S (X × Pf)),
    Ct.QueryBound tC → (∀ st, (Pt st).QueryBound tP) →
    Rom.Pr (bindingExp (withW (Option Wn) A₀) E Ct Pt)
        (fun _ => {o | o.accept = true ∧ o.w = none}) ≤ κ tC tP

namespace Spec

def binding_total : Prop :=
  ∀ (S : OSpec) (I X Wn IVK ISK Pf : Type) (A₀ : Arg S I X Unit IVK ISK Pf)
      (Ry Rno : I → X → Wn → Prop) (sub : ∀ i x w, Ry i x w → Rno i x w)
      (E : Extractor S I X (Option Wn) IVK Pf) (w0 : Wn) (ε κ : ℕ → ℕ → ℝ≥0∞),
    HasIndexBindingWith (relPairW (optR Ry) (optR Rno) (optR_sub sub)) (withW (Option Wn) A₀) E ε →
    MissLe A₀ E κ →
    HasIndexBindingWith (relPairW Ry Rno sub) (withW Wn A₀) (totalE w0 E) fun tC tP =>
      ε tC tP + κ tC tP

end Spec

/-- The outcome with the fixed value in the place of none. -/
def fillW (w0 : Wn) (o : BindingOutcome I X (Option Wn)) : BindingOutcome I X Wn :=
  ⟨o.accept, o.iStar, o.x, o.w.getD w0⟩

theorem bindingExp_total (A₀ : Arg S I X Unit IVK ISK Pf) (E : Extractor S I X (Option Wn) IVK Pf)
    (w0 : Wn) {St : Type} (Ct : Rom.OComp S (IVK × St)) (Pt : St → Rom.OComp S (X × Pf)) :
    bindingExp (withW Wn A₀) (totalE w0 E) Ct Pt =
      (bindingExp (withW (Option Wn) A₀) E Ct Pt).bind fun o => .pure (fillW w0 o) := by
  simp only [bindingExp, Compile.bind_eq, Compile.pure_eq, OComp.bind_assoc]
  rfl

theorem binding_total : Spec.binding_total := by
  intro S I X Wn IVK ISK Pf A₀ Ry Rno sub E w0 ε κ hb hm tC tP St Ct Pt hC hP
  rw [bindingExp_total, Pr_bind_pure]
  have hsub : fillW w0 ⁻¹' bindingBad (relPairW Ry Rno sub) ⊆
      bindingBad (relPairW (optR Ry) (optR Rno) (optR_sub sub)) ∪
        {o : BindingOutcome I X (Option Wn) | o.accept = true ∧ o.w = none} := by
    rintro ⟨acc, is, x, w⟩ ⟨hacc, hbad⟩
    cases w with
    | none => exact Or.inr ⟨hacc, rfl⟩
    | some w =>
      refine Or.inl ⟨hacc, Or.inr ?_⟩
      cases is with
      | none => exact fun h => h
      | some i =>
        intro hw
        rcases hbad with h | h
        · exact h ⟨w, hw⟩
        · exact h hw
  calc
    Rom.Pr (bindingExp (withW (Option Wn) A₀) E Ct Pt)
          (fun _ => fillW w0 ⁻¹' bindingBad (relPairW Ry Rno sub)) ≤
        Rom.Pr (bindingExp (withW (Option Wn) A₀) E Ct Pt) (fun _ =>
          bindingBad (relPairW (optR Ry) (optR Rno) (optR_sub sub)) ∪
              {o | o.accept = true ∧ o.w = none}) := by
        rw [Pr_eq_law, Pr_eq_law]
        exact pr_mono _ hsub
    _ ≤ Rom.Pr (bindingExp (withW (Option Wn) A₀) E Ct Pt)
            (fun _ => bindingBad (relPairW (optR Ry) (optR Rno) (optR_sub sub))) +
          Rom.Pr (bindingExp (withW (Option Wn) A₀) E Ct Pt)
            (fun _ => {o | o.accept = true ∧ o.w = none}) := by
        rw [Pr_eq_law, Pr_eq_law, Pr_eq_law]
        exact pr_union_le _ _ _
    _ ≤ ε tC tP + κ tC tP := add_le_add (hb tC tP St Ct Pt hC hP) (hm tC tP St Ct Pt hC hP)

end ZKCP.Gen
