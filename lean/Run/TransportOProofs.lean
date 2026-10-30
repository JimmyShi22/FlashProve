-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/TransportOProofs.lean: the proofs of the statements of Run/TransportO.lean (a scheme whose
proofs are written as strings that are parsed with the oracle's help). Many statements of this
library are written twice: a definition in the namespace `Spec` states a proposition, and a theorem
of the same name outside that namespace proves it (lean/GLOSSARY.md).

What the statements say and do not say: Run/TransportO.lean, the head. One tool:
`prob_withTrace_bind`. Nothing else is defined here.
-/
import Run.TransportO
import Run.TransportPrintProofs
import ZKCP.ManyOfOne
import ZKCP.HonestKey

set_option autoImplicit false

open scoped ENNReal

namespace Run
open ZKCP

/-- What follows does not read the trace: an experiment that runs a program with its trace and then
does not read the trace gives every event, at every oracle, the same probability as the experiment
that runs the program. -/
theorem prob_withTrace_bind {lam : ℕ} {α β : Type} (f : Oracle lam) (c : OComp lam α)
    (g : α → OComp lam β) (E : Set β) :
    prob ((c.withTrace.bind fun o => g o.1).run f) E = prob ((c.bind g).run f) E := by
  rw [run_bind, run_bind, prob_bind, prob_bind]
  exact expect_withTrace f c fun a => prob ((g a).run f) E

theorem wrO_V : Spec.wrO_V := by
  intro lam I X W IVK ISK Pf B c A N h ivk x b
  refine OComp.QueryBound.bind _ N (fun o => ?_) _ c.t (c.bound ivk x b)
  cases o with
  | none => exact trivial
  | some π => exact h ivk x π

theorem wrO_fair : Spec.wrO_fair := by
  intro lam I X W IVK ISK Pf B c A hB f ivk x π
  by_cases h : true ∈ ((A.V ivk x π).run f).support
  · refine le_of_eq ?_
    show prob (((c.parse ivk x (c.print π)).bind (WrO.after A ivk x)).run f) _ = _
    rw [run_bind, hB f ivk x π h, PMF.pure_bind]
    rfl
  · have h1 : prob ((A.V ivk x π).run f) {b | b = false} = 1 := by
      refine (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 fun b hb => ?_
      cases b with
      | false => rfl
      | true => exact absurd hb h
    rw [h1]
    exact prob_le_one _ _

theorem wrO_complete : Spec.wrO_complete := by
  intro lam I X W PP IVK ISK Pf B c R A α hF h i x w hr
  refine le_trans ?_ (h i x w hr)
  refine MeasureTheory.lintegral_mono fun f => ?_
  show prob
      (((A.C i).bind fun k => ((A.P k.2 x w).mapO c.print).bind fun b => (c.arg A).V k.1 x b).run f)
      {b | b = false} ≤
    prob (((A.C i).bind fun k => (A.P k.2 x w).bind fun π => A.V k.1 x π).run f) {b | b = false}
  refine prob_run_bind_le f _ _ fun k => ?_
  rw [OComp.mapO_bind]
  exact prob_run_bind_le f _ _ fun π => hF f k.1 x π

theorem wrO_binding : Spec.wrO_binding := by
  intro lam I X W PP IVK ISK Pf B c d R A E ε hB h tC tP St Ct Pt hC hP
  refine le_trans ?_
    (h tC (tP + c.t) (IVK × St) (Ct.mapO fun o => (o.1, (o.1, o.2)))
      (fun s => (Pt s.2).bind fun xb => (c.parse s.1 xb.1 xb.2).mapO fun o => (xb.1, o.getD d))
      (OComp.QueryBound.mapO _ Ct tC hC) fun s =>
        OComp.QueryBound.bind _ c.t
          (fun xb => OComp.QueryBound.mapO _ _ _ (c.bound s.1 xb.1 xb.2)) (Pt s.2) tP (hP s.2))
  refine MeasureTheory.lintegral_mono fun f => ?_
  show prob ((Ct.withTrace.bind fun o =>
        (Pt o.1.2).withTrace.bind fun o' =>
          ((c.parse o.1.1 o'.1.1 o'.1.2).bind (WrO.after A o.1.1 o'.1.1)).bind fun b =>
            .pure (⟨b, E.Ei o.1.1 o.2, o'.1.1,
                E.Ew o.1.1 o.2 o'.1.1 d []⟩ : BindingOutcome I X W)).run f) (bindingBad R) ≤
    prob (((Ct.mapO fun o => (o.1, (o.1, o.2))).withTrace.bind fun o =>
        ((Pt o.1.2.2).bind fun xb =>
          (c.parse o.1.2.1 xb.1 xb.2).mapO fun p => (xb.1, p.getD d)).withTrace.bind fun o' =>
            (A.V o.1.1 o'.1.1 o'.1.2).bind fun b =>
              .pure (⟨b, E.Ei o.1.1 o.2, o'.1.1,
                  E.Ew o.1.1 o.2 o'.1.1 o'.1.2 o'.2⟩ : BindingOutcome I X W)).run f) (bindingBad R)
  rw [OComp.withTrace_mapO, OComp.mapO_bind]
  refine prob_run_bind_le f _ _ fun o => ?_
  rw [OComp.withTrace_bind, OComp.bind_bind]
  refine prob_run_bind_le f _ _ fun o' => ?_
  rw [OComp.bind_bind, OComp.bind_bind, OComp.withTrace_mapO, OComp.mapO_bind]
  have e : (fun p : Option Pf × Trace lam =>
        (OComp.pure
          ((o'.1.1, p.1.getD d), o'.2 ++ p.2) : OComp lam ((X × Pf) × Trace lam)).bind fun o'' =>
            (A.V o.1.1 o''.1.1 o''.1.2).bind fun b =>
              .pure (⟨b, E.Ei o.1.1 o.2, o''.1.1,
                  E.Ew o.1.1 o.2 o''.1.1 o''.1.2 o''.2⟩ : BindingOutcome I X W)) =
      fun p =>
        (fun q : Option Pf =>
            (A.V o.1.1 o'.1.1 (q.getD d)).bind fun b =>
                .pure (⟨b, E.Ei o.1.1 o.2, o'.1.1,
                      E.Ew o.1.1 o.2 o'.1.1 d []⟩ : BindingOutcome I X W)) p.1 := by
    funext p
    show ((A.V o.1.1 o'.1.1 (p.1.getD d)).bind fun b =>
        .pure (⟨b, E.Ei o.1.1 o.2, o'.1.1,
            E.Ew o.1.1 o.2 o'.1.1 (p.1.getD d) (o'.2 ++ p.2)⟩ : BindingOutcome I X W)) = _
    rw [hB o.1.1 o.2 o'.1.1 (p.1.getD d) d (o'.2 ++ p.2) []]
  rw [e]
  refine le_trans ?_
    (le_of_eq (prob_withTrace_bind f (c.parse o.1.1 o'.1.1 o'.1.2)
        (fun q : Option Pf =>
          (A.V o.1.1 o'.1.1 (q.getD d)).bind fun b =>
            .pure (⟨b, E.Ei o.1.1 o.2, o'.1.1, E.Ew o.1.1 o.2 o'.1.1 d []⟩ : BindingOutcome I X W))
        (bindingBad R)).symm)
  refine prob_run_bind_le f _ _ fun q => ?_
  cases q with
  | some π => exact le_refl _
  | none =>
    refine le_trans (le_of_eq ?_) (zero_le _)
    show prob (PMF.pure _) (bindingBad R) = 0
    rw [prob_pure, if_neg]
    exact fun hb => Bool.noConfusion hb.1

theorem wrO_privacy : Spec.wrO_privacy := by
  intro lam I X W PP IVK ISK Pf B c R A S ζ h
  exact pr_privacy lam I X W PP IVK ISK Pf B c.print (c.arg A).V R A S ζ h

theorem wrO_arg : Spec.wrO_arg := by
  intro lam I X W PP IVK ISK Pf B c d R A E S α ε ζ h hB hF
  exact ⟨wrO_complete lam I X W PP IVK ISK Pf B c R A α hF h.completeness,
    wrO_binding lam I X W PP IVK ISK Pf B c d R A E ε hB h.indexBinding,
    wrO_privacy lam I X W PP IVK ISK Pf B c R A S ζ h.indexPrivacy⟩

end Run
