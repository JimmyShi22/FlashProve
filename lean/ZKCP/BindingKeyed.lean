-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  ZKCP/BindingKeyed.lean: the experiment of index binding with the key in its outcome. Whatever
  follows, for every key and trace, from
  "V accepts and the outcome is not bad" is true of the key on which V ran, except with the
  probability of the bad event.
  Why. The outcome of the experiment of `HasIndexBinding` (BindingOutcome) has V's bit,
  the extracted index, the instance and the witness: not the key. A sentence such as "what V accepts
  is true at the member that THE KEY names" speaks of the key.
    bindingExpK A E Ct Pt      `HasIndexBinding`'s experiment, step for step (ZKCP/Defs.lean:
                               bindingExp), which also puts out the key that the committer gave
    Pr_keyed_le                for every property Φ of (key, extracted index, instance): if for all
                               keys vk, traces tr, x, w
                               "⟨true, E.Ei vk tr, x, w⟩ is not bad" implies Φ vk (E.Ei vk tr) x,
                               then
                               Pr[V accepts and not Φ (the key) i* x] ≤ Pr[bad]
    good_sigmaU                for a scheme whose key names its member (ZKCP/Sigma.lean) and an
                               extractor that names the key's member:
                               an accepting outcome that is not bad for
                               `IndexedRelation.sigmaU R`: ∃ i, Es.Ei vk tr = some (vk.1, i), and x
                               is in the language of the member vk.1 at i
  What it does not say. Nothing on any scheme. bindingExpK is this library's own, not part of the
  definition in ZKCP/Defs.lean.
-/
import ZKCP.Sigma

set_option autoImplicit false

namespace ZKCP
open scoped ENNReal

variable {lam : ℕ}

/-- The experiment of ZKCP/Defs.lean, `HasIndexBinding`, which also puts out the key -/
def bindingExpK {I X W IVK ISK Pf St : Type} (A : Arg lam I X W IVK ISK Pf)
    (E : Extractor lam I X W IVK Pf) (Ct : OComp lam (IVK × St)) (Pt : St → OComp lam (X × Pf)) :
    OComp lam (IVK × BindingOutcome I X W) :=
  Ct.withTrace.bind fun o =>
      (Pt o.1.2).withTrace.bind fun o' => (A.V o.1.1 o'.1.1 o'.1.2).bind fun b =>
    .pure (o.1.1, ⟨b, E.Ei o.1.1 o.2, o'.1.1, E.Ew o.1.1 o.2 o'.1.1 o'.1.2 o'.2⟩)

theorem Pr_keyed_le {I X W PP IVK ISK Pf St : Type} (R : IndexedRelation I X W PP)
    (A : Arg lam I X W IVK ISK Pf) (E : Extractor lam I X W IVK Pf) (Φ : IVK → Option I → X → Prop)
    (hΦ : ∀ vk tr x w,
      (⟨true, E.Ei vk tr, x, w⟩ : BindingOutcome I X W) ∉ bindingBad R → Φ vk (E.Ei vk tr) x)
    (Ct : OComp lam (IVK × St)) (Pt : St → OComp lam (X × Pf)) :
    Pr (bindingExpK A E Ct Pt) (fun _ => {p | p.2.accept = true ∧ ¬ Φ p.1 p.2.iStar p.2.x}) ≤
      Pr (bindingExp A E Ct Pt) (fun _ => bindingBad R) := by
  refine MeasureTheory.lintegral_mono fun f => ?_
  show prob ((Ct.withTrace.bind fun o =>
        (Pt o.1.2).withTrace.bind fun o' =>
          (A.V o.1.1 o'.1.1 o'.1.2).bind fun b =>
            .pure (o.1.1,
                (⟨b, E.Ei o.1.1 o.2, o'.1.1,
                  E.Ew o.1.1 o.2 o'.1.1 o'.1.2 o'.2⟩ : BindingOutcome I X W))).run f)
      {p | p.2.accept = true ∧ ¬ Φ p.1 p.2.iStar p.2.x} ≤
    prob ((Ct.withTrace.bind fun o =>
        (Pt o.1.2).withTrace.bind fun o' =>
          (A.V o.1.1 o'.1.1 o'.1.2).bind fun b =>
            .pure (⟨b, E.Ei o.1.1 o.2, o'.1.1,
                E.Ew o.1.1 o.2 o'.1.1 o'.1.2 o'.2⟩ : BindingOutcome I X W)).run f) (bindingBad R)
  refine prob_run_bind_le2 f _ _ _ fun o =>
    prob_run_bind_le2 f _ _ _ fun o' => prob_run_bind_le2 f _ _ _ fun b => ?_
  show prob (PMF.pure _) _ ≤ prob (PMF.pure _) _
  rw [prob_pure, prob_pure]
  by_cases h2 : (⟨b, E.Ei o.1.1 o.2, o'.1.1,
      E.Ew o.1.1 o.2 o'.1.1 o'.1.2 o'.2⟩ : BindingOutcome I X W) ∈ bindingBad R
  · rw [if_pos h2]
    split <;> simp
  · rw [if_neg h2, if_neg]
    rintro ⟨ha, hn⟩
    have hb : b = true := ha
    subst hb
    exact hn (hΦ _ _ _ _ h2)

/-- At a scheme whose key names its member, for an extractor whose index names the key's member
(`hE`): if an accepting outcome is not bad for `IndexedRelation.sigmaU R`, the extractor returns
some (vk.1, i), and x is in the language of the member vk.1 at i. -/
theorem good_sigmaU {T I X W : Type} {IVK Pf : T → Type} {R : T → IndexedRelation I X W Unit}
    (Es : Extractor lam (T × I) X W (Σ t, IVK t) (Σ t, Pf t))
    (hE : ∀ vk tr i, Es.Ei vk tr = some i → i.1 = vk.1) (vk : Σ t, IVK t) (tr : Trace lam) (x : X)
    (w : W) (h : (⟨true, Es.Ei vk tr, x, w⟩ : BindingOutcome (T × I) X W) ∉
      bindingBad (IndexedRelation.sigmaU R)) :
    ∃ i : I, Es.Ei vk tr = some (vk.1, i) ∧ ∃ w', (R vk.1).rel i x w' := by
  have h2 : x ∈ (IndexedRelation.sigmaU R).L (Es.Ei vk tr) := by
    by_contra hc
    exact h ⟨rfl, Or.inl hc⟩
  cases e : Es.Ei vk tr with
  | none => rw [e] at h2; exact h2.elim
  | some j =>
    rw [e] at h2
    obtain ⟨w', hw⟩ := h2
    have f := hE vk tr j e
    obtain ⟨t, i⟩ := j
    simp only at f
    subst f
    exact ⟨i, rfl, w', hw⟩

end ZKCP
