-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Rel.lean: a tool for the hypothesis `AdvAlw` of the lemma on deferred programming of
the random oracle (`Spec.defer2`, CompileK/SpecDefer2.lean): from single steps (`Step.Alw`) to runs
(`AdvAlw`), for two challengers: if the states of two challengers are related, the relation keeps
the tables equal and is kept when both tables are replaced by one table, and whenever a step of the
first has `Step.Alw` with an end condition Post₁ the second's step has `Step.Alw` with the end
"there is an end of the first's step with Post₁, an equal reply and related states", then `AdvAlw`
(nothing asked at a halt) passes from the first challenger to the second, for every adversary.

One statement (`Rom.DeferTail2.Spec.advAlw_rel`) and its proof. Generic. The companion of
`interact_cpl` (Rom/SkipRun.lean) for that hypothesis. Nothing assumed beyond the hypotheses of the
statements and whatever the arguments hold as proofs. Programs, states and the two modes:
Rom/Defer.lean. `AdvAlw C cl J G Fn A s` asks
`Step.Alw` of every step of the challenger C that the adversary A can call from s, and Fn at a halt.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Notation: `cl`: `PtCls S K` (CompileK/SpecDefer2.lean): classes of points; `J`: `K → Bool`;
`J κ = true`: κ is a joint class (CompileK/SpecDefer2.lean); `G`, `Fn`: `DSt S → Prop`: predicates
on states; in `Spec.defer2` (CompileK/SpecDefer2.lean): `DSt.Ok2`, `DSt.CntK2`; `Step.Alw`
(CompileK/SpecDefer2.lean): a predicate, by recursion along a step of the challenger.

Limits: the property at a halt is not carried (counts may differ between the two):
CompileK/Defer2Supp.lean adds it from a theorem on the support.
-/
import CompileK.Defer2Adv

set_option autoImplicit false

namespace Rom
namespace DeferTail2
open DeferTail

def Spec.advAlw_rel : Prop :=
  ∀ (S : OSpec) (sp : Split S) (K : Type) (cl : PtCls S K) (J : K → Bool) (G : DSt S → Prop)
      (Out In α : Type) (C₁ C₂ : Chall S sp Out In) (Rel : C₁.τ × DSt S → C₂.τ × DSt S → Prop),
    (∀ s₁ s₂, Rel s₁ s₂ → s₁.2.table = s₂.2.table) →
    (∀ s₁ s₂ T, Rel s₁ s₂ → Rel (s₁.1, withT s₁.2 T) (s₂.1, withT s₂.2 T)) →
    (∀ s₁ s₂ m (Post₁ : (In × C₁.τ) × DSt S → Prop), Rel s₁ s₂ →
      (C₁.step s₁.1 m).Alw cl J G s₁.2 Post₁ →
      (C₂.step s₂.1 m).Alw cl J G s₂.2 fun y₂ =>
        ∃ y₁, y₁.1.1 = y₂.1.1 ∧ Rel (y₁.1.2, y₁.2) (y₂.1.2, y₂.2) ∧ Post₁ y₁) →
    ∀ (A : Adv S Out In α) (s₁ : C₁.τ × DSt S) (s₂ : C₂.τ × DSt S),
      Rel s₁ s₂ → AdvAlw C₁ cl J G (fun _ => True) A s₁ → AdvAlw C₂ cl J G (fun _ => True) A s₂

theorem advAlw_rel : Spec.advAlw_rel := by
  intro S sp K cl J G Out In α C₁ C₂ Rel ht hq hc A
  induction A with
  | halt a => exact fun _ _ _ _ => trivial
  | sample n k ih => exact fun s₁ s₂ h hA r => ih r s₁ s₂ h (hA r)
  | query o q k ih =>
    intro s₁ s₂ h hA y hy
    rw [← ht s₁ s₂ h] at hy
    exact ih y.1 _ _ (hq s₁ s₂ y.2 h) (hA y hy)
  | call m k ih =>
    intro s₁ s₂ h hA
    refine alw_mono (fun y₂ hy => ?_) _ _ (hc s₁ s₂ m _ h hA)
    obtain ⟨y₁, e, hR, hP⟩ := hy
    rw [← e]
    exact ih _ _ _ hR hP

end DeferTail2
end Rom
