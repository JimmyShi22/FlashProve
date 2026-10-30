-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/LanguageRelation.lean: an indexed relation (ZKCP/Defs.lean) without witnesses.

`languageRelation IsTrue` is the relation "the instance is true at the index". Its witnesses and
its public parameters (`pp`) are the one element of `Unit`.
`bindingBad_languageRelation`: for this relation the bad event of index binding is "the verifier
accepts, and no index was extracted at which the instance is true".
`hasIndexBindingWith_languageRelation_iff`: index binding written with that event.
The file says nothing about a particular scheme.
-/
import ZKCP.Basic

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP

variable {lam : ℕ} {I X IVK ISK Pf : Type}

/-- The relation "the instance is true at the index", without a witness and with no public
parameters. -/
def languageRelation {I X : Type} (IsTrue : I → X → Prop) : IndexedRelation I X Unit Unit where
  rel i x _ := IsTrue i x
  pp _ := ()

/-- For a relation without witnesses the bad event of index binding (`bindingBad`) is: the verifier
accepts, and no index was extracted at which the instance is true. -/
theorem bindingBad_languageRelation (IsTrue : I → X → Prop) :
    bindingBad (languageRelation IsTrue)
      = {o | o.accept = true ∧ ¬ ∃ i, o.iStar = some i ∧ IsTrue i o.x} := by
  ext o
  obtain ⟨b, _ | i, x, w⟩ := o
  · refine ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, Or.inl (Set.notMem_empty x)⟩⟩
    rintro ⟨j, e, -⟩
    exact Option.some_ne_none j e.symm
  · constructor
    · rintro ⟨hb, hor⟩
      refine ⟨hb, ?_⟩
      rintro ⟨j, e, hj⟩
      have e' : i = j := Option.some.inj e
      subst e'
      rcases hor with h | h
      · exact h ⟨(), hj⟩
      · exact h hj
    · rintro ⟨hb, hn⟩
      exact ⟨hb, Or.inr fun h => hn ⟨i, rfl, h⟩⟩

/-- Index binding with a named extractor (`HasIndexBindingWith`) for a relation without witnesses,
with the bad event written out. -/
theorem hasIndexBindingWith_languageRelation_iff (IsTrue : I → X → Prop)
    (A : Arg lam I X Unit IVK ISK Pf) (E : Extractor lam I X Unit IVK Pf) (ε : ℕ → ℕ → ℝ≥0∞) :
    HasIndexBindingWith (languageRelation IsTrue) A E ε ↔
      ∀ (tC tP : ℕ) (St : Type) (Ct : OComp lam (IVK × St)) (Pt : St → OComp lam (X × Pf)),
        Ct.QueryBound tC → (∀ st, (Pt st).QueryBound tP) →
          Pr (bindingExp A E Ct Pt)
            (fun _ => {o | o.accept = true ∧ ¬ ∃ i, o.iStar = some i ∧ IsTrue i o.x})
              ≤ ε tC tP := by
  unfold HasIndexBindingWith
  rw [bindingBad_languageRelation]

end ZKCP
