-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartIff.lean: two relations that say the same, point by point, are equal.

An extensionality lemma for the record of relations at a joint of a chain of reductions. One
statement (`Cb.Spec.ldPartIff_eq`) and its proof. Glue on Lean's own records; nothing of this
protocol's technical report (lean/CREDITS.md) is rendered here.

Main names:
  `Spec.ldPartIff_eq`: a relation (`Rels`, Ior/Chain.lean) has exactly four fields: exact (the
    honest side's relation), relaxed (what knowledge soundness speaks of), condition, core.
    Equivalence of the first three at all arguments and equality of the cores ⇒ A = B, by
    extensionality of functions and of propositions.

Why: what the next segment reads of what a closing carries
is known clause by clause (three equivalences and an
equation): it comes by choice. A built front's entry relation is known in the same way.
Cb/Part/LdPartNext.lean states the model's step between two relations
that are written out. With the equation every hypothesis of every block goes over by rewriting.
It can hide nothing: an equivalence that held only under the condition "on" would not meet the
premises.

Limits: this file does not say that the premises can be had from what a closing carries.





Terms: lean/GLOSSARY.md.
-/
import Ior.Chain

set_option autoImplicit false

namespace Cb

open Iop IOR

namespace Spec

def ldPartIff_eq : Prop :=
  ∀ (K X W : Type) (E₀ : ExtSpec) (A B : Rels K X E₀ W), (∀ x y w, A.rel x y w ↔ B.rel x y w) →
    (∀ a w, A.relR a w ↔ B.relR a w) → (∀ a, A.on a ↔ B.on a) → (∀ w, A.core w = B.core w) → A = B

end Spec

theorem ldPartIff_eq : Spec.ldPartIff_eq := by
  intro K X W E₀ A B h1 h2 h3 h4
  obtain ⟨a1, a2, a3, a4⟩ := A
  obtain ⟨b1, b2, b3, b4⟩ := B
  have e1 : a1 = b1 := funext fun x => funext fun y => funext fun w => propext (h1 x y w)
  have e2 : a2 = b2 := funext fun a => funext fun w => propext (h2 a w)
  have e3 : a3 = b3 := funext fun a => propext (h3 a)
  have e4 : a4 = b4 := funext h4
  subst e1 e2 e3 e4
  rfl

end Cb
