-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowRules.lean: rules for round-by-round knowledge soundness of one interactive oracle
reduction (IOR, Ior/Ior.lean), with no condition on any honest prover.

Ior/KnowCollRulesFrame.lean has the rules on a carried part and on steps without rounds for a whole
bundle (`GoodB`, `GoodT`); Ior/KnowCollGood.lean has the last (`goodT_cf`). A bundle holds knowledge
soundness together with completeness, hiding and budgets. Here the clause on
knowledge soundness (`know`) and the clause on outputs (`onOut`) are carried alone.
Statements. The proofs: Ior/KnowRulesProofs.lean. No protocol, no code occurs here.

Main names:
  `Spec.know_beside`, `Spec.onOut_beside`: a reduction beside a part of the statement that is handed
    on unchanged (`R.keep Z F`; joints `A.beside S`, `B.beside S`): same errors; the extractor
    copies the carried part of the witness.
  `Spec.know_pure`, `Spec.onOut_pure`: a step without rounds (`IOR.pure f g`): knowledge soundness
    is the backward step on witnesses; the clause on outputs is read off f and g.
  `Spec.know_cf`: from joints with a condition to the joints whose condition may fail (`Rels.cf`,
    Ior/KnowCollGood.lean), if the reduction carries the condition.

Limits: Nothing on completeness, hiding, budgets or locality. No statement bounds an error.
Terms: lean/GLOSSARY.md: bundle, extractor, IOR, joint.

-/
import Ior.KnowCollRulesFrame

set_option autoImplicit false

namespace Iop
namespace Spec
open IOR

/-- States: knowledge soundness of R from A to B gives that of R beside a carried part, from
`A.beside S` to `B.beside S`, at the same errors. -/
def know_beside : Prop :=
  ∀ (K Xi Xo Z : Type) (Ei Eo F : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo Wz : Type)
      (A : Rels Unit Xi Ei Wi) (B : Rels Unit Xo Eo Wo)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ε : Err R.shape) (S : Rels K Z F Wz),
    R.red.Know A.on A.relR B.relR ext ε →
    (R.keep Z F).red.Know (A.beside S).on (A.beside S).relR (B.beside S).relR
      (fun a τ w => (ext (a.1.1, a.2.1) τ w.1, w.2)) ε

/-- States: if R carries the condition of A to that of B, then R beside a carried part carries that
of `A.beside S` to that of `B.beside S`. -/
def onOut_beside : Prop :=
  ∀ (K Xi Xo Z : Type) (Ei Eo F : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo Wz : Type)
      (A : Rels Unit Xi Ei Wi) (B : Rels Unit Xo Eo Wo) (S : Rels K Z F Wz),
    (∀ a τ b, A.on a → R.red.out a τ = some b → B.on b) →
    ∀ a τ b, (A.beside S).on a → (R.keep Z F).red.out a τ = some b → (B.beside S).on b

/-- States: a step without rounds has knowledge soundness, with the extractor `back`, if `back`
turns every witness of the output into a witness of the input. -/
def know_pure : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (f : Xi → Option Xo) (g : ExtMap Ei Eo) (Wi Wo : Type)
      (on : Xi × Ei.Str → Prop) (RA : Xi × Ei.Str → Wi → Prop) (RB : Xo × Eo.Str → Wo → Prop)
      (back : Xi × Ei.Str → Wo → Wi) (ε : Err (IOR.pure f g).shape),
    (∀ a x' w, on a → f a.1 = some x' → RB (x', g.map a.2) w → RA a (back a w)) →
    (IOR.pure f g).red.Know on RA RB (fun a _ w => back a w) ε

/-- States: a step without rounds carries a condition `on` to a condition `on'` if its two maps
do. -/
def onOut_pure : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (f : Xi → Option Xo) (g : ExtMap Ei Eo)
      (on : Xi × Ei.Str → Prop) (on' : Xo × Eo.Str → Prop),
    (∀ a x', on a → f a.1 = some x' → on' (x', g.map a.2)) →
    ∀ a τ b, on a → (IOR.pure f g).red.out a τ = some b → on' b

/-- States: knowledge soundness from A to B, with the clause on outputs, gives knowledge soundness
from `A.cf` to `B.cf`: on all statements, a statement outside the condition counting as having
every witness. Same errors, same extractor. -/
def know_cf : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ε : Err R.shape),
    R.red.Know A.on A.relR B.relR ext ε →
    (∀ a τ b, A.on a → R.red.out a τ = some b → B.on b) →
    R.red.Know A.cf.on A.cf.relR B.cf.relR ext ε

end Spec
end Iop
