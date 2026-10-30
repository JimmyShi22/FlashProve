-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowBRulesStep.lean: further rules for round-by-round knowledge soundness of IORs in a batch:
steps without rounds, and joints whose condition may fail.

Statements and proofs. No protocol occurs here. It goes on from Ior/KnowBRules.lean.
`IOR.KnowB` (Ior/BatchSeq.lean) is round-by-round knowledge soundness, by sets of bad values, of an
IOR run in the slots of a batch, for the admissible vectors of statements.

Main names:
  `Spec.knowB_pre`: a step without rounds, then R (Ior/Frame.lean: `R.pre f g`): if R has `KnowB`
    and the step is knowledge sound (it carries the condition forward and witnesses backward), then
    `R.pre f g` has `KnowB`, same errors, for any extractor that agrees with "R's, then the step's"
    where the step outputs a statement; a vector is admissible if the vector of the stepped
    statements is. (One instance: Ior/KnowCollRulesFrame.lean: `goodB_pre`.)
  `Spec.knowB_pure`: a step without rounds alone, if it carries witnesses backward: every vector is
    admissible.
  `Spec.knowB_cf`: from "on the statements with a condition" to the joints whose condition is moved
    into the relaxed relation (Ior/KnowCollGood.lean: `Rels.cf`), if the link carries the condition:
    the form in which chains are made.

Limits: what the heads of Ior/BatchSeq.lean and Ior/KnowBRules.lean list as not said is not said
here either.
Terms: lean/GLOSSARY.md.
-/
import Ior.KnowBRules

set_option autoImplicit false

namespace Iop
open Prob

namespace Spec
open IOR

/-- A step without rounds, then R. -/
def knowB_pre : Prop :=
  ∀ (Xi Xi' Xo : Type) (Ei Ei' Eo : ExtSpec) (Wi Wi' Wo : Type) (R : IOR Xi Ei Xo Eo)
      (A : RoundSplits R.shape) (N : ℕ) (adm : (Fin N → Option (Xi × Ei.Str)) → Prop)
      (on : Xi × Ei.Str → Prop) (RA : Xi × Ei.Str → Wi → Prop) (RB : Xo × Eo.Str → Wo → Prop)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ε : Err R.shape) (f : Xi' → Option Xi)
      (g : ExtMap Ei' Ei) (on' : Xi' × Ei'.Str → Prop) (RA' : Xi' × Ei'.Str → Wi' → Prop)
      (back : Xi' × Ei'.Str → Wi → Wi') (ext' : Xi' × Ei'.Str → Tr R.shape → Wo → Wi'),
    R.KnowB A N adm on RA RB ext ε → (∀ x y x₁, on' (x, y) → f x = some x₁ → on (x₁, g.map y)) →
    (∀ x y x₁ w, on' (x, y) → f x = some x₁ → RA (x₁, g.map y) w → RA' (x, y) (back (x, y) w)) →
    (∀ a x₁ τ w, f a.1 = some x₁ → ext' a τ w = back a (ext (x₁, g.map a.2) τ w)) →
    (R.pre f g).KnowB A N
      (fun a => adm fun j => (a j).bind fun aj => (f aj.1).map fun x₁ => (x₁, g.map aj.2))
      on' RA' RB ext' ε

/-- A step without rounds, alone. -/
def knowB_pure : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (f : Xi → Option Xo) (g : ExtMap Ei Eo)
      (N : ℕ) (on : Xi × Ei.Str → Prop) (RA : Xi × Ei.Str → Wi → Prop)
      (RB : Xo × Eo.Str → Wo → Prop) (back : Xi × Ei.Str → Wo → Wi),
    (∀ x y x' w, on (x, y) → f x = some x' → RB (x', g.map y) w → RA (x, y) (back (x, y) w)) →
    (IOR.pure f g).KnowB PUnit.unit N (fun _ => True) on RA RB (fun a _ w => back a w) ()

/-- To the joints whose condition may fail. -/
def knowB_cf : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (R : IOR Xi Ei Xo Eo) (A : RoundSplits R.shape) (N : ℕ)
      (adm : (Fin N → Option (Xi × Ei.Str)) → Prop) (on : Xi × Ei.Str → Prop)
      (on' : Xo × Eo.Str → Prop) (RA : Xi × Ei.Str → Wi → Prop) (RB : Xo × Eo.Str → Wo → Prop)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ε : Err R.shape),
    (∀ a τ b, on a → R.red.out a τ = some b → on' b) → R.KnowB A N adm on RA RB ext ε →
    R.KnowB A N adm (fun _ => True) (Reduction.orOff on RA) (Reduction.orOff on' RB) ext ε

end Spec

open IOR

theorem knowB_pre : Spec.knowB_pre := by
  rintro Xi Xi' Xo Ei Ei' Eo Wi Wi' Wo R A N adm on RA RB ext ε f g on' RA' back ext'
    ⟨bad, c, J⟩ hon hback hext
  refine ⟨fun a => ((f a.1).map fun x₁ => bad (x₁, g.map a.2)).getD (BadFam.empty R.shape),
    ?_, fun a ha => ?_⟩
  · rintro ⟨x, y⟩ τ b w ha hτ hb hw
    have hb' : ((f x).bind fun x₁ => R.out x₁ (g.map y) τ).map (fun xo => (xo, R.imp (g.map y) τ)) =
        some b := hb
    cases hx : f x with
    | none =>
      rw [hx] at hb'
      cases hb'
    | some x₁ =>
      rw [hx, Option.bind_some] at hb'
      have hτ' : (((f x).map fun x₁ => bad (x₁, g.map y)).getD (BadFam.empty R.shape)).Clean τ := hτ
      rw [hx] at hτ'
      rw [hext (x, y) x₁ τ w hx]
      exact hback x y x₁ _ ha hx (c (x₁, g.map y) τ b w (hon x y x₁ ha hx) hτ' hb' hw)
  · refine JWithin.weaken N R.shape A ε _ _ (J _ ha) fun j p hp => ?_
    beta_reduce at hp
    cases hx : a j with
    | none =>
      rw [hx] at hp
      cases hp
    | some aj =>
      rw [hx] at hp
      obtain rfl : _ = p := Option.some.inj hp
      cases hf : f aj.1 with
      | none =>
        right
        show ((f aj.1).map fun x₁ => bad (x₁, g.map aj.2)).getD _ = _
        rw [hf]
        rfl
      | some x₁ =>
        refine Or.inl ⟨(false, bad (x₁, g.map aj.2)), ?_, ?_, fun h => Bool.noConfusion h⟩
        · show ((some aj).bind fun aj => (f aj.1).map fun x₁ => (x₁, g.map aj.2)).map _ = _
          rw [Option.bind_some, hf]
          rfl
        · show ((f aj.1).map fun x₁ => bad (x₁, g.map aj.2)).getD _ = _
          rw [hf]
          rfl

theorem knowB_pure : Spec.knowB_pure := by
  intro Xi Xo Ei Eo Wi Wo f g N on RA RB back h
  refine ⟨fun _ => (), ?_, fun _ _ => trivial⟩
  rintro ⟨x, y⟩ τ b w ha - hb hw
  have hb' : (f x).map (fun xo => (xo, g.map y)) = some b := hb
  obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.mp hb'
  exact h x y x' w ha hx hw

theorem knowB_cf : Spec.knowB_cf := fun Xi Xo Ei Eo Wi Wo R A N adm on on' RA RB ext ε hc h =>
  (knowB_iff_orOff Xi Xo Ei Eo Wi Wo R A N adm on RA (Reduction.orOff on' RB) ext ε).1
    (knowBInto_of_carry Xi Xo Ei Eo Wi Wo R A N adm on on' RA RB ext ε
      (fun a τ b hb ha => hc a τ b ha hb) h)

end Iop
