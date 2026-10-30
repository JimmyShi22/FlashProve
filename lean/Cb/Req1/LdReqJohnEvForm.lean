-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqJohnEvForm.lean: the forms of zero-evaders that have a theorem in this library, as one
predicate on data, closed under products, fewer rows and a larger number; and every zero-evader of
such a form has the property `Evader.OK`.

One inductive predicate, one statement (`Cb.Spec.evForm_ok`), its proof and one lemma
(`Evader.ok_inst`). Generic: any finite field. Nothing assumed beyond the hypotheses of the
statements and whatever the arguments hold as proofs.
A zero-evader `Z : Evader E J` (Cb/Gen/BatEvader.lean) has seeds `Z.D`, coefficients
`Z.ze : Z.D → J → E` for the rows J, and a number `Z.err`.

Why: the records of conditions ask, of each public map of
coefficients (of a batching, a bridge, a switch), `Evader.OK` (Cb/Gen/BatEvader.lean): a vector
other than 0 is annihilated by at most `Z.err` seeds. That is a property of public data, but it is
a property. For the forms below it is a theorem; "Z is of such a form" is a condition on data alone.

Main names:
  `Z.Form`: Z is: independent coefficients (`Evader.indep`); the powers of one challenge (`powers`);
    the equality kernel at a point, on the cube (`eqPt`) or on numbers below 2^g (`eqNum`); the
    coefficients (1 - ρ, ρ) (`line`); the one coefficient 1 (`one`); the Lagrange weights of an
    injective domain at a point (`lag`); or a product of two such (`prod`: the number is
    err₁ |D₂| + |D₁| err₂); or such a one on fewer rows, along an injective map (`comap`); or such a
    one with a larger number (`up`).
  `Spec.evForm_ok`: `Z.Form → Z.OK`.

Limits: this file does not say that the evaders at these places are of these forms:
they are free letters of the data there; no record asks `Z.Form`, but for `LdWfE.Rest2Ev` and
`LdFrontRef.ProtoEv` (Cb/Req1/LdReqJohnEvRec.lean) and the records of Cb/Gl/GlFinalEv.lean. By
reading, in the theorems of a write-up of ours (lean/CREDITS.md) the map is any
zero-evader. This file does not say that a number is small against the number of seeds. It says
nothing on sample maps (`Sample.OK`,
`Sample.OKOn`).
Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Gen.BatEvaderProofs
import Cb.Gen.BatEvaderNumProofs
import Cb.Ld.LdBatProofs
import Cb.Ld.LdZeroProofs
import Cb.Ld.LdZeroSkipProofs

set_option autoImplicit false

namespace Cb
open Prob

/-- The forms of zero-evaders that have a theorem. -/
inductive Evader.Form {E : Type} [Field E] [Fintype E] : {J : Type} → Evader E J → Prop
  | indep (J : Type) [Fintype J] [DecidableEq J] : Evader.Form (Evader.indep E J)
  | powers (n : ℕ) : Evader.Form (Evader.powers E n)
  | eqPt (ι : Type) [Fintype ι] [DecidableEq ι] : Evader.Form (Evader.eqPt E ι)
  | eqNum (g n : ℕ) : n ≤ 2 ^ g → Evader.Form (Evader.eqNum E g n)
  | line : Evader.Form (Evader.line E)
  | one : Evader.Form (Evader.one E)
  | lag {D : Type} [Fintype D] [DecidableEq D] (dom : D → E) :
      Function.Injective dom → Evader.Form (Evader.lag E dom)
  | prod {I₁ I₂ : Type} [Fintype I₁] [Fintype I₂] (Z₁ : Evader E I₁) (Z₂ : Evader E I₂) :
      Evader.Form Z₁ → Evader.Form Z₂ → Evader.Form (Z₁.prod Z₂)
  | comap {J J₀ : Type} [Fintype J₀] (Z : Evader E J₀) (e : J → J₀) :
      Function.Injective e → Evader.Form Z → Evader.Form (Z.comap e)
  | up {J : Type} (Z : Evader E J) (n : ℕ) :
      Z.err ≤ n → Evader.Form Z → Evader.Form { Z with err := n }

/-- States: a zero-evader of such a form has the property `Evader.OK`, for every `Fintype` instance
on its rows. -/
def Spec.evForm_ok : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (J : Type) (Z : Evader E J), Z.Form → ∀ [Fintype J], Z.OK

/-- The property does not see which enumeration of the rows is taken. -/
theorem Evader.ok_inst {E J : Type} [Field E] (Z : Evader E J)
    (i i' : Fintype J) (h : @Evader.OK E J _ i Z) : @Evader.OK E J _ i' Z := by
  rw [Subsingleton.elim i' i]
  exact h

theorem evForm_ok : Spec.evForm_ok := by
  intro E _ _ J Z h
  induction h with
  | indep J =>
      have h := ok_indep E J
      intro i
      exact Evader.ok_inst _ _ i h
  | powers n =>
      have h := ok_powers E n
      intro i
      exact Evader.ok_inst _ _ i h
  | eqPt ι =>
      have h := ok_eqPt E ι
      intro i
      exact Evader.ok_inst _ _ i h
  | eqNum g n hn =>
      have h := ok_eqNum E g n hn
      intro i
      exact Evader.ok_inst _ _ i h
  | line =>
      have h := ldBat_ok_line E
      intro i
      exact Evader.ok_inst _ _ i h
  | one =>
      have h : (Evader.one E).OK := ldZero_ok_one E
      intro i
      exact Evader.ok_inst _ _ i h
  | lag dom hd =>
      have h := ldZero_ok_lag E _ dom hd
      intro i
      exact Evader.ok_inst _ _ i h
  | prod Z₁ Z₂ _ _ ih₁ ih₂ =>
      have h := ldZero_ok_prod E _ _ Z₁ Z₂ ih₁ ih₂
      intro i
      exact Evader.ok_inst _ _ i h
  | comap Z e he _ ih =>
      intro i
      exact ok_comap E _ _ Z e he ih
  | up Z n hn _ ih =>
      intro i v hv
      exact le_trans (ih v hv) hn

end Cb
