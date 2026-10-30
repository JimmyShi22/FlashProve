-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/CodeList.lean: the properties of a code with encoder, with a list in the place of unique
decoding.

Definitions and statements (the latter in `Cb.Spec`); the proofs are in Cb/Gen/CodeListProofs.lean.

Why: `Code.Enc.Props` (Code/Iface.lean) has the field "unique : 2 e < d". Once the radius is past
half the distance, several codewords may lie within it of a single word, and what a protocol then
needs of a code is a number L with "every word has at most L codewords within e".
This file has a record parallel to
`Code.Enc.Props`, without "unique" and with that clause.

Main names:
 1. Two notions at one radius e and for tables with rows named by R (distance counts columns):
    `Enc.ListAt E R e L`: the interleaved code is list-decodable at the radius e with list size L;
    `Enc.MCAat E R e bad`: mutual correlated agreement on lines f0 + θ f1, at most "bad"
      exceptional θ (`Spec.mca_iff_at`: `Code.Enc.MCA` is `Enc.MCAat` for all finite R with one
      number).
 2. `Enc.Core`: what does not depend on a radius, and speaks of F only: place, dist, hides as in
    `Code.Enc.Props`, and 0 < d (in `Code.Enc.Props` that follows from "unique"; with dist it says
    that the encoder is injective, so that a list of messages is a list of codewords).
 3. `Enc.ListProps E L`: the parallel record, at the code's own radius "e" and count "mca".
 4. `Enc.Prox E ok L bad`: list size and count of exceptional θ as functions of the radius and of
    the number of rows, for all radii with "ok e": one code can so be used at several radii, and a
    bound that grows with the number of rows can be stated.
 5. The statements.
    `Spec.listProps_of_props`: (a) from `Code.Enc.Props`, L = 1. `Spec.props_of_listProps`: back,
      given 2 e < d.
    `Spec.listProps_of_johnson`: (b) for a code with `Core`, below the Johnson radius, L =
      `listMax n d e` (Cb/Gen/JohnsonList.lean), with mutual correlated agreement at that radius as
      a hypothesis.
    `Spec.prox_third`: from `HasDist C.G C.d`, without any hypothesis on agreement, for all radii
      with 3 e < d: L = 1, e + 1 exceptional θ.
    `Spec.prox_johnson`: from `HasDist C.G C.d`, for all radii below the Johnson radius, the list
      proved, the agreement a hypothesis.
    `Spec.core_props`: a code with `Core` has all of `Code.Enc.Props` at the radius 0 and the count
      1, so that every fact of Code/Facts.lean on hiding, distance and injectivity is at hand.

Limits: no proximity gap beyond a third of the distance is proved or assumed here: where one is
needed it is a hypothesis of the statement, in the statement's own text. Which statement of the
literature gives it for which code, and with which count, is not this file's matter.
The list is of full messages (any vectors of length k). This file says nothing on the part of a
message behind the randomness; nothing on out-of-domain samples, on decoding functions, on groups
of codes under a repetition, on erasures, or on running times; nothing on protocols or numerals.
That the list size should be an abstract number of the code, and a function of the radius, follows
advice (lean/CREDITS.md).
Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.JohnsonList

set_option autoImplicit false

namespace Code
open Prob Blocks

variable {F : Type} [Field F]

/-- A list at one radius: every table with rows R decodes to at most L tables of full messages. -/
def Enc.ListAt (C : Enc F) (E : Type) [Field E] [Finite E] [Algebra F E]
    (R : Type) [Finite R] (e L : ℕ) : Prop :=
  ∀ f : R → Fin C.n → E, cnt (fun M : R → Fin C.k → E => DecodesTo (C.GE E) e f M) ≤ L

/-- Mutual correlated agreement on lines, for tables with rows R: the clause of `Code.Enc.MCA` at
this R. -/
def Enc.MCAat (C : Enc F) (E : Type) [Field E] [Finite E] [Algebra F E] (R : Type)
    [Finite R] (e bad : ℕ) : Prop :=
  ∀ f₀ f₁ : R → Fin C.n → E,
    cnt (fun θ : E => ∃ S : Finset (Fin C.n), C.n ≤ S.card + e ∧
      C.OnCode E (fun a j => f₀ a j + θ * f₁ a j) S ∧ ¬ (C.OnCode E f₀ S ∧ C.OnCode E f₁ S)) ≤ bad

/-- What does not depend on a radius. -/
structure Enc.Core (C : Enc F) [Fintype F] : Prop where
  place  : C.msg + C.r ≤ C.k
  /-- a non-zero vector has an image of weight at least d -/
  dist   : ∀ v : Fin C.k → F, v ≠ 0 → C.d ≤ cnt (fun j => C.G.mulVec v j ≠ 0)
  pos    : 0 < C.d
  /-- any b positions of an encoding are uniform, for every message -/
  hides  : ∀ (S : Finset (Fin C.n)), S.card ≤ C.b →
    ∀ m : Fin C.msg → F,
      (PMF.uniformOfFintype (Fin C.r → F)).map (fun ρ => fun j : S => C.enc m ρ j) =
        PMF.uniformOfFintype (S → F)

/-- The properties of a code with encoder, with a list: `Code.Enc.Props` without "unique", with
0 < d and the list size L. -/
structure Enc.ListProps (C : Enc F) [Fintype F] (E : Type) [Field E]
    [Finite E] [Algebra F E] (L : ℕ) : Prop extends C.Core where
  /-- every table has at most L tables of messages within the radius e of the code -/
  list : ∀ (R : Type) [Finite R], C.ListAt E R C.e L
  mca  : C.MCA E C.e C.mca

/-- List size and count of exceptional θ as functions of the radius and of the number of rows, at
the radii with "ok". -/
structure Enc.Prox (C : Enc F) (E : Type) [Field E] [Finite E] [Algebra F E]
    (ok : ℕ → Prop) (L bad : ℕ → ℕ → ℕ) : Prop where
  list : ∀ e, ok e → ∀ (R : Type) [Finite R], C.ListAt E R e (L e (Nat.card R))
  mca  : ∀ e, ok e → ∀ (R : Type) [Finite R], C.MCAat E R e (bad e (Nat.card R))

/-- The same code, with another radius and another count in its data. -/
@[reducible] def Enc.atRadius (C : Enc F) (e bad : ℕ) : Enc F := { C with e := e, mca := bad }

end Code

namespace Cb
open Prob Blocks

namespace Spec
section
variable (F : Type) [Field F] [Fintype F] (E : Type) [Field E] [Finite E] [Algebra F E]

def mca_iff_at : Prop :=
  ∀ (C : Code.Enc F) (e bad : ℕ), C.MCA E e bad ↔ ∀ (R : Type) [Finite R], C.MCAat E R e bad

/-- (a) Unique decoding is the instance L = 1. -/
def listProps_of_props : Prop := ∀ C : Code.Enc F, C.Props E → C.ListProps E 1

/-- Back: `ListProps` with 2 e < d gives `Props`, whatever L. -/
def props_of_listProps : Prop :=
  ∀ (C : Code.Enc F) (L : ℕ), C.ListProps E L → 2 * C.e < C.d → C.Props E

/-- (b) Below the Johnson radius, for a code with `Core`: the list is proved; the agreement at that
radius is a hypothesis. -/
def listProps_of_johnson : Prop :=
  ∀ C : Code.Enc F,
    C.Core → InJohnson C.n C.d C.e → C.MCA E C.e C.mca → C.ListProps E (listMax C.n C.d C.e)

def listProps_mono : Prop :=
  ∀ (C : Code.Enc F) (L L' : ℕ), L ≤ L' → C.ListProps E L → C.ListProps E L'

/-- The list clause cannot be met with L = 0: a codeword is in its own list. -/
def listProps_one_le : Prop := ∀ (C : Code.Enc F) (L : ℕ), C.ListProps E L → 1 ≤ L

/-- At the radius 0 and the count 1 a code with `Core` has all the properties of Code/Iface.lean.
-/
def core_props : Prop := ∀ C : Code.Enc F, C.Core → (C.atRadius 0 1).Props E

/-- Up to a third of the distance (3 e < d), nothing assumed but `HasDist C.G C.d`. -/
def prox_third : Prop :=
  ∀ C : Code.Enc F,
    HasDist C.G C.d → C.Prox E (fun e => 3 * e < C.d) (fun _ _ => 1) (fun e _ => e + 1)

/-- Below the Johnson radius, from `HasDist C.G C.d`: the list is proved, the agreement is a
hypothesis, with a count that may depend on the number of rows. -/
def prox_johnson : Prop :=
  ∀ (C : Code.Enc F) (bad : ℕ → ℕ → ℕ), HasDist C.G C.d →
    (∀ e, InJohnson C.n C.d e → ∀ (R : Type) [Finite R], C.MCAat E R e (bad e (Nat.card R))) →
    C.Prox E (InJohnson C.n C.d) (fun e _ => listMax C.n C.d e) bad

/-- From the functions to the record at one radius e with `ok e`, for a code with `Core`, if the
two numbers bound the functions for every number of rows. -/
def listProps_of_prox : Prop :=
  ∀ (C : Code.Enc F) (ok : ℕ → Prop) (L bad : ℕ → ℕ → ℕ) (e L₀ bad₀ : ℕ), C.Core →
    C.Prox E ok L bad → ok e → (∀ rows, L e rows ≤ L₀) →
    (∀ rows, bad e rows ≤ bad₀) → (C.atRadius e bad₀).ListProps E L₀

end
end Spec
end Cb
