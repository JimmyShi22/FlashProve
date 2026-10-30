-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req/ReqSumTerms.lean: from a list of terms to quadratic steps.

A sum of products of any length is written as a straight-line program of steps of degree at most 2
(`Steps`, Cb/Gen/SumSteps.lean), with auxiliary variables for the partial products: the form of the
summand of a sumcheck.
Definitions and statements; the proofs are in Cb/Req/ReqSumTermsProofs.lean. No protocol. Many
statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Why: a family of conditions (Cb/Req/ReqSpec.lean) is a sum of terms, each a coefficient times a
product of numbered atoms.

The steps: the variables 0, .., nc - 1 are the atoms. A term with the atoms a_0, .., a_(k-1), k ≥ 3,
gets k - 2 auxiliary variables, its partial products
      p_0 = a_0 · a_1,   p_1 = p_0 · a_2,   ..,   p_(k-3) = p_(k-4) · a_(k-2),
and enters the last step with the quadratic term coefficient · p_(k-3) · a_(k-1). Auxiliary steps
have no coefficient but 1: which steps there are depends on nc and the lists of atoms alone; only
the last step holds the coefficients.

Main names:
  `stepsOf nc as cs`: the steps: as = the lists of atoms, cs = the coefficients (numbered as the
    terms).
  `Spec.tri_stepsOf`: the steps are triangular (`Steps.Tri`: step l names only variables below nc +
    l) if every atom named is below nc.
  `Spec.out_stepsOf`: the law: if every atom named is below nc, the summand at the atoms' values Y
    is ∑ coefficient · ∏ Y(atom).

Limits: this file says nothing on extensions, points or degrees (Cb/Req/ReqSumFmt.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.SumSteps

set_option autoImplicit false

namespace Cb.Req
open Blocks

/-- the partial products of the variable cur with the atoms of the list but the last, as pairs of
variables: the first product, cur times the first atom, stands at the variable o, the next at o + 1,
and so on -/
def mulUp (o cur : ℕ) : List ℕ → List (ℕ × ℕ)
  | [] => []
  | [_] => []
  | a :: b :: r => (cur, a) :: mulUp (o + 1) o (b :: r)

/-- the two variables whose product is cur times all atoms of the list (the list is not empty; the
variables from o on hold the partial products of `mulUp`) -/
def lastPair (o cur : ℕ) : List ℕ → ℕ × ℕ
  | [] => (cur, cur)
  | [a] => (cur, a)
  | _ :: b :: r => lastPair (o + 1) o (b :: r)

/-- the auxiliary steps of one term, as pairs of variables -/
def termAux (o : ℕ) : List ℕ → List (ℕ × ℕ)
  | [] => []
  | a :: r => mulUp o a r

/-- the auxiliary steps of all terms -/
def auxAll (o : ℕ) : List (List ℕ) → List (ℕ × ℕ)
  | [] => []
  | as :: ts => termAux o as ++ auxAll (o + (termAux o as).length) ts

section
variable {E : Type}

/-- what a term adds to the last step -/
def termLast [Zero E] (o : ℕ) (c : E) : List ℕ → QStep E
  | [] => ⟨c, [], []⟩
  | [a] => ⟨0, [(c, a)], []⟩
  | a :: b :: r => ⟨0, [], [(c, lastPair o a (b :: r))]⟩

/-- the last step; k is the number of the first term of the list -/
def lastStep [Zero E] [Add E] (cs : ℕ → E) (o k : ℕ) : List (List ℕ) → QStep E
  | [] => ⟨0, [], []⟩
  | as :: ts =>
    ⟨(termLast o (cs k) as).c0 + (lastStep cs (o + (termAux o as).length) (k + 1) ts).c0,
      (termLast o (cs k) as).lin ++ (lastStep cs (o + (termAux o as).length) (k + 1) ts).lin,
      (termLast o (cs k) as).quad ++ (lastStep cs (o + (termAux o as).length) (k + 1) ts).quad⟩

/-- The steps of a sum of terms. -/
def stepsOf [Zero E] [One E] [Add E] (nc : ℕ) (as : List (List ℕ)) (cs : ℕ → E) : Steps E where
  nc := nc
  na := (auxAll nc as).length
  step := fun l =>
    if l < (auxAll nc as).length then ⟨0, [], [(1, (auxAll nc as).getD l (0, 0))]⟩
    else lastStep cs nc 0 as

end

/-- the largest number of atoms in a term -/
def maxLen (as : List (List ℕ)) : ℕ := (as.map List.length).foldr max 0

/-- one more than the largest number of an atom that a term names -/
def maxAtom (as : List (List ℕ)) : ℕ := (as.map fun l => (l.map (· + 1)).foldr max 0).foldr max 0

end Cb.Req

namespace Cb.Spec
open Blocks Cb.Req

def tri_stepsOf : Prop :=
  ∀ (E : Type) [CommRing E] (nc : ℕ) (as : List (List ℕ)) (cs : ℕ → E),
    (∀ l ∈ as, ∀ j ∈ l, j < nc) → (stepsOf nc as cs).Tri

/-- The law of the steps. -/
def out_stepsOf : Prop :=
  ∀ (E : Type) [CommRing E] (nc : ℕ) (as : List (List ℕ)) (cs : ℕ → E) (Y : ℕ → E),
    (∀ l ∈ as, ∀ j ∈ l, j < nc) →
    (stepsOf nc as cs).out Y =
      ((List.range as.length).map fun k => cs k * ((as.getD k []).map Y).prod).sum

def lt_maxAtom : Prop := ∀ (as : List (List ℕ)), ∀ l ∈ as, ∀ j ∈ l, j < maxAtom as

def le_maxLen : Prop := ∀ (as : List (List ℕ)), ∀ l ∈ as, l.length ≤ maxLen as

end Cb.Spec
