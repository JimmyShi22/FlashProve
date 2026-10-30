-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Prox/BaseChecks.lean: the checks of the last step of a proximity test (the base case),
written out. Johnson/Desc/Prox/BaseCase.lean says what the step is and calls baseChecks.

The letters. w, u: the last committed message's word under the main code C and its word under the
mask code Z. w*, u*: the masking message's two words. c, d, τ: the claim that is left on w and u.
τ*: what the prover says the claim's left side is at w*, u*. λ: the element that the verifier drew.
What is checked. The prover has shown, in the clear, two messages M0, M1 and two random tails R0,
R1: those of w* + λ w and of u* + λ u, if it is honest.
  linearOk    (i) the linear claim:  ⟨c, M0⟩ + ⟨d, M1⟩ = τ* + λ τ.
  symbolsOk   (ii) at one drawn position x: the code word of (M0, R0) under the main code C has at x
              the symbol  w*(x) + λ w(x),  and the code word of (M1, R1) under the mask code Z has,
              at x's place in the shorter word, the symbol  u*(x) + λ u(x).
  baseChecks  the four lengths are the codes'; (i); and (ii) at every drawn position.
What is taken from the format's library (lean/Fmt/): the field's sum and product (FieldE.lean), the
inner product (M1Types.lean), and, of a code, its encoder's symbol at a position and a position's
place in the shorter word (M1Codes.lean: symE, cp).
Where the three come from: they are the bodies of Fmt.M1.baseB1, baseB2At and baseOK
(Fmt/M1Fold.lean) at the field .two; Johnson/Desc/K12/Law/BaseChecksIs.lean holds the equations.
This file imports nothing of Johnson/Desc/, so that a second caller can take it without that cone.
No theorem here. Nothing on soundness.
-/
import Fmt.M1Types

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Prox

/-- **(i) The linear claim**: ⟨c, M0⟩ + ⟨d, M1⟩ = τ* + λ τ. c, d, tau: the claim that is left. tauS:
the prover's τ*. lam: the drawn λ. M0, M1: the two messages shown in the clear. -/
def linearOk (c d : Array Fmt.M1.E) (tau tauS lam : Fmt.M1.E) (M0 M1 : List Fmt.M1.E) : Bool :=
  decide (Fmt.Fld.two.addE (Fmt.M1.dot .two c M0.toArray) (Fmt.M1.dot .two d M1.toArray) =
    Fmt.Fld.two.addE tauS (Fmt.Fld.two.mulE lam tau))

/-- **(ii) The two code words at one drawn position x.** o: the column's four symbols there: w(x),
w*(x), u(x), u*(x): the last message's main symbol, the masking message's main symbol, the last
message's mask symbol, the masking message's mask symbol. The code word of (M0, R0) under C has at
x the symbol w*(x) + λ w(x); the code word of (M1, R1) under Z has, at x's place in the shorter
word, the symbol u*(x) + λ u(x). -/
def symbolsOk (C Z : Fmt.M1.Code) (lam : Fmt.M1.E) (M0 M1 R0 R1 : List Fmt.M1.E) (x : Nat)
    (o : Fmt.M1.E × Fmt.M1.E × Fmt.M1.E × Fmt.M1.E) : Bool :=
  decide (Fmt.M1.symE C x M0 R0 = Fmt.Fld.two.addE o.2.1 (Fmt.Fld.two.mulE lam o.1)) &&
    decide (Fmt.M1.symE Z (Fmt.M1.cp Z x) M1 R1 =
      Fmt.Fld.two.addE o.2.2.2 (Fmt.Fld.two.mulE lam o.2.2.1))

/-- **The base case's checks**: the two messages and the two tails have the codes' lengths; (i); and
(ii) at every drawn position. xs: the drawn positions. col: the opened column at a position; where
a drawn position has no column the answer is no. -/
def baseChecks (C Z : Fmt.M1.Code) (c d : Array Fmt.M1.E) (tau tauS lam : Fmt.M1.E)
    (M0 M1 R0 R1 : List Fmt.M1.E) (xs : List Nat)
    (col : Nat → Option (Fmt.M1.E × Fmt.M1.E × Fmt.M1.E × Fmt.M1.E)) : Bool :=
  decide (M0.length = C.l ∧ M1.length = Z.l ∧ R0.length = C.r ∧ R1.length = Z.r) &&
    linearOk c d tau tauS lam M0 M1 &&
  xs.all fun x =>
    match col x with
    | some o => symbolsOk C Z lam M0 M1 R0 R1 x o
    | none => false

end VerifiableInference.Desc.Prox
