--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/Moves.lean: THE HONEST PROVER's SCALARS IN A MASKED SUMCHECK, WITH CODE,
over any commutative ring: plain weights (a polynomial is summed at 0 and 1), round polynomials of
degree 2, no value shown at the end. DEFINITIONS ALONE: this file defines part of the honest prover;
what is proved of it stands in Code.lean, SumLaw.lean, Tables.lean and CodeRow.lean of this folder.
Of Mathlib the definitions use the ring's operations and `Fin.cons`, and nothing else.

The sumcheck. There are n variables. The hiding polynomial is U(X) = the sum over l of w_l(X_l)
times the product of X_j over j above l; w_l has a coefficient of X and one of X^2, and the last
variable's also a constant. THE ORDER of its 2 n + 1 coefficients, which are handed in as a function
u of their number: variable by variable, degree upwards: for each variable but the last its X, then
its X^2; for the last variable its constant, then its X, then its X^2. That is the order of the
verifier's walk (`Psc.hidingWalk`, OnBytes/Iop/Psc.lean; shown in CodeRow.lean: `walk_uAt`). The
polynomial of the sumcheck is U + eps (s X_1 .. X_n + the summand), with s the value of the claim's
incoming mask form. At n = 0 there is no variable and U counts as 0; the verifier asks for a
variable.

What is sent: the sum of U over the cube; then in each round the constant and the quadratic
coefficient of the round's polynomial. The term s X_1 .. X_n adds to the linear coefficients alone,
which are not sent: no function here is handed s.

The summand, in two forms. As a parameter (`sentL`): q, from the challenges heard so far to the
three coefficients of the summand's polynomial of the next round. As tables (`sent`): for each row j
two tables of 2^n entries, A_j and B_j; the summand is the sum over j of A_j B_j, entry by entry, as
multilinear extensions; an entry's number has the first variable as its lowest bit (the library's
`Alg.num` has it as the highest).
Main names:
  `tailU u n i`: the sum over the cube of U's part in the n variables whose coefficients begin at
    number i. `sumU u n`: **what is sent first.**
  `sentL u eps q n i seen gs`: **what is sent in the rounds**, the summand a parameter.
  `foldT g T`: a table with its first variable set to g. `quadT A B`: the three coefficients of a
    round, of two tables. `foldAll`, `quadAll`: the same over the rows.
  `sent u eps n i S gs`: **what is sent in the rounds**, the summand given by tables.
  `eqT z`: the table of the equality vector at the point z. `scaleT c T`: every entry times c.
  `weave A B`, `tabOf k f`: the table of a vector on the cube.

Which prover. The one with code; the kind's statements on an honest prover speak of it. The library
has an honest prover of the same sumcheck without code (`TWhole.shortHonC`, Cb/G6/Core.lean), which
picks a round's coefficients by choice, and an account of the sent scalars as polynomials, also
without code (`sentOf`, Johnson/Desc/Part/MaskedSumHonest.lean). That these send the same is not
shown.

What is not claimed. No theorem stands in this file. That `sumU` is the sum of U over the cube is
said by `tailU`'s recursion alone. The functions take all challenges at once; that a round's scalars
read the earlier ones alone: `sentL_take`, `sent_take` (SumLaw.lean). Nothing on running times.
Nothing on soundness or on hiding.

-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest

variable {K : Type} [CommRing K]

/-! ## The hiding polynomial -/

/-- The sum over the cube of the part of U in n variables, whose coefficients begin at number i. -/
def tailU (u : ℕ → K) : ℕ → ℕ → K
  | 0, _ => 0
  | 1, i => 2 * u i + u (i + 1) + u (i + 2)
  | n + 2, i => u i + u (i + 1) + 2 * tailU u (n + 1) (i + 2)

/-- What is sent first: the sum of the hiding polynomial. -/
def sumU (u : ℕ → K) (n : ℕ) : K := tailU u n 0

/-! ## The rounds, the summand a parameter -/

/-- **What is sent in the rounds of n variables**, for each the constant and the quadratic
coefficient. i: the number of the first coefficient of the hiding polynomial's part in these
variables. seen: the challenges heard so far. gs: those to come; the last one is not read. -/
def sentL (u : ℕ → K) (eps : K) (q : List K → K × K × K) :
    ℕ → ℕ → List K → List K → List (K × K)
  | 0, _, _, _ => []
  | 1, i, seen, _ =>
    let c := q seen
    [(u i + eps * c.1, u (i + 2) + eps * c.2.2)]
  | n + 2, i, seen, gs =>
    let c := q seen
    (tailU u (n + 1) (i + 2) + eps * c.1, u (i + 1) + eps * c.2.2) ::
      sentL u eps q (n + 1) (i + 2) (seen ++ [gs.headD 0]) gs.tail

/-! ## The rounds, the summand given by tables -/

/-- A table with its first variable set to g: entries 2 e and 2 e + 1 become one. -/
def foldT (g : K) : List K → List K
  | a :: b :: l => (a + g * (b - a)) :: foldT g l
  | _ => []

/-- The coefficients of 1, X, X^2 of the sum of the products, entry by entry, of two tables whose
first variable is set to X. -/
def quadT : List K → List K → K × K × K
  | a0 :: a1 :: A, b0 :: b1 :: B =>
    let r := quadT A B
    (a0 * b0 + r.1, a0 * (b1 - b0) + (a1 - a0) * b0 + r.2.1, (a1 - a0) * (b1 - b0) + r.2.2)
  | _, _ => (0, 0, 0)

/-- The rows' tables with the first variable set. -/
def foldAll (g : K) (S : List (List K × List K)) : List (List K × List K) :=
  S.map fun p => (foldT g p.1, foldT g p.2)

/-- The three coefficients of a round, over the rows. -/
def quadAll : List (List K × List K) → K × K × K
  | [] => (0, 0, 0)
  | p :: S =>
    let a := quadT p.1 p.2
    let r := quadAll S
    (a.1 + r.1, a.2.1 + r.2.1, a.2.2 + r.2.2)

/-- **What is sent in the rounds of n variables**: for each the constant and the quadratic
coefficient. gs: the challenges; the last one is not read. -/
def sent (u : ℕ → K) (eps : K) : ℕ → ℕ → List (List K × List K) → List K → List (K × K)
  | 0, _, _, _ => []
  | 1, i, S, _ =>
    let c := quadAll S
    [(u i + eps * c.1, u (i + 2) + eps * c.2.2)]
  | n + 2, i, S, gs =>
    let c := quadAll S
    (tailU u (n + 1) (i + 2) + eps * c.1, u (i + 1) + eps * c.2.2) ::
      sent u eps (n + 1) (i + 2) (foldAll (gs.headD 0) S) gs.tail

/-! ## Tables -/

/-- The table of the equality vector at a point: the first coordinate is the lowest bit. -/
def eqT : List K → List K
  | [] => [1]
  | z :: zs => (eqT zs).flatMap fun v => [v * (1 - z), v * z]

/-- Every entry times c. -/
def scaleT (c : K) (T : List K) : List K := T.map fun v => c * v

/-- The entries of two lists in turn, as far as the shorter goes. -/
def weave {K : Type} : List K → List K → List K
  | a :: A, b :: B => a :: b :: weave A B
  | _, _ => []

/-- **The table of a vector on the cube**: the first variable is the lowest bit. -/
def tabOf {K : Type} : (k : ℕ) → ((Fin k → Bool) → K) → List K
  | 0, f => [f fun i => i.elim0]
  | k + 1, f => weave (tabOf k fun b => f (Fin.cons false b)) (tabOf k fun b => f (Fin.cons true b))

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.sumU
#print axioms VerifiableInference.Desc.K13.Honest.sentL
#print axioms VerifiableInference.Desc.K13.Honest.sent
#print axioms VerifiableInference.Desc.K13.Honest.eqT
#print axioms VerifiableInference.Desc.K13.Honest.tabOf
