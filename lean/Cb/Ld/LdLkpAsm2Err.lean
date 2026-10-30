-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpAsm2Err.lean: the error of each round of a lookup argument, as a count, beside the number
of values of that round's verifier message; the number of rounds in closed form.

The assembled lookup (`LkAsm2`, Cb/Ld/LdLkpAsm2.lean) is a lookup argument by products (2^v keys, a
table of 2^d entries, multiplicities in bits) as one chain of reductions; that file's head tells its
rounds in order. Definitions and statements (each a `Prop` in `Cb.Spec`); the proofs are in
Cb/Ld/LdLkpAsm2ErrProofs.lean. An error is a count of exceptional values of the round's verifier
message; the fraction is count / number of values. q: the number of elements of E; 2^w bit positions
of which the first W = n + 1 count; v = v' + 1; κ = w + d. (In `pscErrs k n D` and `coreErrs k n`
the letter n is an argument of its own, not `A.n`.)

Main names:
  `pscErrs k n D`, `pscVals q k`: one sumcheck with k variables and a further variable
    (Cb/Ld/LdLkpAsmErr.lean): errors 1, n (k times), D, 0; numbers of values q, q (k times), q - 1,
    1.
  `coreErrs k n`, `coreVals q k`: one sumcheck with k variables, where no map is revealed
    (`PscPar.core`, Cb/Ld/LdPsc.lean): errors 1, n (k times); numbers of values q, q (k times).
  `A.errs q`: λ: 2^v - 1 | the tie, n + 1 sumchecks: (1, 1, 0) | (1, 3, 0), W - 1 times | the point
    for the table's products: w q^(w-1) | keys: for l < v: (1, 2 (l times), 2, 0), 1 | table: for l
    < d: (1, 2 (w + l times), 2, 0), 1 | the table's factor: 1, 2 (κ times) | the bit test:
    zerocheck point: κ q^(κ-1) | one sumcheck: 1, 2 (κ times), 2, 0.
  As fractions: (2^v - 1)/q | 1/q, 1/(q-1), 0 | (1/q, 3/(q-1), 0)^(W-1) | w/q | .. | 1/q, (2/q)^κ |
    κ/q | 1/q, (2/q)^κ, 2/(q-1), 0: the list of a write-up of ours (lean/CREDITS.md), entry
    for entry (by reading, not machine-checked).
  `A.vals q`; `Spec.ldLkpAsm2E_errs`, `Spec.ldLkpAsm2E_vals`, `Spec.ldLkpAsm2E_sub` (`A.baseN`,
    `A.subN`, `A.subIN`: Cb/Ld/LdLkpAsm2Pull.lean).
  `Spec.ldLkpAsm2E_len`: both lists have as many entries as there are rounds: the sum of
    `Spec.ldLkpAsm2_rounds` (Cb/Ld/LdLkpAsm2.lean), written out.
  `Spec.ldLkpAsm2E_closed`: the number of rounds in closed form: 3 W + 7 + 4 v + C(v, 2) + (w + 6) d
    + C(d, 2) + 2 w.
  `Spec.ldLkpAsm2E_last`, `Spec.ldLkpAsm2E_small`: the rounds in which the verifier sends nothing
    (one value); every error is below its number of values; each under the conditions that its doc
    comment tells.

Why w > 0 in `Spec.ldLkpAsm2E_last` is no narrowing: the conditions on numbers (`LkB.Adm`,
Cb/Ld/LdLkp.lean) give w > 0: 2^v < 2^W makes W at least 2, and W ≤ 2^w.

Limits: this file does not say the number of own masks: Cb/Ld/LdLkpMaskPlaces2.lean
(`ldLkpPlaces2_card`). The number of scalars sent is said nowhere in Cb/Ld/ (in our format a round
polynomial is sent with one coefficient more than it has masks). This file says nothing on a sum of
the fractions.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdLkpAsm2Pull
import Cb.Ld.LdLkpAsmErr

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob

/-- the errors of one sumcheck where no map is revealed (`PscPar.core`, Cb/Ld/LdPsc.lean); the
numbers of values beside them -/
def coreErrs (k n : ℕ) : List ℕ := 1 :: List.replicate k n
def coreVals (q k : ℕ) : List ℕ := q :: List.replicate k q

namespace LkAsm2
variable {E : Type} [Field E] [Fintype E] (A : LkAsm2 E)

/-- The errors, in the order of the rounds. -/
def errs (q : ℕ) : List ℕ :=
  (((([2 ^ (A.v' + 1) - 1] ++ (pscErrs 0 2 1 ++ (List.range A.n).flatMap fun _ => pscErrs 0 2 3)) ++
          [A.w * q ^ (A.w - 1)]) ++
        (((List.range (A.v' + 1)).flatMap fun l => pscErrs (0 + l) 2 2 ++ [1]) ++
          (List.range A.d).flatMap fun l => pscErrs (A.w + l) 2 2 ++ [1])) ++
      coreErrs (A.w + A.d) 2) ++
    ([(A.w + A.d) * q ^ (A.w + A.d - 1)] ++ pscErrs (A.w + A.d) 2 2)

/-- The numbers of values of the verifier messages, in the same order. -/
def vals (q : ℕ) : List ℕ :=
  (((([q] ++ (pscVals q 0 ++ (List.range A.n).flatMap fun _ => pscVals q 0)) ++ [q ^ A.w]) ++
        (((List.range (A.v' + 1)).flatMap fun l => pscVals q (0 + l) ++ [q]) ++
          (List.range A.d).flatMap fun l => pscVals q (A.w + l) ++ [q])) ++
      coreVals q (A.w + A.d)) ++
    ([q ^ (A.w + A.d)] ++ pscVals q (A.w + A.d))

end LkAsm2
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp

section
variable (E : Type) [Field E] [Fintype E]

/-- States that `A.errs` at the number of elements of E is the list of errors of `A.baseN`. -/
def ldLkpAsm2E_errs : Prop :=
  ∀ (A : LkAsm2 E) (N : Type) (ι : N → A.J) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E),
    (A.baseN ι Ex M Wp Kc msg).P.err.toList = A.errs (Fintype.card E)

/-- States that `A.vals` at the number of elements of E is the list of the numbers of values of the
verifier messages of `A.baseN`. -/
def ldLkpAsm2E_vals : Prop :=
  ∀ (A : LkAsm2 E) (N : Type) (ι : N → A.J) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E),
    (A.baseN ι Ex M Wp Kc msg).R.shape.chalList = A.vals (Fintype.card E)

/-- Over a signature, and with an encoded index: the same lists. -/
def ldLkpAsm2E_sub : Prop :=
  (∀ (A : LkAsm2 E) (N : Type) (ι : N → A.J) (S : Sig E) (E₀ : ExtSpec)
        (Kc Wp : Type) (msg : S.Msg → A.J → E),
      (A.subN ι S E₀ Kc Wp msg).P.err.toList = A.errs (Fintype.card E) ∧
      (A.subN ι S E₀ Kc Wp msg).R.shape.chalList = A.vals (Fintype.card E)) ∧
  ∀ (A : LkAsm2 E) (N : Type) (ι : N → A.J) (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (msg : C.Msg × S.Msg → A.J → E),
    (A.subIN ι C S msg).P.err.toList = A.errs (Fintype.card E) ∧
    (A.subIN ι C S msg).R.shape.chalList = A.vals (Fintype.card E)

def ldLkpAsm2E_len : Prop :=
  ∀ (A : LkAsm2 E) (q : ℕ),
    (A.errs q).length = (A.vals q).length ∧
    (A.errs q).length =
      (1 + 3 * (A.n + 1)) + 1 +
        ((∑ l ∈ Finset.range (A.v' + 1), (0 + l + 3 + 1)) +
          ∑ l ∈ Finset.range A.d, (A.w + l + 3 + 1)) +
        (A.w + A.d + 1) + (1 + (A.w + A.d + 3))

/-- The number of rounds in closed form. -/
def ldLkpAsm2E_closed : Prop :=
  ∀ (A : LkAsm2 E) (q : ℕ), (A.errs q).length =
    3 * (A.n + 1) + 7 + 4 * (A.v' + 1) + (A.v' + 1).choose 2 +
      (A.w + 6) * A.d + A.d.choose 2 + 2 * A.w

/-- The rounds in which the verifier sends nothing (one value). States, if q > 2 and w > 0, that
they are W + v + d + 1. -/
def ldLkpAsm2E_last : Prop :=
  ∀ (A : LkAsm2 E) (q : ℕ), 2 < q → 0 < A.w → (A.vals q).count 1 = (A.n + 1) + (A.v' + 1) + A.d + 1

/-- States, if 2^v ≤ q, 5 ≤ q, κ < q (q the number of elements of E): every error is below its
number of values. -/
def ldLkpAsm2E_small : Prop :=
  ∀ (A : LkAsm2 E) (N : Type) (ι : N → A.J) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E),
    2 ^ (A.v' + 1) ≤ Fintype.card E → 5 ≤ Fintype.card E →
    A.w + A.d < Fintype.card E → (A.baseN ι Ex M Wp Kc msg).P.err.Small

end
end Cb.Spec
