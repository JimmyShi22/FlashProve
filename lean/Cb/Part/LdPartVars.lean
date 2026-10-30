-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartVars.lean: cube variables of a sumcheck, each with a degree and a form of its own;
points read as functions on the variables.

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Part/LdPartVarsProofs.lean. No
protocol.
This file is book-keeping for sumchecks over a Boolean cube in which each variable has its own
bound on the degree and its own weights of summation.
A variable of Cb/Ld/LdPsc.lean is a format (`PFmt`: degree, names of nodes, challenge set) and data
(`PDat`: nodes and weights of the functional "sum over the variable", and ψ).

Why: the sumchecks that are built from a family of conditions (Cb/Part/LdPartPsc.lean,
Cb/Part/LdPartPscFam.lean) run over the variables of a cube. By this protocol's technical report
(lean/CREDITS.md) a claim on the value, at a point z, of a map that is given by an inner sum is a
sum over all variables: the outer ones under the equality form at z's coordinate (the value at 1
with the weight z, the value at 0 with the weight 1 - z), the inner ones under the plain form (both
values with the weight 1).
The form stands in the functional on the round polynomial, not in the summand: it adds no degree.
And the degree of a summand is counted variable by variable. Cb/Ld/LdPscVars.lean has lists of k
variables of one kind and one degree; here each variable has its own.

Main names:
  `ldPartDat E k n w`: the data. w i = some z: the equality form at z (ψ = 1); w i = none: the
    plain form (ψ = X; needs 1 ≤ n i).
  `Spec.ldPartVars_ok`, `Spec.ldPartVars_sum`, `Spec.ldPartVars_deg`: see their docstrings.

Limits: this file says nothing on a protocol. Whether a variable is plain or weighted may here
depend on whatever w depends on; that it is a public parameter is a matter of the file that fills
w. The technical report allows to replace an outer variable by the point's coordinate where the
summand has degree at most 1 in it: not rendered here (such a variable is simply no variable of the
list).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdPscVars

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

noncomputable section

section
variable (E : Type) [Field E] [Fintype E]

/-- The formats: k cube variables, the i-th with round polynomials of degree at most n i; challenges
from all of E. -/
def ldPartFmt : (k : ℕ) → (Fin k → ℕ) → List (PFmt E)
  | 0, _ => []
  | k + 1, n => pfCube E (n 0) :: ldPartFmt k fun i => n i.succ

/-- the data of one variable: the plain form, or the equality form at z -/
def ldPartDat1 (n : ℕ) : Option E → PDat E (pfCube E n)
  | none => pdPlain E n
  | some z => pdEq E n z

/-- The data: a form for each variable. -/
def ldPartDat : (k : ℕ) → (n : Fin k → ℕ) → (Fin k → Option E) → PDats (ldPartFmt E k n)
  | 0, _, _ => ()
  | k + 1, n, w => (ldPartDat1 E (n 0) (w 0), ldPartDat k (fun i => n i.succ) fun i => w i.succ)

end

section
variable {E : Type} [Field E] [Fintype E]

/-- The weight of a form at a coordinate of a corner. -/
def ldPartWt : Option E → Bool → E
  | none, _ => 1
  | some z, b => if b then z else 1 - z

/-- A point as a function on the variables, and a function as a point without data. -/
def ldPartFn :
    (k : ℕ) → (n : Fin k → ℕ) → (d : PDats (ldPartFmt E k n)) →
    HPt (pVars (ldPartFmt E k n) d) → Fin k → E
  | 0, _, _, _ => Fin.elim0
  | k + 1, n, d, X => Fin.cons X.1 (ldPartFn k (fun i => n i.succ) d.2 X.2)
def ldPartPP : (k : ℕ) → (n : Fin k → ℕ) → (Fin k → E) → PPt (ldPartFmt E k n)
  | 0, _, _ => ()
  | k + 1, n, x => (x 0, ldPartPP k (fun i => n i.succ) fun i => x i.succ)

/-- A point with one more coordinate at the end (the verifier's point after a sumcheck with a dummy
last variable): its first k coordinates as a function; its last coordinate. -/
def ldPartIni : (k : ℕ) → (n : Fin k → ℕ) → (g : PFmt E) → PPt (ldPartFmt E k n ++ [g]) → Fin k → E
  | 0, _, _, _ => Fin.elim0
  | k + 1, n, g, γ => Fin.cons γ.1 (ldPartIni k (fun i => n i.succ) g γ.2)
def ldPartLast : (k : ℕ) → (n : Fin k → ℕ) → (g : PFmt E) → PPt (ldPartFmt E k n ++ [g]) → E
  | 0, _, _, γ => γ.1
  | k + 1, n, g, γ => ldPartLast k (fun i => n i.succ) g γ.2

end

namespace Spec
section
variable (E : Type) [Field E] [Fintype E]

/-- Every variable meets the one condition on a variable, (sum of ψ) = 1, if the plain ones have a
degree of at least 1. -/
def ldPartVars_ok : Prop :=
  ∀ (k : ℕ) (n : Fin k → ℕ) (w : Fin k → Option E),
    (∀ i, w i = none → 1 ≤ n i) → ∀ v ∈ pVars (ldPartFmt E k n) (ldPartDat E k n w), v.OK

/-- Different challenges have different values. -/
def ldPartVars_inj : Prop :=
  ∀ (k : ℕ) (n : Fin k → ℕ), ∀ f ∈ ldPartFmt E k n, Function.Injective f.val

/-- The sum over all variables is the weighted sum over the corners. -/
def ldPartVars_sum : Prop :=
  ∀ (k : ℕ) (n : Fin k → ℕ) (w : Fin k → Option E)
      (f : HPt (pVars (ldPartFmt E k n) (ldPartDat E k n w)) → E),
    hSumAll (pVars (ldPartFmt E k n) (ldPartDat E k n w)) f =
      ∑ b : Fin k → Bool,
        (∏ i, ldPartWt (w i) (b i)) * f (pH _ (ldPartDat E k n w) (ldPartPP k n (Alg.corner b)))

/-- `ldPartFn` after `pH` after `ldPartPP` is the identity, whatever the data. -/
def ldPartVars_fn : Prop :=
  ∀ (k : ℕ) (n : Fin k → ℕ) (d : PDats (ldPartFmt E k n)) (x : Fin k → E),
    ldPartFn k n d (pH _ d (ldPartPP k n x)) = x

/-- A function of k coordinates with degree at most n i in the i-th (`Alg.DegLE`) has the degrees of
the variables (`HDeg`), whatever the data. -/
def ldPartVars_deg : Prop :=
  ∀ (k : ℕ) (n : Fin k → ℕ) (d : PDats (ldPartFmt E k n)) (g : (Fin k → E) → E),
    Alg.DegLE n g → HDeg (pVars (ldPartFmt E k n) d) fun X => g (ldPartFn k n d X)

/-- The readers of a point with one more coordinate are `hInit`, `hLast` of Cb/Ld/LdPsc.lean, read
as functions. -/
def ldPartVars_ini : Prop :=
  ∀ (k : ℕ) (n : Fin k → ℕ) (d : PDats (ldPartFmt E k n)) (g : PFmt E)
      (e : PDat E g) (γ : PPt (ldPartFmt E k n ++ [g])),
    ldPartFn k n d (hInit _ d g e (pH _ (PDats.snoc _ d g e) γ)) = ldPartIni k n g γ
def ldPartVars_last : Prop :=
  ∀ (k : ℕ) (n : Fin k → ℕ) (d : PDats (ldPartFmt E k n)) (g : PFmt E)
      (e : PDat E g) (γ : PPt (ldPartFmt E k n ++ [g])),
    hLast _ d g e (pH _ (PDats.snoc _ d g e) γ) = ldPartLast k n g γ

/-- k formats, with the degrees n. -/
def ldPartVars_len : Prop := ∀ (k : ℕ) (n : Fin k → ℕ), (ldPartFmt E k n).length = k
def ldPartVars_degs : Prop := ∀ (k : ℕ) (n : Fin k → ℕ), (ldPartFmt E k n).map PFmt.n = List.ofFn n

end
end Spec
end
end Cb
