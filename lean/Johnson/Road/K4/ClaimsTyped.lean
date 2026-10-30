-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/ClaimsTyped.lean: THE CLAIMED SUMS OF SIX OF THE SEVEN SUMCHECKS OF THE CHAIN OF A
LAYERS' SUB-PROOF's OWN ROUNDS, AT THE LIBRARY's VALUE (`FullPar.own`, Cb/Pv/Lay/At/OwnW.lean; a
sub-proof that is not the first), WRITTEN OUT: the first component of each stage's `cl`, as a
formula in the parts of the statement that the stage finds. Nine statements, each by unfolding.

  `cl1` (the sums of squares): the sum over the norms, under the equality weights of the join's
    point, of (1/2)^lDd times the sum of the sent scalars under the powers of the drawn element.
  `cl2` (the products of the rows), `cl3` (the terms): the further scalar that was sent.
  `cl5`, `st5_v` (the gated products): the batched sumcheck's end value under the name aH1.
  `cl6`, `st6_v` (the routed experts' gated products): the sum over the layers with experts, under
    the equality weights of the join's point, of the batched sumcheck's end values under the names
    aH2.
  `cl7`, `st7_v` (the merge): the sum over the weight claims, under the powers of the drawn
    element, of the batched sumcheck's end values under the claims' names.

Limits. The typed side alone: nothing here names a program's record.
-/
import Cb.Pv.Lay.At.OwnW

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (lDd)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : FullPar E M X)

/-- The sums of squares. -/
theorem cl1 (y : ((P.XT × (Fin (P.D.nNu * 9) → E)) × E) × (Fin (P.D.lL + 1) → E))
    (r : Fin 0 → E) :
    (P.own.toOwn.tail.s1.cl y r).1 =
      ∑ i : Fin P.D.nNu, Blocks.eqN (P.D.lL + 1) 0 (Blocks.nat y.2) i.val *
        ((2⁻¹ : E) ^ lDd P.D *
          ∑ s : Fin 9, y.1.2 ^ (s : ℕ) * y.1.1.2 (finProdFinEquiv (i, s))) := rfl

/-- The products of the rows. -/
theorem cl2 (x : ((P.own.toOwn.tail.s1.Nx × E) × (Fin P.own.toOwn.tail.nP → E)) × E)
    (r : Fin 1 → E) : (P.own.toOwn.tail.s2.cl x r).1 = r 0 := rfl

/-- The terms. -/
theorem cl3 (b : P.own.toOwn.tail.s2.Nx) (r : Fin 1 → E) :
    (P.own.toOwn.tail.s3.cl b r).1 = r 0 := rfl

/-- The gated products. -/
theorem cl5 (z : P.own.toOwn.tail.s4.Nx) (r : Fin 0 → E) :
    (P.own.toOwn.tail.s5.cl z r).1 = (P.st5 z.2).v := rfl

theorem st5_v (o : P.O4) : (P.st5 o).v = o.vals (.inl (aH1 P.D)) := rfl

/-- The routed experts' gated products. -/
theorem cl6 (y : (P.own.toOwn.tail.s5.Nx × E) × (Fin (P.D.lL - 1) → E)) (r : Fin 0 → E) :
    (P.own.toOwn.tail.s6.cl y r).1 =
      ∑ i : Fin P.D.ne, Blocks.eqN (P.D.lL - 1) 0 (Blocks.nat y.2) i.val *
        (P.st6 y.1.1.1.1.2).v i := rfl

theorem st6_v (o : P.O4) (i : Fin P.D.ne) : (P.st6 o).v i = o.vals (.inl (aH2 P.D i)) := rfl

/-- The merge. -/
theorem cl7 (y : ((P.own.toOwn.tail.s6.Nx × E) × (Fin 0 → E)) × E) (r : Fin 0 → E) :
    (P.own.toOwn.tail.s7.cl y r).1 =
      ∑ a : Fin P.nW, y.2 ^ (a : ℕ) * (P.ip.st7 P.num y.1.1.1.1.1.1.1.1.1.2).v a := rfl

theorem st7_v (o : P.O4) (a : Fin P.nW) :
    (P.ip.st7 P.num o).v a = o.vals (.inr (.inr (P.num a))) := rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.cl1
#print axioms OnBytes.Road.K4.cl2
#print axioms OnBytes.Road.K4.cl3
#print axioms OnBytes.Road.K4.cl5
#print axioms OnBytes.Road.K4.cl6
#print axioms OnBytes.Road.K4.cl7
#print axioms OnBytes.Road.K4.st5_v
#print axioms OnBytes.Road.K4.st6_v
#print axioms OnBytes.Road.K4.st7_v
