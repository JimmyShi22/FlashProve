-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/ClaimsTypedFirst.lean: THE CLAIMED SUMS OF SIX OF THE SEVEN SUMCHECKS OF THE CHAIN
OF THE FIRST LAYERS' SUB-PROOF's OWN ROUNDS, AT THE LIBRARY's VALUE (`FullFPar.ownF`,
Cb/Pv/Lay/At/OwnFirstW.lean), WRITTEN OUT: the first component of each stage's `cl`, as a formula in
the parts of the statement that the stage finds. Six statements, each by unfolding. The twin of
Johnson/Road/K4/ClaimsTyped.lean, which treats a sub-proof that is not the first.

  `cl1F`, `cl2F`, `cl3F`, `cl5F`, `cl6F`: the formulas of ClaimsTyped.lean's `cl1` … `cl6`; the
    statement in front holds three points, not one.
  `cl7F` (the merge): the sum over the weight claims, under the powers of the drawn element, of the
    batched sumcheck's end values under the claims' names, AND the next power times the one scalar
    that was sent in the weights' round (the embedding's claim).

Limits. The typed side alone: nothing here names a program's record.
-/
import Cb.Pv.Lay.At.OwnFirstW

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (lDd)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : FullFPar E M X)

/-- The sums of squares. -/
theorem cl1F (y : ((P.ofp.fs.X3 × (Fin (P.D.nNu * 9) → E)) × E) × (Fin (P.D.lL + 1) → E))
    (r : Fin 0 → E) :
    (P.ownF.toOwn.tail.s1.cl y r).1 =
      ∑ i : Fin P.D.nNu, Blocks.eqN (P.D.lL + 1) 0 (Blocks.nat y.2) i.val *
        ((2⁻¹ : E) ^ lDd P.D *
          ∑ s : Fin 9, y.1.2 ^ (s : ℕ) * y.1.1.2 (finProdFinEquiv (i, s))) := rfl

/-- The products of the rows. -/
theorem cl2F (x : ((P.ownF.toOwn.tail.s1.Nx × E) × (Fin P.ownF.toOwn.tail.nP → E)) × E)
    (r : Fin 1 → E) : (P.ownF.toOwn.tail.s2.cl x r).1 = r 0 := rfl

/-- The terms. -/
theorem cl3F (b : P.ownF.toOwn.tail.s2.Nx) (r : Fin 1 → E) :
    (P.ownF.toOwn.tail.s3.cl b r).1 = r 0 := rfl

/-- The gated products. -/
theorem cl5F (z : P.ownF.toOwn.tail.s4.Nx) (r : Fin 0 → E) :
    (P.ownF.toOwn.tail.s5.cl z r).1 = (P.st5 z.2).v := rfl

/-- The routed experts' gated products. -/
theorem cl6F (y : (P.ownF.toOwn.tail.s5.Nx × E) × (Fin (P.D.lL - 1) → E)) (r : Fin 0 → E) :
    (P.ownF.toOwn.tail.s6.cl y r).1 =
      ∑ i : Fin P.D.ne, Blocks.eqN (P.D.lL - 1) 0 (Blocks.nat y.2) i.val *
        (P.st6 y.1.1.1.1.2).v i := rfl

/-- The merge, with the embedding's claim. -/
theorem cl7F (y : ((P.ownF.toOwn.tail.s6.Nx × E) × (Fin 1 → E)) × E) (r : Fin 0 → E) :
    (P.ownF.toOwn.tail.s7.cl y r).1 =
      ∑ a : Fin P.nW, y.2 ^ (a : ℕ) * (P.ip.st7 P.num y.1.1.1.1.1.1.1.1.1.2).v a +
        y.2 ^ P.nW * y.1.2 0 := rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.cl1F
#print axioms OnBytes.Road.K4.cl2F
#print axioms OnBytes.Road.K4.cl3F
#print axioms OnBytes.Road.K4.cl5F
#print axioms OnBytes.Road.K4.cl6F
#print axioms OnBytes.Road.K4.cl7F
