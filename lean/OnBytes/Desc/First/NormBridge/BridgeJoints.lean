--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- OnBytes/Desc/First/NormBridge/BridgeJoints.lean:
A TRIAL OF FLOOR B's JOINTS (BridgeWorld.lean,
BridgeTables.lean): THE TWO SUMCHECKS RUN ON TRUE CLAIMS WHEN THE TRUE SUMS AND PRODUCTS ARE
SENT. Algebra
over a field. Statements and proofs.

Why. A law over the masked sumcheck is empty if its summand or its tables are not the caller's own:
then the
claimed sum is false also for an honest prover, and no honest run meets the premises. Here: with the
true
sums (trueW) the squares' start value (Run.cvS's formula) IS the sum of the squares' table's square
under the
point's equality weights; with the true products (trueP) their batch IS the sum of the products'
summand on
the products' tables. Both hold at EVERY draw and WHATEVER THE DATA.

  joint_squares, joint_products.
NOT CLAIMED: that a run exists which meets floor B's five groups. What is left for that is the
masked
sumcheck's COMPLETENESS on a true claim (an honest prover's rounds as a term, its row worth 0, none
of its
elements bad): no such statement lies with the law that floor B takes.
-/
import OnBytes.Desc.First.NormBridge.BridgeTables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D6.Bridge
open Finset
open Blocks (ext eqN)
open OnBytes.Desc.First.P1 (sumTerms)

variable {K : Type} [Field K] (c : Data K)

/-- With the true sums sent, the squares' sumcheck's claim is true. a: the squares' point; its
middle
lPd coordinates are h; its last lt coordinates are the point over the positions. -/
theorem joint_squares (lPd : ℕ) (hd : c.d ≤ 2 ^ lPd) (hN : c.NI ≤ 2 ^ c.lNI) (gam h : K)
    (hh : 1 - h = h) (a : ℕ → K) (ha : ∀ t < lPd, a (c.lNI + t) = h) :
    h ^ lPd * ∑ i ∈ range c.NI, eqN c.lNI 0 a i * ∑ s ∈ range 9,
        gam ^ s * c.trueW (fun t => a (c.lNI + lPd + t)) (9 * i + s) =
      ext (c.lNI + lPd + c.lt) (fun X => c.sqTab lPd gam X * c.sqTab lPd gam X) a := by
  rw [c.ext_sqTab lPd hd hN gam h hh a ha]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  congr 1
  have e := ext_squares c (fun t => a (c.lNI + lPd + t)) gam i
  have e' : c.sqZ gam (fun t => a (c.lNI + lPd + t)) i =
      ∑ s ∈ range 9, gam ^ s * c.sumWAt (fun t => a (c.lNI + lPd + t)) i s := e
  rw [e']
  refine sum_congr rfl fun s hs => ?_
  have hs' := mem_range.mp hs
  unfold Data.trueW
  rw [show (9 * i + s) / 9 = i by omega, show (9 * i + s) % 9 = s by omega]

/-- With the true products sent, the products' sumcheck's claim is true. -/
theorem joint_products (u : ℕ → K) (om : K) :
    ∑ m ∈ range (7 * c.NI), om ^ m * c.trueP u m =
      ext c.lt (fun X => sumTerms (prTerms c.NI om) fun e => c.field e X) u := by
  have e1 : (fun X => sumTerms (prTerms c.NI om) fun e => c.field e X) =
      fun t => ∑ m ∈ range (7 * c.NI), om ^ m * c.prodR (m / 7) (m % 7) t :=
    funext fun t => sumTerms_field c om t
  rw [e1, ext_products]
  rfl

end D6.Bridge

#print axioms D6.Bridge.joint_squares
#print axioms D6.Bridge.joint_products
