-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/HalveW.lean: `halvedW` computes a fold's round polynomials at
`Fld.two` as `halved` (Halve.lean) does, with the five operations on elements computed on 64-bit
words alone (FldW.lean). Definitions only. Imports Halve.lean and FldW.lean, and no Mathlib.

Each definition repeats a text that stands, at `Fld.two`, with `addEW`, `subEW`, `negEW` and `mulEW`
in the place of `f.addE`, `f.subE`, `f.negE`, and of `f.mulE` and `f.mulEF`:
- `dotLW`, `dotW`, `fold1AW`, `fold1LW`, `fold1W`, `foldLowW` repeat `dotL`, `dot`, `fold1A`,
  `fold1L`, `fold1`, `foldLow` (Fmt/M1Types.lean).
- `tailProdW`, `hidePolyW`, `coeffsW` repeat `tailProd`, `hidePoly`, `coeffs` (Fmt/M1Fold.lean).
- `lightTermW`, `lightAtW`, `halvedFromW`, `halvedW` repeat `lightTerm`, `lightAt`, `halvedFrom`,
  `halved` (Halve.lean).
HalveWLaw.lean proves each equal to its original at `Fld.two`, as functions, for all arguments, also
for words that are not below the prime, and without hypothesis. Examples: HalveWToy.lean.

Not repeated. `cube` has no arithmetic. With more sampled elements than the fold has variables
`halvedW` calls `FoldOwn.honest`, as `halved` does.

Limits. A second text, for speed. CsW.lean calls `foldLowW`; `Seams.fast` (FastW.lean) calls
`halvedW`. Theorems on a run are stated at the originals and are carried over by the equations. It
computes with random values too (a hiding polynomial's coefficients, which `hidePolyW` reads by
their names as `hidePoly` does, and mask tables) and keeps its originals' defaults, without a
warning: `hidePolyW` reads a missing coordinate of the point as 0, `fold1AW` folds a lone last entry
against 0, and `dotLW` stops at the shorter list. In `coeffsW` the inverse of 2 is still computed by
`Fld.invE` of Fmt/FieldE.lean, which is none of the five: once in a round. At `Fld.two` only.
Nothing is measured here. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Halve
import Johnson.Desc.ProofFile.Honest.K12.FldW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Fmt (Fld)
open Fmt.M1 (E)
open Fmt.M1.FoldOwn (Trial Hide cube honest)

/-! ## 1 Tables -/

/-- `dotL` on 64-bit words alone: acc plus the sum of the products, entry by entry. -/
def dotLW : List E → List E → E → E
  | a :: u, b :: v, acc => dotLW u v (addEW acc (mulEW a b))
  | _, _, acc => acc

/-- `dot` on 64-bit words alone. -/
def dotW (u v : Array E) : E := dotLW u.toList v.toList Fld.zeroE

/-- `fold1A` on 64-bit words alone. One variable: new entry i = (1 - g) T[2 i] + g T[2 i + 1]. -/
def fold1AW (g : E) : List E → List E → List E
  | a :: b :: T, acc => fold1AW g T (addEW a (mulEW g (subEW b a)) :: acc)
  | [a], acc => (addEW a (mulEW g (subEW Fld.zeroE a)) :: acc).reverse
  | [], acc => acc.reverse

/-- `fold1L` on 64-bit words alone. -/
def fold1LW (g : E) (T : List E) : List E := fold1AW g T []

/-- `fold1` on 64-bit words alone. -/
def fold1W (g : E) (T : Array E) : Array E := (fold1LW g T.toList).toArray

/-- `foldLow` on 64-bit words alone: a table of 2 ^ |g| rows folded at g. -/
def foldLowW (g : List E) (T : Array E) : Array E :=
  (g.foldl (fun T x => fold1LW x T) T.toList).toArray

/-! ## 2 The hiding polynomial; three coefficients from three values -/

/-- `tailProd` on 64-bit words alone: the product of g_j over j > l (variables counted from 1). -/
def tailProdW (g : List E) (l : Nat) : E := (g.drop l).foldl (fun s a => mulEW s a) Fld.oneE

/-- `hidePoly` on 64-bit words alone: the hiding polynomial at a point. -/
def hidePolyW (k : Nat) (U : Hide) (xs : List E) : E :=
  (List.range k).foldl (fun s i =>
    let x := xs.getD i Fld.zeroE
    addEW s (mulEW (addEW (mulEW (U.w (i + 1) 1) x) (mulEW (U.w (i + 1) 2) (mulEW x x)))
      (tailProdW (xs.take k) (i + 1)))) U.w0

/-- `coeffs` on 64-bit words alone: the three coefficients of a polynomial of degree 2 from its
values at 0, 1 and -1. -/
def coeffsW (v0 v1 vm : E) : E × E × E :=
  let q2 := subEW (mulEW (Fld.two.invE (addEW Fld.oneE Fld.oneE)) (addEW v1 vm)) v0
  (v0, subEW (subEW v1 v0) q2, q2)

/-! ## 3 The rounds -/

/-- `lightTerm` on 64-bit words alone. -/
def lightTermW (T : Trial) (xs : List E) : E :=
  addEW (hidePolyW T.k T.U xs)
    (mulEW T.eps
      (mulEW (dotW (foldLowW (xs.take T.h) T.G.d) (foldLowW (xs.take T.h) T.mu))
        (tailProdW (xs.take T.k) T.h)))

/-- `lightAt` on 64-bit words alone. -/
def lightAtW (T : Trial) (before : List E) (X : E) : E :=
  (cube (T.k - before.length - 1)).foldl
    (fun s p => addEW s (lightTermW T (before ++ X :: p))) Fld.zeroE

/-- `halvedFrom` on 64-bit words alone: the rounds from one round on. -/
def halvedFromW (T : Trial) : List E → Array E → Array E → List E → List ((E × E) × E)
  | _, _, _, [] => []
  | before, c, m, g :: gs =>
    let v (X : E) : E :=
      addEW (lightAtW T before X) (mulEW T.eps (dotW (fold1W X c) (fold1W X m)))
    let q := coeffsW (v Fld.zeroE) (v Fld.oneE) (v (negEW Fld.oneE))
    ((q.1, q.2.2), q.2.1) :: halvedFromW T (before ++ [g]) (fold1W g c) (fold1W g m) gs

/-- **The rounds, on 64-bit words alone.** Equal to `halved .two` (`halvedW_eq`, HalveWLaw.lean). -/
def halvedW (T : Trial) (g : List E) : List ((E × E) × E) :=
  if g.length ≤ T.k then halvedFromW T [] T.G.c T.m g else honest .two T [] g

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.dotLW
#print axioms ProofFile.Honest.K12.Light.dotW
#print axioms ProofFile.Honest.K12.Light.fold1AW
#print axioms ProofFile.Honest.K12.Light.fold1LW
#print axioms ProofFile.Honest.K12.Light.fold1W
#print axioms ProofFile.Honest.K12.Light.foldLowW
#print axioms ProofFile.Honest.K12.Light.tailProdW
#print axioms ProofFile.Honest.K12.Light.hidePolyW
#print axioms ProofFile.Honest.K12.Light.coeffsW
#print axioms ProofFile.Honest.K12.Light.lightTermW
#print axioms ProofFile.Honest.K12.Light.lightAtW
#print axioms ProofFile.Honest.K12.Light.halvedFromW
#print axioms ProofFile.Honest.K12.Light.halvedW
