-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Halve.lean: `halved` computes a fold's round polynomials, as
`FoldOwn.honest` (Fmt/M1Fold.lean) does, in another order: each round folds the two large tables
(the claim's coefficients, the main rows) once, at the element that the round sampled, and hands
them to the next round. Definitions only. It imports Run.lean alone; no Mathlib.

  `lightTerm`, `lightAt`   a round polynomial's value at X without the main tables' share: the
                 hiding polynomial's and the mask tables' shares, summed over the cube by the
                 functions of Fmt/ (`hidePoly`, `foldLow`, `dot`, `tailProd`, `cube`)
  `halvedFrom`   the rounds from one round on
  `halved`       the rounds. With more sampled elements than the fold has variables it calls
                 `FoldOwn.honest`
  `Seams.halving`   `Seams` (Run.lean) with `halved` at `Fld.two`, and the originals elsewhere

`halved_eq` (HalveLaw.lean) proves that `halved` and `FoldOwn.honest` return the same list at
`Fld.two`, without hypothesis. Examples: HalveToy.lean.

Cost. `halved` needs about 11 N products where `FoldOwn.honest` needs about 6 (2 ^ k - 1) N, for
main tables of N entries; the mask tables' share costs the same in both. Only the rounds are
computed otherwise: `Trial.sigma`, the tables, the columns and the claim's row are not touched.
Counted by reading the code, not measured.

Limits. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Fmt (Fld)
open Fmt.M1 (E dot fold1 foldLow tailProd csOwnG)
open Fmt.M1.FoldOwn (Trial hidePoly cube coeffs honest)

/-- `sumPoly` (Fmt/M1Fold.lean) at a point, without the main tables' share. -/
def lightTerm (f : Fld) (T : Trial) (xs : List E) : E :=
  f.addE (hidePoly f T.k T.U xs)
    (f.mulE T.eps
      (f.mulE (dot f (foldLow f (xs.take T.h) T.G.d) (foldLow f (xs.take T.h) T.mu))
        (tailProd f (xs.take T.k) T.h)))

/-- A round polynomial's value at X without the main tables' share: `roundAt` (Fmt/M1Fold.lean) with
`lightTerm` in the place of `sumPoly`. before: the elements sampled so far. -/
def lightAt (f : Fld) (T : Trial) (before : List E) (X : E) : E :=
  (cube (T.k - before.length - 1)).foldl
    (fun s p => f.addE s (lightTerm f T (before ++ X :: p))) Fld.zeroE

/-- **The rounds from one round on.** The first list: the elements sampled so far. c, m: the two
large tables folded at them. The last list: the elements still to come. -/
def halvedFrom (f : Fld) (T : Trial) : List E → Array E → Array E → List E → List ((E × E) × E)
  | _, _, _, [] => []
  | before, c, m, g :: gs =>
    let v (X : E) : E :=
      f.addE (lightAt f T before X) (f.mulE T.eps (dot f (fold1 f X c) (fold1 f X m)))
    let q := coeffs f (v Fld.zeroE) (v Fld.oneE) (v (f.negE Fld.oneE))
    ((q.1, q.2.2), q.2.1) :: halvedFrom f T (before ++ [g]) (fold1 f g c) (fold1 f g m) gs

/-- **The rounds.** Equal to `honest f T [] g` at `Fld.two` (`halved_eq`, HalveLaw.lean). -/
def halved (f : Fld) (T : Trial) (g : List E) : List ((E × E) × E) :=
  if g.length ≤ T.k then halvedFrom f T [] T.G.c T.m g else honest f T [] g

/-- `Seams` with `halved` at `Fld.two`. -/
def Seams.halving : Seams :=
  ⟨fun f T g =>
    match f with
    | .two => halved .two T g
    | .one => honest .one T [] g, csOwnG, Fmt.M1.Own.tabOf,
    fun next last Q => (next.C.a, Fmt.M1.Own.colOf next false last Q), denseAt⟩

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.lightTerm
#print axioms ProofFile.Honest.K12.Light.lightAt
#print axioms ProofFile.Honest.K12.Light.halvedFrom
#print axioms ProofFile.Honest.K12.Light.halved
#print axioms ProofFile.Honest.K12.Light.Seams.halving
