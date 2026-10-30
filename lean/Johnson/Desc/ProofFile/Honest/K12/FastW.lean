-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FastW.lean: `Seams.fast`, the five functions that `runBy`
(RunBy.lean) takes as parameters (`Seams`, Run.lean), each in a version meant to be faster. One
definition. It imports Fast.lean, HalveW.lean, CsW.lean, ColW.lean and FastDense.lean; no Mathlib.

  `Seams.fast`   a fold's rounds by `halvedW` (HalveW.lean), a code switch's two tables by `csW`
                 (CsW.lean), rows as one table by `tabFast` (Fast.lean), the tree that a switch
                 sends by `colTreeW` (ColW.lean), a claim's row by `denseAtFast` (FastDense.lean)

By what. `halvedW` and `csW` compute at `Fld.two` alone and take no field as an argument, while the
fields `rounds` and `folded` do. So each of the two is chosen by a match on the field: at `Fld.one`
`FoldOwn.honest` (Fmt/M1Fold.lean) and `csFast` stay. `stagesBy` calls both at `Fld.two`.

`fast_eq : Seams.fast = Seams.lib` (FastWLaw.lean): the two structures are equal, without
hypothesis. So whatever is proved of `runBy` at `Seams.lib` holds at `Seams.fast`.

Limits. The first four compute with random values too (rows' tails, mask rows, free entries, a
hiding polynomial's coefficients); their files say with which defaults. Nothing is measured here.
Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Fast
import Johnson.Desc.ProofFile.Honest.K12.HalveW
import Johnson.Desc.ProofFile.Honest.K12.CsW
import Johnson.Desc.ProofFile.Honest.K12.ColW
import Johnson.Desc.ProofFile.Honest.K12.FastDense

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light

/-- The five functions, each in a version meant to be faster. Equal to `Seams.lib` (`fast_eq`,
FastWLaw.lean). -/
def Seams.fast : Seams :=
  ⟨fun f T g =>
    match f with
    | .two => halvedW T g
    | .one => Fmt.M1.FoldOwn.honest .one T [] g,
   fun f =>
    match f with
    | .two => csW
    | .one => csFast .one,
   tabFast, fun next last Q => colTreeW next last Q, denseAtFast⟩

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.Seams.fast
