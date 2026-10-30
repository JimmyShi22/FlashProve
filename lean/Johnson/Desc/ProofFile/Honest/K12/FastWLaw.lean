-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FastWLaw.lean: `Seams.fast` (FastW.lean) equals `Seams.lib`
(Run.lean), as structures and without hypothesis. It imports Mathlib through the law files.

  `fast_eq`      `Seams.fast = Seams.lib`
  `runBy_fast`   so `runBy` (RunBy.lean) returns the same value at both, warnings included

By what. Field by field, each by the equation of its function: `halvedW_eq` (HalveWLaw.lean) with
`halved_eq` (HalveLaw.lean); `csW_eq` (CsWLaw.lean) with `csFast_eq` (FastLaw.lean); `tabFast_eq`
(FastLaw.lean); `colTreeW_eq` (ColWLaw.lean); `denseAtFast_eq` (FastDenseLaw.lean). At `Fld.one`
the first field is the original itself, and the second is `csFast`.

Limits. Nothing on cost. Two definitions give the same words; nothing follows on what a verifier
decides.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.FastW
import Johnson.Desc.ProofFile.Honest.K12.FastLaw
import Johnson.Desc.ProofFile.Honest.K12.HalveWLaw
import Johnson.Desc.ProofFile.Honest.K12.CsWLaw
import Johnson.Desc.ProofFile.Honest.K12.ColWLaw
import Johnson.Desc.ProofFile.Honest.K12.FastDenseLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Fmt (Fld)

theorem fast_eq : Seams.fast = Seams.lib := by
  have h1 : Seams.fast.rounds = Seams.lib.rounds := by
    funext f T g
    cases f
    · rfl
    · show halvedW T g = Fmt.M1.FoldOwn.honest .two T [] g
      rw [halvedW_eq]
      exact halved_eq T g
  have h2 : Seams.fast.folded = Seams.lib.folded := by
    funext f
    cases f
    · show csFast .one = Fmt.M1.csOwnG .one
      rw [csFast_eq]
    · show csW = Fmt.M1.csOwnG .two
      rw [csW_eq, csFast_eq]
  have h3 : Seams.fast.tab = Seams.lib.tab := tabFast_eq
  have h4 : Seams.fast.tree = Seams.lib.tree := by
    funext next last Q
    exact colTreeW_eq next last Q
  have h5 : Seams.fast.dense = Seams.lib.dense := denseAtFast_eq
  show (⟨Seams.fast.rounds, Seams.fast.folded, Seams.fast.tab, Seams.fast.tree,
    Seams.fast.dense⟩ : Seams) = Seams.lib
  rw [h1, h2, h3, h4, h5]

theorem runBy_fast (I : RunIn) (D : Nat → Fmt.Drawn) :
    runBy Seams.fast I D = runBy Seams.lib I D := by
  rw [fast_eq]

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.fast_eq
#print axioms ProofFile.Honest.K12.Light.runBy_fast
