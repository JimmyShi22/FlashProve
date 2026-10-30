-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/SoundOfConditionsCore.lean: `sound_of_conditions_core_at`: soundness of the
name's system of record at one set of public files Z, from the first chain's kinds and TWO TESTS ON
THE PUBLIC FILES. IT COMPILES OVER THE PROOF FILE'S ENTRY TESTS AS A LIST OF FOURTEEN ROWS.

The binder `core` is one Bool of Z alone.


It is `sound_of_conditions_free_at` (Johnson/Goal/Skeleton/SoundOfConditionsFree.lean)
with its hypothesis on the last chain, `h.LastLeftAt`, paid by the
theorem `P5J.lastLeft_of_coreAt` (Johnson/P2LawR/CoreAtFiles.lean) from `P5J.coreAt Z = true`.

THE HYPOTHESES, all at the one Z (in scope, read as pp, with exact match), where `protocolDataWellFormed` accepts:
  `owed`    `At.CondsOwed Z`: `rowsRead Z`: one test with code on the three public files; over
           thirteen entry tests no test that `verify` runs asks it; over fourteen the fourteenth
           asks its like, and SoundOfBareLawsDoor.lean has `owed` from it
  `kinds`   under every head: `KindsConds h h.free`: the first chain's kinds, each by its
           own named condition, or bare, or called (Johnson/Goal/Skeleton/KindsOfConds.lean says
           which)
  `core`    `P5J.coreAt Z = true`: one Bool of the three public files: the head's letters are made
           from the files, and at them the conjunction of fifteen named tests on the plan of the
           last chain's own proximity test is asked; no test that `verify` runs asks it.

SO NO JOINING ROW, NO SHARE OF THE TWO LATER CHAINS, NO FACT ON REACHED STATES OUTSIDE `kinds`, AND
NOTHING ON THE KEY FILE OR THE COPY'S FILE IS A HYPOTHESIS HERE.

Limits. One call: it pays nothing. The limits of the files that are called hold here too.
No evaluation of `coreAt` at any files is told in this library (CoreAtFiles.lean's head),
and it stands in a noncomputable section: if it is false at the
release's files this theorem says nothing there. The head stands over fourteen entry tests, two of
which compare the plan with values written for the full size. No kind's law is proved here, and no
condition is shown to be met in Lean at any Z.
-/
import Johnson.Goal.Skeleton.SoundOfConditionsFree
import Johnson.P2LawR.CoreAtFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals FlashProve FlashProve
open P5J

/-- **SOUNDNESS AT ONE SET OF PUBLIC FILES, FROM THE FIRST CHAIN'S KINDS AND TWO TESTS ON THE
PUBLIC FILES.** -/
theorem sound_of_conditions_core_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact)
    (owed : protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsConds h h.free)
    (core : protocolDataWellFormed (asDescriptionFiles Z) = true → P5J.coreAt Z = true) :
    VerifiableInference.Sound (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp))
      fun t => VerifierAndGoals.soundnessErrorInQueries t 1 :=
  sound_of_conditions_free_at Z pp scope read exact owed kinds
    fun hl _ _ _ _ h => P5J.lastLeft_of_coreAt (core hl) h

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.sound_of_conditions_core_at
