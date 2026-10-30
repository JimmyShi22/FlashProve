-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/SoundOfConditionsFree.lean: `sound_of_conditions_free_at`: soundness of the
name's system of record at one set of public files Z, AT THE CLOSED FILLING of the tower's free
letters (`h.free`), with ALL THREE JOINING ROWS, the shared chain's whole row, the key file's
condition and the closed tests paid by their files' theorems. IT COMPILES OVER THE PROOF FILE'S
ENTRY TESTS AS A LIST OF FOURTEEN ROWS.
No letter is bound in the binder `last`, and the row `tables_fit` is no hypothesis.


It is `sound_of_conds_at_free` (Johnson/Goal/Skeleton/SoundOfCondsAtFree.lean) at
  the key file:     `keySound_at_live_holds` (Johnson/Goal/Conditions/KeyOpenHolds.lean)
  the closed tests: `conds_of_laid` (Johnson/Goal/Skeleton/CondsOfLaid.lean)
  the typed stages: `H2K12.lastTypedAt_of_live` (Johnson/Loose/H2K12/LastTypedOfLaid.lean)
  the five rows:    `P5J.five_at_free2_laid2` (Johnson/P5J/FiveAtFree2Laid2.lean): head_cuts,
                    reply_leaves, shared_joint_count and tables_fit are called there.

THE HYPOTHESES, all at the one Z (in scope, read as pp, with exact match), where `protocolDataWellFormed` accepts:
  `owed`   `At.CondsOwed Z`: `rowsRead Z`: one test with code on the three public files; over
           thirteen entry tests no test that `verify` runs asks it; over fourteen the fourteenth
           asks its like, and SoundOfBareLawsDoor.lean has `owed` from it
  `kinds`  under every head: `KindsConds h h.free`: the first chain's kinds, each by its files' own
           named condition, or bare (Johnson/Goal/Skeleton/KindsOfConds.lean says which)
  `last`   under every head: `h.LastLeftAt` (Johnson/P5J/L0/LastLeftAt.lean): what other files'
           theorem on the last chain's row leaves, at closed terms of the head: tests on public
           data, facts on reached states, and, as long as it stands there, one law: that file and
           Johnson/P5J/L0/LastFreeT.lean say which.
AGAINST `sound_of_conditions_no_key_at`: no filling is chosen by the payer; the seven shares of the
two later chains are gone (the shared chain's are paid inside, the last chain's stand as
`LastLeftAt`); none of the three joining rows is a hypothesis.

Limits. ONE CALL: IT PAYS NOTHING. Those of the files that are called. `LastLeftAt` is False where
the last chain's stretch of the laid data is empty. One of its tests (`Sh.Tests`) has been evaluated
true at the stored full-size files and FALSE at the stored small ones: AT THE SMALL SIZE THIS
THEOREM SAYS NOTHING. The shared chain's row is paid by `Desc.K14.Law.k14_at_free_head`, a long
proof in other files.
NO CONDITION IS SHOWN TO BE MET IN LEAN AT ANY Z: THE THEOREM MAY BE
EMPTY, and one field that cannot be met empties it whole. No kind's law is proved.

-/
import Johnson.Goal.Skeleton.SoundOfCondsAtFree
import Johnson.Goal.Skeleton.CondsOfLaid
import Johnson.Loose.H2K12.LastTypedOfLaid
import Johnson.Goal.Conditions.KeyOpenHolds
import Johnson.P5J.FiveAtFree2Laid2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals FlashProve FlashProve
open P5J

/-- **SOUNDNESS AT ONE SET OF PUBLIC FILES, AT THE CLOSED FILLING, NO JOINING ROW ASSUMED.** -/
theorem sound_of_conditions_free_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact)
    (owed : protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsConds h h.free)
    (last : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        h.LastLeftAt) :
    VerifiableInference.Sound (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp))
      fun t => VerifierAndGoals.soundnessErrorInQueries t 1 :=
  sound_of_conds_at_free Z pp scope read exact (keySound_at_live_holds Z scope)
    (fun hl => conds_of_laid scope hl read (owed hl))
    (fun hl => H2K12.lastTypedAt_of_live Z scope hl) kinds
    fun hl Zp Np cF x h => five_at_free2_laid2 h hl (last hl Zp Np cF x h)

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.sound_of_conditions_free_at
