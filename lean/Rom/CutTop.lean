-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/CutTop.lean: the two theorems on the splitting step for a whole scheme, `cutExit` and
`cutState`. The head of Rom/SpecCut.lean says what the statements say and what they do not.

  `cutExit : Spec.cutExit`   An oracle is split in two, one for the first part of its answer and one
                             for the second; the second is queried only where a rule that sees the
                             first part says so. If committer, prover and verifier each meet the
                             condition `ReadsCut` under their rule (`NeedOKCut`) and the extractor
                             reads only entries at oracles that are not split (`WholeOnly`), then
                             completeness, index binding and index privacy (ZKCP/Gen.lean), with
                             named extractor and simulator (`IsZKCPArgWith`), carry over with the
                             same three bounds.
  `cutState : Spec.cutState` Under these two conditions and those of the step that expands long
                             answers from a state (Rom/StateFirst.lean: its bounds on queries to
                             chain oracles, and `PlainOnly` and `HidFree` of the scheme after the
                             splitting and of its extractor), the three properties carry over to the
                             scheme after both steps, with that step's three bounds. The numbers in
                             its added error terms are counted on the algorithms before the
                             splitting, in a weight in which a query whose second part is not
                             queried does not count its second part.

`cutExit` follows from `completeness_cut`, `binding_cut` (Rom/CutBind.lean: completeness, index
binding) and `privacy_cut` (Rom/CutPriv.lean: index privacy); `cutState` follows by `cutState_of`
(Rom/CutState.lean) and `cutCost` (Rom/CutRun.lean).

Limits, from the head of Rom/SpecCut.lean, which has more: nothing is said about any scheme, and
which rule each algorithm runs under is left to the user. Only the three properties of
`IsZKCPArgWith` are carried over. In `cutExit` the bounds stay the same, but a query of an honest
algorithm whose second part is asked is now two queries. Both theorems go from typed oracles to
typed oracles and say nothing about one hash function.
-/
import Rom.CutPriv
import Rom.CutState

set_option autoImplicit false

noncomputable section

namespace Rom

theorem cutExit : Spec.cutExit := fun _ C _ _ _ _ _ _ _ R _ B E Sim α ε ζ _ _ _ hN hE h =>
  ⟨completeness_cut C R hN B α h.completeness,
    binding_cut C R hN E hE ε h.indexBinding,
    privacy_cut C R hN B Sim ζ h.indexPrivacy⟩

theorem cutState : Spec.cutState := cutState_of cutExit cutCost

end Rom
