-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/LinkDecAt.lean: for public files that pass the two tests InScope and
protocolDataWellFormed, the link decision inside dataAtFiles flashProveData Z is the decision of which link_yes speaks
(dec_at_D).
What the link is, and where these files stand: Johnson/Prover/Link/LinkYesStm.lean.

The setting. dataAtFiles flashProveData Z (Johnson/Goal/Tie/DescriptionOfData.lean) is the protocol data at the public
files Z from which the description descriptionOfDataOnBytes flashProveData is made (a structure DescriptionDataAtFiles,
Johnson/Goal/Tie/DescriptionOnDecodedProof.lean). Among its fields are the plan's values, the key file's and the proof
file's rounds' data, and three decisions, of which dec is the link's. flashProveData
(Johnson/Goal/Description/Lay.lean) gives each of these as a function of the files. Its dec stands
behind a gate: it is protocolDataWellFormed && the link's decision (theLinkGate,
Johnson/Goal/Description/Gates.lean), so where protocolDataWellFormed rejects it rejects everything. That is why
protocolDataWellFormed is a premise below. asDescriptionFiles Z (Johnson/Goal/Tie/ReadThruHead.lean) is the three public
files: parameter file, layout file, scale file. descriptionOfDataOnBytes flashProveData is the description at which
completeOn_last's verifier stands (Johnson/Goal/Conditions/HomeLast.lean).

What this file has. dec_at_D. Let Z be public files with InScope Z = true and protocolDataWellFormed (asDescriptionFiles Z) =
true. Then the field dec of dataAtFiles flashProveData Z equals the following function of an instance rr and a
view V (the decision's input, Fmt.View): (linkDescriptionAt frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan)).run at the
two table keys made of rr, on V (linkDescriptionAt: Johnson/Desc/Link/LinkDesc.lean; the structure OneChainFileDescription and
its run: Johnson/Desc/Link/OneChainFileDescription.lean). That function is the decision in LinkYes
(LinkYesStm.lean), with the same two keys (keysOf).
The two tests. InScope (Ladder.lean) is a Boolean function of the public files. The layout file
equals that of the stored full-size example (storedPublicFiles.lay), the files can be read, the parameter file
is policyFile at the eight free numbers that were read from it (FreeLines, Ladder/Stored.lean), and
2 ^ 8 ≤ theta, one of the eight. So what is free in scope is these eight numbers and the scale file.
protocolDataWellFormed (Johnson/Goal/Description/Live.lean) is a Boolean function of the public files too. The
description's three makers (the plan's, the key file's, the proof file's) return a value at them,
both files' data have the depth of the full-size parameter set, the description's test on numbers
passes, and none of the six lists of rounds is empty. That it accepts is proved in Lean, in the side
library (outside the main library and with that library's own limits), at the written copy of the
full-size example under every acceptance policy in scope (C, theta, cap: three of the eight;
theLive_zAt, AtFullSide/Top/LiveAtPolicies.lean). For the rest of the scope see
Johnson/Goal/Conditions/HomeLast.lean, limit 4.

How it fits. link_yes (Johnson/Prover/Link/LinkJoinF.lean) proves that this decision accepts the
explicit honest prover's view, where Meant holds. linkFits_of_yes
(Johnson/Goal/Conditions/LinkFitsHome.lean) rewrites by dec_at_D, so that its premise in LinkYes'
form, which link_yes proves on the way to linkFits_at (Johnson/Goal/Conditions/LinkFitsAt.lean),
speaks of the decision of dataAtFiles flashProveData Z. This file states no goal. dec_at_D is a theorem about the
goals' description.

Lemmas used: dec_the_at (Johnson/Goal/Conditions/GatesAtThe.lean) · K15_sits_keys
(Johnson/Goal/Conditions/EntrySits.lean).

Limits. dec_at_D is an equation of functions. Nothing in this file says that the decision accepts
(see link_yes).
It is proved only for public files that pass InScope and protocolDataWellFormed.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.EntrySits
import Johnson.Goal.Conditions.GatesAtThe

set_option autoImplicit false

namespace FlashProve
open VerifierAndGoals FlashProve OnBytes.Flat OnBytes.Slice
open _root_.Desc.K15 (frP linkDeclaredRounds linkRoundsMatchPlan linkDescriptionAt)

/-- **The link decision inside dataAtFiles flashProveData Z is the decision of LinkYes**, for public files that
pass InScope and protocolDataWellFormed. An equation of functions; LinkYes' keysOf
(Johnson/Prover/Link/LinkYesStm.lean) is written out in it. -/
theorem dec_at_D {Z : PublicFiles} (hZ : InScope Z = true) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    (dataAtFiles flashProveData Z).dec = fun rr V =>
      (linkDescriptionAt frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP OnBytes.Params.recordPlan)).run
        (keyOf (fun β : NZ => β.val) rr.1,
          { keyOf (fun β : NZ => β.val) rr.2 with item := 1 }) V := by
  rw [dec_the_at Z _ (K15_sits_keys hZ), hl]
  rfl

end FlashProve
