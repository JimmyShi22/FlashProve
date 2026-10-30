-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinksFreeHeadAll.lean: the pieces of the check of the head at two requests, gathered.

OnBytes/Flat/LinksFreeHead.lean cuts `HeadFree p` into seven pieces. Five are shown: `hearFree`,
`weightsClaimFree` (OnBytes/Flat/LinksFreeHeadA.lean), `tablesFree`
(OnBytes/Flat/LinksFreeTables.lean), `walkFree` (OnBytes/Flat/LinksFreeHeadD.lean), and
`selfTestsFree` here, over OnBytes/Flat/LinksFreeHeadF.lean and OnBytes/Flat/LinksFreeCoef.lean.

Main theorems: `selfTestsFree`; `headFree_of_two`: `HeadFree p` at every p from `TranscriptFree` and
`DoorFree`.

Not claimed: these two. Nothing on a run on a view. For proofs only; no module of the program
imports this file.


-/
import OnBytes.Flat.LinksFreeHeadF
import OnBytes.Flat.LinksFreeCoef
import OnBytes.Flat.LinksFreeTables

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Model

/-- **The tests of the verifier's own walk, at two requests.** -/
theorem selfTestsFree : SelfTestsFree := selfTestsFree_of coefficientsF_rel

/-- **The check of the head at two requests**, from the two pieces that are not gathered here. -/
theorem headFree_of_two (h3 : TranscriptFree) (h7 : DoorFree) (p : Verify.Planned) : HeadFree p :=
  headFree_of hearFree tablesFree h3 weightsClaimFree walkFree selfTestsFree h7 p

end OnBytes.Flat
