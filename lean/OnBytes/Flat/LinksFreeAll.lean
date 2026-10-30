-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinksFreeAll.lean: the rounds of a proof's first chain do not hang on the request.

A description of a protocol has one list of rounds for all instances, and the rounds of a proof's
first chain are made by a dry run of a block that knows the request. `PlannedFirstFree p`
(OnBytes/Flat/LinksDry.lean) says that at any two requests which `Head.coveredOf` takes the two dry
runs both fail, or both return, with the same rounds, the same statement, the same book of trees and
the same four numbers of what the test on the table passes on. OnBytes/Flat/LinksFree.lean cuts it
into four statements, OnBytes/Flat/LinksFreeHead.lean cuts the one on the head into seven. Here all
are gathered.

Main theorems.
 `headFree`          `HeadFree p`, at every p.
 `plannedFirstFree`  `PlannedFirstFree p`, under one premise hV: the size of the vocabulary by which
                  the request's tokens are tested is at most the one that the checks of the layers
                  hold. `Verify.publicOf` lays one number at both places; that is read from its
                  text, not shown here.

Where each piece lies: `layerFree` OnBytes/Flat/LinksFreeLayer.lean; `pendingFree`
OnBytes/Flat/PendingFreeOf.lean; `memberFree` OnBytes/Flat/MemberFree.lean; `hearFree`,
`weightsClaimFree` OnBytes/Flat/LinksFreeHeadA.lean; `tablesFree` OnBytes/Flat/LinksFreeTables.lean;
`transcriptFree` OnBytes/Flat/TranscriptFreeOf.lean; `walkFree` OnBytes/Flat/LinksFreeHeadD.lean;
`selfTestsFree` OnBytes/Flat/LinksFreeHeadAll.lean; `doorFree` OnBytes/Flat/LinksFreeDoor.lean.

Not claimed: hV at any p. That a dry run returns at any p: two dry runs that both fail count as
alike, whatever the names of the two failures. The statement speaks of the requests that
`Head.coveredOf` takes and at which `Verify.linksOf` returns: at a p where one of the two never
returns it holds idly. Anything on a run on a view: there the tests that a dry run skips are made,
and the decision hangs on the request. Nothing on the other chains. For proofs only; no module of
the program imports this file.


-/
import OnBytes.Flat.LinksFreeHeadAll
import OnBytes.Flat.LinksFreeDoor
import OnBytes.Flat.TranscriptFreeOf
import OnBytes.Flat.MemberFree
import OnBytes.Flat.PendingFreeOf

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Model

/-- **The check of the head at two requests.** -/
theorem headFree (p : Verify.Planned) : HeadFree p := headFree_of_two transcriptFree doorFree p

/-- **The rounds of a proof's first chain do not hang on the request.** -/
theorem plannedFirstFree (p : Verify.Planned) (hV : p.X.P.h.V ≤ p.X.layers.V) :
    PlannedFirstFree p :=
  plannedFirstFree_of layerFree pendingFree memberFree p (headFree p) hV

end OnBytes.Flat
