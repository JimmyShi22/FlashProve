-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/KeysAtLink.lean: EACH CALL's KEY POINT, OF THE LOOKUP ON THE CALLS
OF A LINK, GENERAL IN THE SIZE: THE LINK AND THE ROUNDS IN FRONT ARE ARGUMENTS. Two definitions with
code. NOTHING IS STATED OR PROVED IN THIS FILE.

  `callsShapeAt Z m`    the shape of the site on the calls at link m: kind K3's own line
                        (`headCallsShape`, Honest/K3/Law/Thread/HeadCallsTie.lean, at link 24 ·
                        `callsShape`, LayersTieHead.lean of that folder, at link 2 g) with the link
                        an argument
  `keysAtLink m n₀`     each call's key point: the field zk of kind K3's `keyPtsAt`
                        (Honest/K3/Heard.lean) at that shape. n₀: how many rounds of the first chain
                        stand in front of that lookup

Why. Kind K3's texts for the key points (`headKeysOfK3`; the field zk of `lookOfK3`) are written at
the full size's numbers. These two are meant to serve the layers' links and the head's at every
size: `keysAtLink` is called at the head alone (`headFourN`, ClaimsN.lean of this folder); the
layers go by `callsShapeAt` (Honest/K13/PileOfAnySize.lean); what is shown is at the full size.

Limits. DEFINITIONS ALONE: THAT AT LINK 24 AND THE ROUNDS IN FRONT OF NUMBER 340 `keysAtLink` IS
`headKeysOfK3` IS SHOWN BY NO FILE OF THE LIBRARY BY ITSELF (inside `headFourN_scope`,
Honest/K13/PileOfAnySizeAt.lean, it is used). HOW A LINK's SHAPE IS FOUND AT A GENERAL PUBLIC PART
IS KIND K3's TO SAY: the line is taken from its two texts; no law of that kind says it at a general
link. WHERE THE LIST OF SITES HAS NONE AT LINK m THE DEFAULT SHAPE IS READ, IN SILENCE. No file of
the library runs it. The name zk is a field of the lookup's structure: not zero knowledge. Nothing
on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Heard
import Johnson.Desc.ProofFile.Honest.K3.Lot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (E)
open ProofFile.Honest.K3 (keyPtsAt lookSites)

/-- **The shape of the site on the calls at link m.** WHERE THE LIST OF SITES HAS NONE IT IS THE
DEFAULT SHAPE, IN SILENCE. -/
def callsShapeAt (Z : Pub) (m : Nat) : OnBytes.Model.Forest.Shape :=
  (((lookSites Z).find? fun s => s.link == m && !s.digits).map (·.shape)).getD default

/-- **Each call's key point, of the lookup on the calls of link m.** n₀: the rounds of the first
chain in front of that lookup. The ground is not read. -/
def keysAtLink (m n₀ : Nat) : Pub → Ground → List Fmt.Drawn → Array (Array E) :=
  fun Z _ hd => (keyPtsAt (callsShapeAt Z m) n₀ hd).zk

end ProofFile.Honest.K11

#print axioms ProofFile.Honest.K11.callsShapeAt
#print axioms ProofFile.Honest.K11.keysAtLink
