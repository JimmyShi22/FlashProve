-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/LightLook.lean: A TEXT FOR WHAT THE LOOKUP IN FRONT HAS SAMPLED
THAT LAYS EACH CALL's KEY POINT ALONE. Two definitions with code; no theorem. GENERAL IN THE
LOOKUP's SHAPE AND IN THE NUMBER OF ROUNDS IN FRONT OF IT: no number of a size stands in this file.
It imports Honest/K3/Heard.lean alone, so that a text that is made of it stays light; the laws on it
stand in LightLookLaw.lean of this folder.

Why. `ProofFile.Honest.K3.lookHeardAt h base heard` (Honest/K3/HeardWhole.lean) fills eleven fields of the
verifier program's structure of a lookup. Two of them, tT and leavesA, are tables' values: dear to
make. Of that structure the layers' arm of the pile's filler's parameter reads the field zk alone
(`layersClaims_reads_zk`, ClaimsReadZk.lean of this folder), and so does the text for the head's key
points, which is that field. Where the compiler does not lay a function's text into its caller's, a
compiled program makes every field of the structure that the function returns before one is read: so
a caller that EVALUATES the filler pays for the two tables and reads neither. THAT IS A WORD ON
LEAN's COMPILER, BY READING; NOTHING HAS BEEN TIMED.
Main names:
  `callKeysAt h base heard`: each call's key point: the field zk of `keyPtsAt`
    (Honest/K3/Heard.lean).
  `lookZkAt h base heard`: **the light text**: the structure with the shape and zk laid; the field
    leaves, which has no default, laid empty as the full text lays it; ALL ELSE AT THE STRUCTURE's
    OWN DEFAULTS.
AT LEAST THREE TEXTS OF OTHER FOLDERS ARE `callKeysAt` AT ARGUMENTS OF THEIR OWN; this file, which
has no theorem, shows it of none: `ProofFile.Honest.K3.Law.AtThr.headKeysOfK3`
(Honest/K3/Law/Thread/HeadCallsTie.lean), `ProofFile.Honest.K11.keysAtLink`
(Honest/K11/KeysAtLink.lean) and one arm of `ProofFile.Honest.K5.keyOfK3`
(Honest/K5/Law/KeyOfK3.lean). For the second the equation is `keysAtLink_eq`
(PileOfAnySizeSame.lean: no part of the library): within the library nothing ties the two.

A CALLER MUST READ NOTHING BUT shape AND zk OFF THE LIGHT TEXT: theta, alpha, zx, zy, e, zb0, zb1,
tT and leavesA, which the full text fills, are blank in it; so `OpenSame` (HeardWhole.lean) NEED NOT
HOLD between it and a hearing's structure, and is claimed of it nowhere.

Where the two texts fall silent. They take over `keyPtsAt`'s defaults (the first two: the head of
Honest/K3/Heard.lean, under "Limits"; the third: the text of `keyPtsOf` there): A ROUND THAT IS NOT
YET HEARD, OR THAT SAMPLED FEWER ELEMENTS THAN ARE READ, COUNTS AS ZEROS; more elements than are
read are dropped; a call for which the shape states no number of tree bits counts as 0 bits; NOTHING
REJECTS. That base is the number of the chain's rounds in front of the lookup is the caller's. So at
a list of challenges that is too short, or at a wrong base, both yield key points of the right
lengths with wrong or zero coordinates, WITH NO MARK.

The name zk, here and in the files named, is a field of the lookup's structure: each call's key
point: it does not stand for zero knowledge. What is not claimed. That the text is what a run's
lookup returns. That anything is faster: not timed. The definitions are none of the library's goals.
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K3.Heard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes (E)
open OnBytes.Model (Forest.Shape Forest.Heard)
open ProofFile.Honest.K3 (keyPtsAt)

/-- Each call's key point, of the lookup's shape, the number of rounds in front and the challenges
heard. -/
def callKeysAt (h : Forest.Shape) (base : Nat) (heard : List Fmt.Drawn) : Array (Array E) :=
  (keyPtsAt h base heard).zk

/-- **THE LIGHT TEXT**: the shape and each call's key point; all else at the structure's defaults.
-/
def lookZkAt (h : Forest.Shape) (base : Nat) (heard : List Fmt.Drawn) : Forest.Heard :=
  { shape := h, leaves := {}, zk := callKeysAt h base heard }

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.callKeysAt
#print axioms ProofFile.Honest.K13.lookZkAt
