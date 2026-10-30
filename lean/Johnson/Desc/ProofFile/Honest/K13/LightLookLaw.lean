-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/LightLookLaw.lean: THE CLAIMS OF THE LAYERS' ARM OF THE PILE's
FILLER's PARAMETER (`layersClaims`, ClaimsIsLayers.lean of this folder) AT THE LIGHT TEXT FOR WHAT
THE LOOKUP IN FRONT HAS SAMPLED (`lookZkAt`, LightLook.lean) ARE THE CLAIMS AT THE FULL TEXT
(`ProofFile.Honest.K3.lookHeardAt`, Honest/K3/HeardWhole.lean). Statements with their proofs: unfoldings
and one lemma, called twice. GENERAL IN THE LOOKUP's SHAPE AND IN THE NUMBER OF ROUNDS IN FRONT.
Main names:
  `callKeysAt_full` · `lookZkAt_zk`: both are the field zk of `lookHeardAt` at the same three
    arguments: by unfolding.
  `layersClaims_light`: **at every small input w of K4's honest parts: `layersClaims`
    (ClaimsIsLayers.lean) with `lookZkAt h base` laid as its `look` is `layersClaims` with
    `lookHeardAt h base` laid there**, at every Q, instance and list of challenges: by
    `layersClaims_reads_zk` (ClaimsReadZk.lean).
  `layersClaims_light_of`: the same where the shape and the count are read off the instance by any
    two functions: the form in which a maker of the small input would be written.
Who calls. `layersClaims_light`: PileOfAnySizeAt.lean of this folder. The other three: no file yet.

What is not claimed. That either text is what a run's lookup returns: that is the tie of
Honest/K3/Law/. Anything on what else reads a `K4In`. The name zk, here and in the files named, is a
field of the lookup's structure: each call's key point: it does not stand for zero knowledge.
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.LightLook
import Johnson.Desc.ProofFile.Honest.K13.ClaimsReadZk
import Johnson.Desc.ProofFile.Honest.K3.HeardWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes.Model (Forest.Shape Forest.Heard)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In)
open ProofFile.Honest.K3 (lookHeardAt)

/-- The key points are the full text's field zk. -/
theorem callKeysAt_full (h : Forest.Shape) (base : Nat) (heard : List Fmt.Drawn) :
    callKeysAt h base heard = (lookHeardAt h base heard).zk := rfl

/-- The light text has the full text's field zk. -/
theorem lookZkAt_zk (h : Forest.Shape) (base : Nat) (heard : List Fmt.Drawn) :
    (lookZkAt h base heard).zk = (lookHeardAt h base heard).zk := rfl

variable {Xi : Type}

/-- **THE CLAIMS AT THE LIGHT TEXT ARE THE CLAIMS AT THE FULL ONE.** -/
theorem layersClaims_light (Q : K4Pub) (w : Xi → K4In) (h : Forest.Shape) (base : Nat) (ξ : Xi)
    (hd : List Fmt.Drawn) :
    layersClaims Q (fun x => { w x with look := lookZkAt h base }) ξ hd =
      layersClaims Q (fun x => { w x with look := lookHeardAt h base }) ξ hd :=
  layersClaims_reads_zk Q _ _ ξ hd rfl rfl

/-- The same where the shape and the count hang on the instance. -/
theorem layersClaims_light_of (Q : K4Pub) (w : Xi → K4In) (shapeOf : Xi → Forest.Shape)
    (baseOf : Xi → Nat) (ξ : Xi) (hd : List Fmt.Drawn) :
    layersClaims Q (fun x => { w x with look := lookZkAt (shapeOf x) (baseOf x) }) ξ hd =
      layersClaims Q (fun x => { w x with look := lookHeardAt (shapeOf x) (baseOf x) }) ξ hd :=
  layersClaims_reads_zk Q _ _ ξ hd rfl rfl

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.callKeysAt_full
#print axioms ProofFile.Honest.K13.lookZkAt_zk
#print axioms ProofFile.Honest.K13.layersClaims_light
#print axioms ProofFile.Honest.K13.layersClaims_light_of
