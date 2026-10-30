-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsKeysAt.lean: `KeysFit` (Johnson/Road/K4/K4PinsKeys.lean) AT THE LOOKUP's
AUTHORS' OWN PUBLIC LETTERS OF A LAYERS' SEGMENT, `pubAt X (m / stepOf X)`
(Johnson/Desc/First/Look/K3CallerMeans.lean): the letters at which `meanEqs_of_means`
(Johnson/Road/K4/K4PinsOfMeans.lean) hands `K4MeanEqs`. One theorem: `keysFit_of_pub`
(Johnson/Road/K4/K4PinsKeysPub.lean), called: two of its three equations on the letters hold by
unfolding; the third is a premise on two numbers. And the layout's equation that `k4_own_end` asks.

  **`keysFit_at_pub`**: `KeysFit X p (pubAt X (m / stepOf X))`, from `PublicSteps`, `RefPub`, the
    two lines on p, and m / stepOf X = p.g.
  `pubAt_y`: `(pubAt X g).y = X.layers.y`, by unfolding.

OBJECT: none of its own. USER: K4PinsPlanOf.lean, K04LawOf.lean, two more. LETTERS: X, p, m: free.

Limits. K04_law IS NOT PROVED BY THIS. m / stepOf X = p.g IS A PREMISE (it follows from m = 2 p.g
where attention has a link of its own: not drawn here).
-/
import Johnson.Road.K4.K4PinsKeysPub
import Johnson.Desc.First.Look.K3CallerMeans
import Johnson.Desc.First.Look.K3CallerLayTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes.Model.Verify (Public)
open VerifiableInference.PlanWritten (PublicSteps)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc.First.Look (pubAt stepOf)

/-- **`KeysFit` at the lookup's authors' public letters.** -/
theorem keysFit_at_pub {pol KL : ByteArray} {X : Public} {p : Par} {tk : Array Nat} {m : ℕ}
    (St : PublicSteps pol KL X) (B : RefPub X p.g) (hP : p.P = { X.layers with tokv := tk })
    (hG : X.G[p.g]? = some p.hp) (hgr : m / stepOf X = p.g) :
    KeysFit X p (pubAt X (m / stepOf X)) :=
  keysFit_of_pub St B hP hG rfl rfl hgr

/-- The layout of these letters is the public parameters'. -/
theorem pubAt_y (X : Public) (g : ℕ) : (pubAt X g).y = X.layers.y := rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.keysFit_at_pub
#print axioms OnBytes.Road.K4.pubAt_y
