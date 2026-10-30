-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/JoinB.lean: THE LAYERS' OWN ROUNDS (K4): A TEST ON THE PLAN FOR THE
LOOKUP's JOIN, AS A FUNCTION WITH VALUES IN Bool, IN A FILE OF ITS OWN. Two definitions; no law;
nothing is evaluated.

The laws about them stand in Johnson/Desc/First/K4/Returns/JoinSkel.lean, which imports this file.

  envBlank        the environment of the forms with no point of the lookup laid.
  joinB           each call's factor in the join is there, at no point, at the elements 0 and with
                  the array of the columns' marks left empty. Whether a factor is there does not
                  hang on that array (joinPart_skel, JoinSkel.lean): so the marks need not be made.

Limits. That joinB is true at a plan is not shown here. Nothing on soundness, completeness or
hiding.
-/
import OnBytes.Model.LayerForms
import OnBytes.Model.LayerPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt

open OnBytes OnBytes.Model OnBytes.Model.Layer

/-- The environment of the forms with no point of the lookup laid. -/
def envBlank (P : Pub) (hp : HPlan2) (g iU3 : Nat) (tab : List TableAt) : Env :=
  { y := P.y, sc := P.sc, g := g, iU3 := iU3, K3 := ((hp.Fp.trees[iU3]?).map (·.K)).getD 0,
    tab := tab, zk := #[] }

/-- **The test on the plan**: each call's factor in the join is there, at no point, at the elements
0 and with the array of the columns' marks left empty. -/
def joinB (P : Pub) (hp : HPlan2) (g iU3 : Nat) (tab : List TableAt) : Bool :=
  (List.range P.y.calls.size).all fun q =>
    ((envBlank P hp g iU3 tab).joinPart zeroE zeroE q (P.y.calls.getD q default) #[]).isSome

end OnBytes.Desc.First.K4.Rt
