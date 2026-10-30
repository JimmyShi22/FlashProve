-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4OnX.lean: NINE FACTS ON THE PUBLIC PARAMETERS X AND K4's OWN PARAMETERS par AT A
SEGMENT m, AS ONE STRUCTURE: seven are fields of `K4RowPlan` (K4RowOfMeans.lean) to the letter, at
hp := par.hp; two more tie par to X and to m. A definition alone: it reads X, the two public files,
the layout file, m and par: no meaning, no data of a meaning.

  `K4OnX`: shape · pc2 · pc7 · pubOf · notHead · step · plan (`K4RowPlan`'s seven) · g (m is twice
    K4's group's number) · y (K4's layout of the model is X's).

WHO PAYS: Riders/OnXOfPlan.lean (`k4OnX_of_plan`, `k4OnX_of_scope`): Riders/PlanOfScope.lean's
structure PlanAtX has these nine lines (at m := 2 * g; its line g reads par.g = g), and its theorem
plan_of_scope has them in the goals' scope, where X.p4 = true, at every member of the IOP as written
in Lean's list of K4's parameters (not imported here).

Limits. A structure of premises. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED.
Nothing on soundness.
-/
import Johnson.Desc.First.K4.Block
import Johnson.Desc.First.Look.K3Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)

/-- Nine facts on the public parameters and K4's own parameters at segment m. -/
structure K4OnX (X : Verify.Public) (pol KL : ByteArray) (layout : Option ByteArray) (m : Nat)
    (par : Par) : Prop where
  shape : X.y.fo = par.P.y.fo
  pc2 : VerifiableInference.Desc.K3.pieceAt X m false = 2
  pc7 : VerifiableInference.Desc.K3.pieceAt X m true = 7
  pubOf : Verify.publicOf pol KL layout = .ok X
  notHead : m ≠ (if X.p4 then 2 else 1) * X.NGr
  step : m % (if X.p4 then 2 else 1) = 0
  plan : X.G[m / (if X.p4 then 2 else 1)]? = some par.hp
  g : m = 2 * par.g
  y : par.P.y = X.y

end OnBytes.Road.K4
