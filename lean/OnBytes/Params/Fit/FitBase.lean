-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/FitBase.lean: what the laws on the sub-proofs' routines (FitSub.lean in this
folder) ask of the planner's own routines holds at the property Small, under the caps on the
setting.

Main name: subBase_small : SetCap s → SubBase s Small.
Limits: nothing beyond FitSmall.lean's seven laws that it gathers.
The program does not import this file.

-/
import OnBytes.Params.Fit.FitSmall
import OnBytes.Params.Fit.FitSub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params

theorem subBase_small {s : Setting} (S : SetCap s) : SubBase s Small where
  psc := keeps_psc
  lookup := keeps_lookup S
  zero := keeps_zero
  join := keeps_join
  line := keeps_line
  batSigma := keeps_batSigma
  rng := keeps_rng S

end OnBytes.Params

#print axioms OnBytes.Params.subBase_small
