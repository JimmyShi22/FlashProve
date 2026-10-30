-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoFixedUSAtt.lean.
The attention sub-proof's claims: Fo.FixedUS (OnBytes/Tie/Pv/Lookup/Ends/FoFixedUS.lean) in the
place of Fo.FixedU.

The statements are those of OnBytes/Tie/Pv/Lookup/Ends/FoFixedUAtt.lean, one for one, with
Fo.FixedUS in the place of Fo.FixedU and the tactic `fixedus` in the place of `fixedu`; what is
asked of the records, and the instances, are that file's. The limits of Fo.Fixed, Fo.FixedU and
Fo.FixedUS stand here too.

Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed here that a heard record is good: for the records of the checks' own runs that is
good_aHeard and good_hRun (OnBytes/Tie/Pv/Lookup/Ends/FoRetJoin.lean).

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoFixedUSLook
import OnBytes.Tie.Pv.Lookup.Ends.FoFixedUAtt

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Attention

variable {t0 : ℕ}

theorem fixedUS_u3at (h : Attention.Heard) (t i : ℕ) : FixedUS h.iU3 (u3at h t i) := by fixedus

macro_rules | `(tactic| fixedus_rule) => `(tactic| with_reducible exact fixedUS_u3at _ _ _)

theorem fixedUS_claim3 (h : Attention.Heard) [Good h.iU3 h] (j : Joins) [Good h.iU3 j] :
    FixedUS h.iU3 (claim3 h j) := by fixedus
theorem fixedUS_claim4 (h : Attention.Heard) [Good h.iU3 h] (j : Joins) [Good h.iU3 j] :
    FixedUS h.iU3 (claim4 h j) := by fixedus
theorem fixedUS_claim5 (h : Attention.Heard) [Good h.iU3 h] (j : Joins) [Good h.iU3 j] :
    FixedUS h.iU3 (claim5 h j) := by fixedus
theorem fixedUS_claim6 (h : Attention.Heard) [Good h.iU3 h] : FixedUS h.iU3 (claim6 h) := by fixedus
theorem fixedUS_claim7 (h : Attention.Heard) [Good h.iU3 h] : FixedUS h.iU3 (claim7 h) := by fixedus
theorem fixedUS_claim8 (h : Attention.Heard) [Good h.iU3 h] : FixedUS h.iU3 (claim8 h) := by fixedus
theorem fixedUS_allJoined (t0 : ℕ) (j : Joins) : FixedUS t0 (allJoined j) := by fixedus
theorem fixedUS_paddingLaidA (t0 : ℕ) (S : Shape) (g : Forest.Heard) :
    FixedUS t0 (Attention.paddingLaid S g) := by fixedus

macro_rules | `(tactic| fixedus_rule) => `(tactic| with_reducible first
  | exact fixedUS_claim3 _ _ | exact fixedUS_claim4 _ _ | exact fixedUS_claim5 _ _
  | exact fixedUS_claim6 _ | exact fixedUS_claim7 _ | exact fixedUS_claim8 _
  | exact fixedUS_allJoined _ _ | exact fixedUS_paddingLaidA _ _ _
  | exact fixedUS_objects _ | exact fixedUS_join _ _
  | refine fixedUS_planeLins _ _ _ _ ?_ ?_)

/-- **All claims of the attention sub-proof.** -/
theorem fixedUS_claims (P : Plan) (h : Attention.Heard) [Good h.iU3 h] :
    FixedUS h.iU3 (Attention.claims P h) := by fixedus

end Fo
