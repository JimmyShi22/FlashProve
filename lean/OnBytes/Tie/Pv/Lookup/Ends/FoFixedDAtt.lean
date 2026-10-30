-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoFixedDAtt.lean.
The attention sub-proof's claims: the value and the list of added claims as data.

The statements of OnBytes/Tie/Pv/Lookup/Ends/FoFixedUSAtt.lean, one for one, with `FixedD`
(OnBytes/Tie/Pv/Lookup/Ends/FoFixedD.lean) in the place of `FixedUS`: each is a definition, made by
the tactic `fixedd`. What is asked of the records, and the instances, are those of
OnBytes/Tie/Pv/Lookup/Ends/FoFixedUAtt.lean. `fixedD_claims P h` holds the value and the list of
Attention.claims P h. It asks that the record h is good, and nothing of the key forms between the
claims: the rule for a bind takes that from the law of the routine before.

Limits: those of OnBytes/Tie/Pv/Lookup/Ends/FoFixedD.lean. The list is that of Attention.claims
alone: behind it the attention check adds the smallness test's claims too. No statement says what
the list is, member by member, nor that it is the rows, A, the join's form, B and the planes' three
of Fo.AttBaseW (OnBytes/Tie/Pv/Lookup/Ends/FoBaseWhole.lean);
OnBytes/Tie/Pv/Lookup/Test/TestFoFixedD.lean computes claim 3's list at one made-up record.
Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed here that a heard record is good: for the records of the checks' own runs that is
good_aHeard (OnBytes/Tie/Pv/Lookup/Ends/FoRetJoin.lean).

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoFixedDLook
import OnBytes.Tie.Pv.Lookup.Ends.FoFixedUAtt

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Attention

variable {t0 : ℕ}

def fixedD_u3at (h : Attention.Heard) (t i : ℕ) : FixedD h.iU3 (u3at h t i) := by fixedd

macro_rules | `(tactic| fixedd_rule) => `(tactic| with_reducible exact fixedD_u3at _ _ _)

def fixedD_claim3 (h : Attention.Heard) [Good h.iU3 h] (j : Joins) [Good h.iU3 j] :
    FixedD h.iU3 (claim3 h j) := by fixedd
def fixedD_claim4 (h : Attention.Heard) [Good h.iU3 h] (j : Joins) [Good h.iU3 j] :
    FixedD h.iU3 (claim4 h j) := by fixedd
def fixedD_claim5 (h : Attention.Heard) [Good h.iU3 h] (j : Joins) [Good h.iU3 j] :
    FixedD h.iU3 (claim5 h j) := by fixedd
def fixedD_claim6 (h : Attention.Heard) [Good h.iU3 h] : FixedD h.iU3 (claim6 h) := by fixedd
def fixedD_claim7 (h : Attention.Heard) [Good h.iU3 h] : FixedD h.iU3 (claim7 h) := by fixedd
def fixedD_claim8 (h : Attention.Heard) [Good h.iU3 h] : FixedD h.iU3 (claim8 h) := by fixedd
def fixedD_allJoined (t0 : ℕ) (j : Joins) : FixedD t0 (allJoined j) := by fixedd
def fixedD_paddingLaidA (t0 : ℕ) (S : Shape) (g : Forest.Heard) :
    FixedD t0 (Attention.paddingLaid S g) := by fixedd

macro_rules | `(tactic| fixedd_rule) => `(tactic| with_reducible first
  | exact fixedD_claim3 _ _ | exact fixedD_claim4 _ _ | exact fixedD_claim5 _ _
  | exact fixedD_claim6 _ | exact fixedD_claim7 _ | exact fixedD_claim8 _
  | exact fixedD_allJoined _ _ | exact fixedD_paddingLaidA _ _ _
  | exact fixedD_objects _ | exact fixedD_join _ _
  | refine fixedD_planeLins _ _ _ _ ?_ ?_)

/-- **All claims that Attention.claims adds.** -/
def fixedD_claims (P : Plan) (h : Attention.Heard) [Good h.iU3 h] :
    FixedD h.iU3 (Attention.claims P h) := by fixedd

end Fo
