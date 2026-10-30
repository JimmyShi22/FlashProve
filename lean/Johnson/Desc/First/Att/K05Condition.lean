-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Condition.lean: kind K5: the proved chain's condition at a plan's numbers:
the
general half, proved; the numeric half, one decidable equation on the plan's record.

Main names:
  `AtPlan P p`: four variables number a bit (P.kap = 4), and the plan's record of the place is the
    record
    made of the description's sizes (recOf P p.own.rows = p.own).
  `K05_condition`: under AtPlan, for the letters P.own (theMeans …): (1) knowledge soundness of the
    chain's
    reduction from "Dn and Todo" to "Last Dn", at every incoming joint, whose condition is carried
      through
    unturned, with the chain's errors (ownAt_knowAt: it has no further condition); (2) the
      reduction's shape
    is an instance of the kind's rounds; (3) the list of errors is errOf z over them, with
    z = v |K|^(v - 1) at the draw of the point, v = 2 lgk + 2 lt + 4 its coordinates; (4) z |K| = v
      |K|^v;
    (5) at v, errOf gives the library's attNums.
  `smallRecord`, `atPlan_small`; `fullRecord`, `atPlan_full`: AtPlan is met at the records of the
    small and
    of the full-size stored configuration; at the latter the sizes are the library's Dim.ref.

Limits. P is a parameter here: its entries, its reading of the cells, the places of the mask entries
and
the three free linear claims are given by whoever lays the segment (Att/K05Caller.lean goes
further). The
two records are typed here from a print of the planner's output; that the planner returns them is
not shown in this file or in what it imports. The print was made on another build's stored files;
that the planner as released gives the same
records has not been checked. They speak of two stored configurations alone, not of every
configuration in
scope.
Sources: Cb/Pv/Att/OwnAt.lean (theMeans, ownAt_knowAt); OnBytes/Tie/Pv/Att/OwnAtFits.lean (recOf,
ownAt_fits,
ownAt_nums); OwnShape.lean (zero_ratio); and what Att/K05Rounds.lean names.
Nothing is claimed on completeness or hiding.

-/
import Cb.Pv.Att.OwnAt
import OnBytes.Tie.Pv.Att.OwnAtFits
import Johnson.Desc.First.Att.K05Rounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole IOR OnBytes OnBytes.Model Cb.Pv.Att
open OnBytes.Tie.Pv.Att (recOf ownAt_fits ownAt_nums zero_ratio)

variable {K M X : Type} [Field K] [Fintype K]

/-- **The numeric condition**: the plan's record of the place is the record made of the
description's sizes. -/
structure AtPlan (P : OwnPar K M X) (p : Par) : Prop where
  kap : P.kap = 4
  record : recOf P p.own.rows = p.own

/-- **K05_condition**, the general half. -/
theorem K05_condition (P : OwnPar K M X) (p : Par) (h : AtPlan P p) :
    (∀ (Kc X0 Wp : Type) (Ex : ExtSpec) (A0 : Rels Kc X0 Ex (M × Wp)) (pr : X → X0) (Dn : X → M → Prop),
      KnowAt ((P.own (theMeans K P.D P.C P.kap)).ch.R Ex)
        (jt A0 pr fun x m => Dn x m ∧ (P.own (theMeans K P.D P.C P.kap)).ch.Todo x m)
        (jt A0 (fun e => pr ((P.own (theMeans K P.D P.C P.kap)).ch.back e))
          ((P.own (theMeans K P.D P.C P.kap)).ch.Last Dn))
        (fun _ _ _ wp => wp) ((P.own (theMeans K P.D P.C P.kap)).ch.eps Ex)) ∧
    (∀ Ex : ExtSpec, OnBytes.G4.ShapeIs K ((P.own (theMeans K P.D P.C P.kap)).ch.R Ex).shape
      ((rounds p).map (·.entry))) ∧
    (∀ Ex : ExtSpec, errList ((P.own (theMeans K P.D P.C P.kap)).ch.eps Ex) = ((rounds p).map (·.entry)).map
      (errOf ((2 * p.own.lgk + 2 * p.own.lt + 4) * Fintype.card K ^ (2 * p.own.lgk + 2 * p.own.lt + 4 - 1)))) ∧
    (2 * p.own.lgk + 2 * p.own.lt + 4) * Fintype.card K ^ (2 * p.own.lgk + 2 * p.own.lt + 4 - 1) * Fintype.card K =
      (2 * p.own.lgk + 2 * p.own.lt + 4) * Fintype.card K ^ (2 * p.own.lgk + 2 * p.own.lt + 4) ∧
    ((rounds p).map (·.entry)).map (errOf (2 * p.own.lgk + 2 * p.own.lt + 4)) =
      OnBytes.Tie.Pv.Att.Plan.attNums p.own := by
  have hf : OnBytes.Tie.Pv.Att.OwnFits (P.own (theMeans K P.D P.C P.kap)) p.own := by
    rw [← h.record]
    exact ownAt_fits P _ h.kap _
  have hv : P.g1 + P.g2 = 2 * p.own.lgk + 2 * p.own.lt + 4 := by
    rw [← h.record]
    show P.D.lg + P.D.lT + (P.kap + P.D.lg + P.D.lT) = 2 * P.D.lg + 2 * P.D.lT + 4
    rw [h.kap]
    omega
  refine ⟨fun Kc X0 Wp Ex A0 pr Dn => ownAt_knowAt P Ex A0 pr Dn, fun Ex => (K05_rounds _ p hf Ex).1, fun Ex => ?_,
    zero_ratio _ _ (by omega), (K05_rounds _ p hf extNone).2.2⟩
  rw [(K05_rounds _ p hf Ex).2.1, ← hv]
  rfl

/-! ## The numeric condition at the small stored configuration -/

/-- The planner's record of an attention segment's own rounds at the small stored configuration
(both segments alike), typed
from a print of the planner's output on its three public configuration files. -/
def smallRecord : Params.AttentionRounds :=
  { lt := 6, lgk := 1, pairs := 8, Lam := 4, planeMessages := 2, score := [(11, 8), (10, 8)], e := 7, valueM := 8,
    valueD := 7, attained := 14, bits := 11, rows := 2074535 }

/-- **The numeric condition is met at the small plan**: at the description's sizes lg lP lB ln na nl
= 1 1 4 7 2 4 (the plan's
shape's lgk · log hP · lB · ldh · HA · Lam), two plane messages and four variables for a bit's
number. u0 is read by no
number of the record. -/
theorem atPlan_small (P : OwnPar K M X) (u0 : ℕ) (hD : P.D = ⟨1, 1, 4, 7, 2, 4, u0⟩) (hn : P.npl = 2) (hk : P.kap = 4)
    (p : Par) (hp : p.own = smallRecord) : AtPlan P p := by
  refine ⟨hk, ?_⟩
  rw [hp]
  unfold recOf
  rw [hD, hn, hk]
  rfl

/-! ## The numeric condition at the full-size plan -/

/-- The planner's record of an attention segment's own rounds at the full-size stored configuration
(twelve attention plans,
all twelve alike), typed from a print of the planner's output on its three public configuration
files. -/
def fullRecord : Params.AttentionRounds :=
  { lt := 10, lgk := 3, pairs := 20, Lam := 4, planeMessages := 2, score := [(17, 20), (14, 20)], e := 13, valueM := 16,
    valueD := 13, attained := 20, bits := 17, rows := 14166783 }

/-- **The numeric condition is met at the full-size plan**: at the description's sizes lg lP lB ln
na nl = 3 3 6 7 5 4: the
library's own reference sizes (Inst/Model/Att/Index.lean: Dim.ref, whatever its u0), two plane
messages and four variables
for a bit's number. -/
theorem atPlan_full (P : OwnPar K M X) (u0 : ℕ) (hD : P.D = ⟨3, 3, 6, 7, 5, 4, u0⟩) (hn : P.npl = 2) (hk : P.kap = 4)
    (p : Par) (hp : p.own = fullRecord) : AtPlan P p := by
  refine ⟨hk, ?_⟩
  rw [hp]
  unfold recOf
  rw [hD, hn, hk]
  rfl

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.atPlan_full
#print axioms VerifiableInference.Desc.First.Att.P.atPlan_small
#print axioms VerifiableInference.Desc.First.Att.P.K05_condition
