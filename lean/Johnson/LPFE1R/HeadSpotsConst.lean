-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/LPFE1R/HeadSpotsConst.lean: K9Left's CLOSED CONJUNCT "∃ nH, HeadSpots Zp nH"
(P5J/K09Left.lean) AT THE CLOSED CONSTANT, FROM THE HEAD ALONE. One statement: a joining of
four theorems that lie.

  headSpots_at     (h : AtMgA secondHashFunction Z D r Zp Np cF x) : ∃ nH, HeadSpots Zp nH:
                   LPFE1R/HeadSpotsAt.lean's headSpots_of_fit at: H2K12.spots_atAll (the named
                   test spotsFitB accepts: under the head and the written cut) ·
                   P5J.pins_of_laid's second half (the first chain's cut is the written one: rows 9
                   and 10 of the entry tests) · P1K2.links25_atAll ·
                   P5J.AtMg.kind24

Limits. The head is a premise: a member of it is proved at storedPublicFiles and zGap alone (at secondHashFunction; side
library AtFullSide/Top/). spots_atAll's own limits hold: its test
accepts an empty or short list; the written cut rests on prints of the evaluator. The full size
alone; the concrete second hash function alone. No soundness statement.

-/
import Johnson.LPFE1R.HeadSpotsAt
import Johnson.Loose.H2K12.SpotsAtAll
import Johnson.Top.H0.Opts.Links25AtHead
import Johnson.P5T.Kind24AtMg
import Johnson.Goal.Skeleton.PinsOfLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open OnBytes OnBytes.Maker
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.LinkJoin (HeadSpots headSpots_of_fit)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **HeadSpots at the closed constant, from the head alone.** -/
theorem headSpots_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : ∃ nH, HeadSpots Zp nH :=
  ⟨_, headSpots_of_fit (H2K12.spots_atAll h (pins_of_laid h.scope h.laid).2)
    (P1K2.links25_atAll h) h.toAtMg.kind24⟩

end P5J

#print axioms P5J.headSpots_at
