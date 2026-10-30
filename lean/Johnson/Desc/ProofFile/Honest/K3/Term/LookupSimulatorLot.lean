-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupSimulatorLot.lean: AT ANY FILLING. The kind "lookup"
(K3): the lookups' rows as a lot of rows with simulators (`SLot`, Honest/Thread/Rows.lean), and the
equation: forgetting the simulators gives the lot's honest side. Two definitions; theorems. General
in the filling, which may read the public part. No premise in any of them.

  `lookupSimulatorRow A s`        the row at a site: the place, each part with its simulator
                                  (`rowPairs`, Honest/K3/LotRow.lean), On and bud "true"
  `lookupSimulatorRowHalf`        its prover's side is the seated row at the site
  `lookupSimulatorLot F`          the lot of these rows, a row for each site of the public part
  `lookupSimulatorLotForgets`     (lookupSimulatorLot F).toHLot = rowLotAt F
  `lookupSimulatorRowOfLot`       a row of the lot is the row at one of the public part's sites
  `lookupSimulatorOnHolds`, `lookupSimulatorBudHolds`   On and bud hold of every row of the lot,
                                  everywhere

The simulators. Beside a stage with a sumcheck: `sumSim` (Honest/Sum.lean): as many coins of its own
as the call sends scalars, each output as it is. Beside a stage that sends nothing: one round in
which nothing is shown. Neither reads the public field, `front`, the challenges or the positions.

On and bud. Both are "true". In the field `exact` of `Good` (Honest/Side.lean) they are hypotheses,
so "true" asks the most of `exact`; in `Owed` (Honest/Owed.lean) they are conclusions, so "true"
asks nothing there (Honest/Law/OwedRule.lean, head, way 4: the two count only together, at one On
and one bud). `exact` at these two is `lookupRowIsExact` (LookupRowIsExactAndFresh.lean).

The sites of a public part (`lookSites`) are PLACES OF THE PROOF FILE ALONE (fifty under the
library's hypothesis at the full size): THE KEY FILE'S TWO LOOKUPS ARE NOT SPOKEN OF.

Limits. Equations between definitions. Of `Good` nothing is said here. Nothing on any property of
the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.RowsMore
import Johnson.Desc.ProofFile.Honest.K3.LotInst
import Johnson.Desc.ProofFile.Honest.K3.Law.Good.K3Lettered

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open ProofFile.Honest.K3.Law

variable {V W X Pb : Type}

/-- **The lookup's row with its simulators, at a site.** A: the filling. -/
def lookupSimulatorRow (A : Fill W) (s : Site) : Unlettered V W X Pb :=
  ⟨s.at_.place, rowPairs A s, fun _ _ _ _ => True, fun _ _ _ => True⟩

/-- Its prover's side is the seated row at the site. -/
theorem lookupSimulatorRowHalf (A : Fill W) (s : Site) :
    (lookupSimulatorRow (V := V) (X := X) (Pb := Pb) A s).half =
      ⟨s.at_.place, (proverSideOfLookupInChainAtOneOwner theReads (A.jobs s).asked (A.wit s) s.at_).parts⟩ :=
  congrArg (Placed.mk s.at_.place) (rowPairs_parts A s)

/-- **THE LOOKUPS' LOT OF ROWS WITH SIMULATORS**, at a filling that may read the public part. -/
def lookupSimulatorLot (F : Pub → Fill W) : SLot V W X Pb :=
  ⟨lotName, fun publicPart _ => (lookSites publicPart).map fun s => lookupSimulatorRow (F
      publicPart) s⟩

/-- **Forgetting the simulators gives the lot's honest side.** -/
theorem lookupSimulatorLotForgets (F : Pub → Fill W) :
    (lookupSimulatorLot (V := V) (X := X) (Pb := Pb) F).toHLot = rowLotAt F := by
  unfold SLot.toHLot lookupSimulatorLot rowLotAt rowLot lotBy
  congr 1
  funext publicPart _
  rw [List.map_map]
  exact List.map_congr_left fun s _ => lookupSimulatorRowHalf (F publicPart) s

/-- A row of the lot is the row at one of the public part's sites. -/
theorem lookupSimulatorRowOfLot (F : Pub → Fill W) (publicPart : Pub) (ground : Ground)
    (r : Unlettered V W X Pb) (inLot : r ∈ (lookupSimulatorLot F).rows publicPart ground) :
    ∃ s ∈ lookSites publicPart, r = lookupSimulatorRow (F publicPart) s := by
  obtain ⟨s, hs, e⟩ := List.mem_map.1 inLot
  exact ⟨s, hs, e.symm⟩

/-- **On holds of every row of the lot, everywhere.** -/
theorem lookupSimulatorOnHolds (F : Pub → Fill W) (publicPart : Pub) (ground : Ground)
    (r : Unlettered V W X Pb) (inLot : r ∈ (lookupSimulatorLot F).rows publicPart ground)
    (u : Member V W X Pb) (ca : CsAll u.part.carries) (m : Mid W X) (front : Before) :
    r.On u ca m front := by
  obtain ⟨s, _, rfl⟩ := lookupSimulatorRowOfLot F publicPart ground r inLot
  exact trivial

/-- **bud holds of every row of the lot, everywhere.** -/
theorem lookupSimulatorBudHolds (F : Pub → Fill W) (publicPart : Pub) (ground : Ground)
    (r : Unlettered V W X Pb) (inLot : r ∈ (lookupSimulatorLot F).rows publicPart ground) (n : Nat)
    (ds : List Fmt.Drawn) (asks : List (List (List Nat))) : r.bud n ds asks := by
  obtain ⟨s, _, rfl⟩ := lookupSimulatorRowOfLot F publicPart ground r inLot
  exact trivial

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.lookupSimulatorRow
#print axioms ProofFile.Honest.K3.Term.lookupSimulatorRowHalf
#print axioms ProofFile.Honest.K3.Term.lookupSimulatorLot
#print axioms ProofFile.Honest.K3.Term.lookupSimulatorLotForgets
#print axioms ProofFile.Honest.K3.Term.lookupSimulatorRowOfLot
#print axioms ProofFile.Honest.K3.Term.lookupSimulatorOnHolds
#print axioms ProofFile.Honest.K3.Term.lookupSimulatorBudHolds
