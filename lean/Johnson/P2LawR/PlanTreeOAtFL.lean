-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/PlanTreeOAtFL.lean: THE LAST TABLE's TEST ON THE PLAN `PlanTreeO`
(Johnson/LLT25R/LastTreeO.lean), TO THE LETTER, AT ANOTHER NAME FOR THE PROOF FILE's
DESCRIPTION (FL o mk Z (seatK Z N) N c: Johnson/LLT25R/LastSeat.lean,
Johnson/LLT25R/LastRowZeroB.lean), AT (p14At Z).codes, (p14At Z).S AND D.t₁ + 1: FROM THE
DESCRIPTION's DATA AND ITS planOk. One call of Johnson/Desc/ProofFile/Law/OmegaTold.lean; that FL is
the description of which that file speaks is
shown by rfl.
IS IT EMPTY? As Johnson/Desc/ProofFile/Law/OmegaTold.lean's head says. Nothing on soundness.

-/
import Johnson.LLT25R.LastTreeO
import Johnson.LLT25R.LastRowZeroB
import Johnson.Desc.ProofFile.Law.OmegaTold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law
open VerifiableInference.Desc

/-- Something is told of that tree. -/
theorem told_FL (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (file : String) (D : OnBytes.Maker.WholeD)
    (hD : (LLT25.FL o mk Z (LLT25.seatK Z N) N c).data file = .ok D)
    (hp : (LLT25.FL o mk Z (LLT25.seatK Z N) N c).planOk = true) :
    ∃ o', (LLT25.FL o mk Z (LLT25.seatK Z N) N c).oracleAt (D.t₁ + 1) = some o' := by
  obtain ⟨o', h, -⟩ := Book.omega_told_at_proofFile o mk Z _ _ _ _ _ N _ _ c _ _ rfl file D hD hp
  exact ⟨o', h⟩

/-- **PlanTreeO at FL.** -/
theorem planTreeO_FL (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (file : String) (D : OnBytes.Maker.WholeD)
    (hD : (LLT25.FL o mk Z (LLT25.seatK Z N) N c).data file = .ok D)
    (hp : (LLT25.FL o mk Z (LLT25.seatK Z N) N c).planOk = true) :
    LLT25.PlanTreeO (LLT25.FL o mk Z (LLT25.seatK Z N) N c) (ToldDesc.p14At Z).codes
      (ToldDesc.p14At Z).S (D.t₁ + 1) :=
  Book.planTreeO_at_proofFile o mk Z _ _ _ _ _ N _ _ c _ _ rfl file D hD hp

end P2Law

#print axioms P2Law.told_FL
#print axioms P2Law.planTreeO_FL
