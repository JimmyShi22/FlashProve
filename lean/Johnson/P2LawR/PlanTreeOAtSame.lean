-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/PlanTreeOAtSame.lean: THE LAST TABLE's TEST ON THE PLAN `PlanTreeO`
(Johnson/LLT25R/LastTreeO.lean) AT EVERY DESCRIPTION G THAT TELLS WHAT THE PROOF FILE's OWN
DESCRIPTION TELLS. PlanOk₃'s field planTreeO stands at a letter G; Johnson/P2LawR/PlanTreeOAtFL.lean
has the test at FL … alone.
Here: three equations of make carry it to G. Two theorems.


  oracleAt_same      G.oracleAt n = F.oracleAt n, where the three chains of G tell what the three
                     chains of F tell (oraclesOf …, chain by chain).
  planTreeO_of_same  PlanTreeO G (p14At Z).codes (p14At Z).S (D.t₁ + 1), from FL's data and planOk
                     (PlanOk₃'s dataIs and planOk) and these three equations at F := FL ….
IS IT EMPTY? At G := FL …, its unpulled form, or a pull of it, the three equations are meant to be
rfl (FileDescription.pull keeps the three chains). Nothing is evaluated here. Nothing on soundness.

-/
import Johnson.P2LawR.PlanTreeOAtFL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law
open VerifiableInference.Desc

/-- Two descriptions whose chains tell the same tell the same of every tree. -/
theorem oracleAt_same {Xi Xi' : Type} (G : FileDescription Xi') (F : FileDescription Xi)
    (h1 : oraclesOf G.first.blocksInOrder = oraclesOf F.first.blocksInOrder)
    (h2 : oraclesOf G.shared.blocksInOrder = oraclesOf F.shared.blocksInOrder)
    (h3 : oraclesOf G.second.blocksInOrder = oraclesOf F.second.blocksInOrder) (n : Nat) :
    G.oracleAt n = F.oracleAt n := by
  unfold FileDescription.oracleAt
  rw [h1, h2, h3]

/-- **PlanTreeO at every description that tells what FL tells.** -/
theorem planTreeO_of_same {Xi' : Type} (G : FileDescription Xi') (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy)
    (Z : ProofFile.Pub) (N : H2U.Places4) (c : Chain First.S ProofFile.Cl) (D : OnBytes.Maker.WholeD)
    (hD : ∃ file, (LLT25.FL o mk Z (LLT25.seatK Z N) N c).data file = .ok D)
    (hp : (LLT25.FL o mk Z (LLT25.seatK Z N) N c).planOk = true)
    (h1 : oraclesOf G.first.blocksInOrder = oraclesOf (LLT25.FL o mk Z (LLT25.seatK Z N) N c).first.blocksInOrder)
    (h2 : oraclesOf G.shared.blocksInOrder = oraclesOf (LLT25.FL o mk Z (LLT25.seatK Z N) N c).shared.blocksInOrder)
    (h3 : oraclesOf G.second.blocksInOrder = oraclesOf (LLT25.FL o mk Z (LLT25.seatK Z N) N c).second.blocksInOrder) :
    LLT25.PlanTreeO G (ToldDesc.p14At Z).codes (ToldDesc.p14At Z).S (D.t₁ + 1) := by
  obtain ⟨file, hD⟩ := hD
  intro lay hl o' ho
  rw [oracleAt_same G _ h1 h2 h3] at ho
  exact planTreeO_FL o mk Z N c file D hD hp lay hl o' ho

end P2Law

#print axioms P2Law.oracleAt_same
#print axioms P2Law.planTreeO_of_same
