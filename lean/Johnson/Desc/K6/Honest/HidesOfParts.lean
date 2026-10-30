-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/HidesOfParts.lean: THE OUTPUT HEAD'S OWN ROUNDS, THE HONEST PROVER'S SIDE:
FROM WHAT EACH OF THE SIX PARTS THAT SEND SCALARS LEAVES TO THE STRUCTURE HidesTables
(TruthOfTables.lean).
WHAT IT IS NOT. No prover, no round, no coin, no hearing: EVERY PREMISE IS A SENTENCE ON A WORLD,
and that any ledger meets them is not shown here. Nothing on whether the verifier accepts, on
soundness, on completeness or on what a proof hides. Equations in the field K. Mathlib and
Johnson/Desc/Kinds/Law/ are in the closure of its imports.
WHAT IT IS. At all sizes. CONDITIONAL on fourteen premises and two sizes. The premises have the
forms in which LaidLaw.lean's batch_truth and ProofFile/Honest/K6/SumTruth.lean's level_truth and
sumcheck_truth end, at the four sums of Tables.lean:
  w, p            the nine and the seven hidden scalars' variables are worth Tables.lean's values;
  ..2             a claimed sum's variable is worth the claimed sum of Tables.lean;
  ..3             an end value's variable is worth the sum's end value at the challenges heard;
  ..4             IF the start form (the claimed sum) is worth (reads as) the sum's total, THEN for
                  every S0 that reads as the summand on what is shown the sumcheck's own form is
                  worth 0.
WHAT IS DONE HERE. The four "if" are paid: for the squares by start_at_truth (Law/NormEnds.lean) on
the nine scalars with sqTotal_reads; for the three others by TablesLaw.lean's readings of lead and
total. The four S0 of the verifier's text are shown to read as the summands: product_on, summand_on
(LaidLaw.lean). A default of getD is turned (getD_zero).

-/
import Mathlib
import Johnson.Desc.K6.Honest.TruthOfTables
import Johnson.Desc.K6.Honest.LaidLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Honest

open OnBytes (E okE zeroE)
open OnBytes.Model (Fork)
open Norm (lt ls d lPd T S2)
open Law (K rd worldE noEnt)
open Law.Came (val)

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In]

/-- **FROM THE SIX PARTS TO THE STRUCTURE.** -/
theorem hides_of_parts (c : Law.NCells) (mask : Nat → E) (H : HeardAll) (G : Fork)
    (sPV : H.1.pV.size = lt) (hzt : (FinalNorm.zt).size = lt)
    (w : ∀ s, s < 9 → val (worldE G mask noEnt) (H.1.W.getD s {}).var =
      rd ((wScalars c H.1.pV).getD s 0))
    (p : ∀ n, n < 7 → val (worldE G mask noEnt) (H.1.P.getD n {}).var =
      rd ((pScalars c H.1.pV).getD n 0))
    (sq3 : ∀ j, j < 2 → val (worldE G mask noEnt) (H.1.squares.end_ j).var =
      rd (((sqSum c H.1.pV H.1.gam).ends H.1.squares.r.toList).getD j zeroE))
    (sq4 : val (worldE G mask noEnt) (Norm.squaresStart H.1.W H.1.gam #[]) =
        rd (sqSum c H.1.pV H.1.gam).total →
      ∀ S0 : E, rd S0 = (sqSum c H.1.pV H.1.gam).onK (fun j => rd (H.1.squares.end_ j).shown) →
        val (worldE G mask noEnt) (H.1.squares.left S0) = 0)
    (pr2 : val (worldE G mask noEnt) H.1.products.claimed.var = rd (prLead c H.1.pV H.1.om))
    (pr3 : ∀ q, q < 4 → val (worldE G mask noEnt) (H.1.products.end_ q).var =
      rd (((prSum c H.1.pV H.1.om).ends H.1.products.r.toList).getD q zeroE))
    (pr4 : rd (prLead c H.1.pV H.1.om) = rd (prSum c H.1.pV H.1.om).total →
      ∀ S0 : E, rd S0 = (prSum c H.1.pV H.1.om).onK (fun j => rd (H.1.products.end_ j).shown) →
        val (worldE G mask noEnt) (H.1.products.left S0) = 0)
    (nm2 : val (worldE G mask noEnt) H.2.1.normed.claimed.var = rd (nmLead c))
    (nm3 : ∀ j, j < 2 → val (worldE G mask noEnt) (H.2.1.normed.end_ j).var =
      rd (((nmSum c).ends H.2.1.normed.r.toList).getD j zeroE))
    (nm4 : rd (nmLead c) = rd (nmSum c).total →
      ∀ S0 : E, rd S0 = (nmSum c).onK (fun j => rd (H.2.1.normed.end_ j).shown) →
        val (worldE G mask noEnt) (H.2.1.normed.left S0) = 0)
    (lg2 : val (worldE G mask noEnt) H.2.2.logits.claimed.var = rd (lgLead c.toCells))
    (lg3 : ∀ j, j < 2 → val (worldE G mask noEnt) (H.2.2.logits.end_ j).var =
      rd (((lgSum c.toCells).ends H.2.2.logits.r.toList).getD j zeroE))
    (lg4 : rd (lgLead c.toCells) = rd (lgSum c.toCells).total →
      ∀ S0 : E, rd S0 = (lgSum c.toCells).onK (fun j => rd (H.2.2.logits.end_ j).shown) →
        val (worldE G mask noEnt) (H.2.2.logits.left S0) = 0)
    (ok1 : okE (H.2.2.logits.end_ 1).var.const = true) :
    HidesTables c mask H G where
  w := w
  p := p
  sqRow := sq4
    ((Law.start_at_truth c H.1.pV sPV H.1.gam H.1.W (worldE G mask noEnt) fun s hs => by
      rw [w s hs, wScalars_reads c H.1.pV sPV s hs, sumWAt_tuple]).trans
      (sqTotal_reads c H.1.pV H.1.gam).symm) _
    (product_on (sqSum c H.1.pV H.1.gam) rfl fun j => (H.1.squares.end_ j).shown)
  sqEnd := fun j hj => (sq3 j hj).trans (Law.getD_zero _ _).symm
  prClaimed := pr2
  prRow := pr4
    ((prLead_reads c H.1.pV H.1.om sPV).trans (prTotal_reads c H.1.pV H.1.om).symm) _
    (summand_on c H.1.pV H.1.om fun j => (H.1.products.end_ j).shown)
  prEnd := fun q hq => (pr3 q hq).trans (Law.getD_zero _ _).symm
  nmClaimed := nm2
  nmRow := nm4 ((nmLead_reads c hzt).trans (nmTotal_reads c).symm) _
    (product_on (nmSum c) rfl fun j => (H.2.1.normed.end_ j).shown)
  nmEnd := fun j hj => (nm3 j hj).trans (Law.getD_zero _ _).symm
  lgClaimed := lg2
  lgRow := lg4 ((lgLead_reads c.toCells hzt).trans (lgTotal_reads c.toCells).symm) _
    (product_on (lgSum c.toCells) rfl fun j => (H.2.2.logits.end_ j).shown)
  lgEnd := fun j hj => (lg3 j hj).trans (Law.getD_zero _ _).symm
  ok1 := ok1

end VerifiableInference.Desc.Kinds.Head.Honest

#print axioms VerifiableInference.Desc.Kinds.Head.Honest.hides_of_parts
