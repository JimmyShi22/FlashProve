-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K2RowFull.lean: AN ADDITION TO Johnson/AtFull/Desc/Lots/K2Row.lean: the
code switch's lot's row ON THE WRITTEN SKELETONS OF ProofFile.Sk.Full
(Johnson/Desc/ProofFile/Law/Skel/Full/Data.lean): so that a law on the description's back can
spend the row as one equation of plain data. NO BLOCK IMPORTS THIS FILE.
  k2SkelW_full    BY LEAN's KERNEL: the written rows k2SkelW (six fields cut out of cutFirstFull;
                  planOk := true and the two empty lists are K2Row.lean's own constants) are
                  ProofFile.Sk.Full.lot2Blocks, sign for sign
  k2_lotSk_full   K2Row's eight hypotheses (hc hz t1 t2 t3 t4 t5 hH) ⟹ lotSk G (k2Pure Zq) has
                  these blocks
  k2_lotW_full    the same eight ⟹ lotW as ls (lotSk G (k2Pure Zq)) = ProofFile.Sk.Full.lot2, AT ALL
                  LISTS as OF ASKED PLACES AND ls OF SEGMENTS' NUMBERS: the lot supplies no
                  batching, no test after a list, no tests
  k2SkelW_bent    A FACT, NO TEST, BY THE KERNEL: without its first row k2SkelW is not that list.
                  ONCE k2SkelW_full HOLDS IT COULD NOT HAVE COME OUT OTHERWISE: a list that is not
                  empty is not itself less its first row
LIMITS. Both written lists come off prints of the very code that they describe (their own heads
say so): neither is an independent witness of the other's source. The eight hypotheses stay owed
(K2Row.lean's head). No soundness is claimed.
-/
import Johnson.AtFull.Desc.Lots.K2Row
import Johnson.Desc.ProofFile.Law.Skel.Full.Data

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.K2
open P1K2
open ProofFile (Pub Ground)
open ProofFile.Sk (lotSk lotW)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First.K2 (headPlanOk)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.AtFull.Cut (cutWritten)

set_option maxRecDepth 1000000 in
theorem k2SkelW_full : k2SkelW = ProofFile.Sk.Full.lot2Blocks := by decide +kernel

set_option maxRecDepth 1000000 in
theorem k2SkelW_bent : k2SkelW.drop 1 ≠ ProofFile.Sk.Full.lot2Blocks := by decide +kernel

theorem k2_lotSk_full {Zq : Pub} {G : Ground} (hc : Zq.cuts = cutWritten)
    (hz : Zq.p.chains.made.sized.proof = proofSizedFull)
    (t1 : proofSizedFull.request = G.first.shape) (t2 : proofSizedFull.codes = G.first.codes)
    (t3 : Zq.s₀.st.codes = proofSizedFull.codes)
    (t4 : Zq.s₀.check.frame.shape = proofSizedFull.request)
    (t5 : proofSizedFull.set.samples = Zq.P.samples)
    (hH : (pureLetters G 24).map headPlanOk = some true) :
    lotSk G (ProofFile.k2Pure Zq) =
      { name := "the code switch", letters := false, still := []
        blocks := ProofFile.Sk.Full.lot2Blocks
        batch := fun _ => none, each := fun _ => false, tests := fun _ => false } := by
  rw [k2_lotSk hc hz t1 t2 t3 t4 t5 hH, k2SkelW_full]

theorem k2_lotW_full {Zq : Pub} {G : Ground} (hc : Zq.cuts = cutWritten)
    (hz : Zq.p.chains.made.sized.proof = proofSizedFull)
    (t1 : proofSizedFull.request = G.first.shape) (t2 : proofSizedFull.codes = G.first.codes)
    (t3 : Zq.s₀.st.codes = proofSizedFull.codes)
    (t4 : Zq.s₀.check.frame.shape = proofSizedFull.request)
    (t5 : proofSizedFull.set.samples = Zq.P.samples)
    (hH : (pureLetters G 24).map headPlanOk = some true) (as : List Place) (ls : List Nat) :
    lotW as ls (lotSk G (ProofFile.k2Pure Zq)) = ProofFile.Sk.Full.lot2 := by
  rw [k2_lotSk_full hc hz t1 t2 t3 t4 t5 hH]
  simp [lotW, ProofFile.Sk.Full.lot2, ProofFile.Sk.Full.lot2Batch]

end Johnson.AtFull.Lots.K2

#print axioms Johnson.AtFull.Lots.K2.k2SkelW_full
#print axioms Johnson.AtFull.Lots.K2.k2SkelW_bent
#print axioms Johnson.AtFull.Lots.K2.k2_lotSk_full
#print axioms Johnson.AtFull.Lots.K2.k2_lotW_full
