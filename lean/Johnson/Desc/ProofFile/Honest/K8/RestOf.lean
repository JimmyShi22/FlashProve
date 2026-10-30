-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/RestOf.lean: THE SMALLNESS TEST: `K8Rest`
(Johnson/Desc/ProofFile/Honest/K8/TestsSplit.lean: the guards of the verifier's three tests behind
the adding that are not among the kind's share) FROM A SHORTER LIST OF PREMISES: the clauses that
have a payer are paid inside. A gathering of Johnson/Desc/ProofFile/Honest/K8/RestLaid.lean,
Johnson/Desc/K8/Honest/BlocksCount.lean and Johnson/Desc/K8/Honest/RestPowers.lean. None of the
library's goals.

  **`k8Rest_of`**   PAID INSIDE, OF THE FOURTEEN CLAUSES: "as many kept slots as the window has" and
                   "the window is what was kept" (from: the kept slots are the ledger's own slice;
                   the window ends inside the ledger's coefficients) · "the two rows' weights are
                   the powers of the batching element", whole, and the first two of the eight
                   conjuncts of the shapes (from: the data's vectors of powers are the powers of the
                   ledger's batching element; the digits' array has its two last virtual rows; two
                   facts that keep other arrays apart from it; the data's blocks are the loop's, one
                   or two of them)
WHAT STAYS A PREMISE, AS THE VERIFIER's TEXT HAS IT: the lengths of the vectors · what the lookup
heard, the joining object and the wanted pieces are there · the first shapes · the pieces tile · the
points · six of the eight conjuncts of the shapes · the planes' weights · the reads' shape and
weights.
Limits. AN IMPLICATION: the ten premises that come in for the paid clauses are facts on the plan and
on what the run "K8.equations" has laid: none is shown here of an honest state. THE HEAVIEST: "the
data's vectors of powers are the powers of THE LEDGER's batching element", at the ledger at which
the tests are called: the run "K8.equations" lays these vectors at its own ledger's element: THAT
THE TWO LEDGERS HAVE ONE BATCHING ELEMENT, AND THAT NO RUN BETWEEN WRITES THE VECTORS, IS NOT SAID
HERE. Ten clauses and six conjuncts of an eleventh stay as they were.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.RestLaid
import Johnson.Desc.K8.Honest.BlocksCount
import Johnson.Desc.K8.Honest.RestPowers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open Fo (HasRow)
open OnBytes.Tie.Pv.Tail.Port (Powered)
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.K8.Honest (wants_blocks rest_powers rest_sizes)

/-- **`K8Rest` from what is left.** -/
theorem k8Rest_of {nU : Array Nat} {tl : HTailF2} {F : Fork} {g : Forest.Heard} {jo nbW : Nat}
    {W : List Want} (hls : tl.lsTail = F.LS.extract tl.slotA tl.slotB)
    (hin : tl.slotB ≤ F.LS.size) (hb : t2BL tl.tau = .ok tl.blocks) (b1 : tl.blocks.size ≠ 0)
    (b2 : tl.blocks.size ≤ 2) (hP : Powered tl F.theta) (hR : HasRow F tl.ix.ZZ tl.zzRowReads)
    (hT : HasRow F tl.ix.ZZ tl.zzRowTies) (hB : tl.ix.BZ ≠ tl.ix.ZZ)
    (hm : ∀ mu, mu < tl.NM → tl.gtTree.getD mu 0 ≠ tl.ix.ZZ)
    (r1 : (nU == tl.nUF) = true) (hg : tl.heard = some g) (hjo : tl.joinObj9 = some jo)
    (hW : tl.wants = some (nbW, W))
    (r4 : (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.size == 2 * nbW + 2 && tl.forestHeld g &&
      [0, 1].all (tl.callHeld g nbW)) = true)
    (r5 : tl.piecesTile (coefBody tl g F) W = true) (r6 : tl.pointsHeld g = true)
    (r7 : ((((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW + 1) {}).L.size ==
        2 * tl.mz &&
      tl.gamX.size == tl.NM && tl.gamV.size == tl.NM &&
      (List.range tl.NM).all (tl.tieShapeHeld (coefBody tl g F)) &&
      tl.shp.foldl (fun n s => n + s.m) 0 == tl.mz &&
      tl.planesShapeHeld (coefBody tl g F) g) = true)
    (r9 : tl.planesWeightsHeld (coefBody tl g F) g jo = true)
    (r10 : tl.readShapeHeld
      (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW) {}).L = true)
    (r11 : tl.readWeightsHeld (coefBody tl g F)
      (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW) {}).L = true) :
    K8Rest nU tl F := by
  have hn : nbW = tl.zzBlocks := wants_blocks tl hb b1 b2 nbW W hW
  have s2 : (tl.lsTail.size == tl.slotB - tl.slotA) = true := by
    rw [hls]
    exact size_laid tl F hin
  have s3 : selfSlots tl F = true := by
    unfold selfSlots
    rw [hls]
    exact beq_self_eq_true _
  have s7 := rest_sizes tl g F nbW hP hR hT hB hm hn
  have s8 := rest_powers tl g F nbW hP hR hT hB hm hn
  refine ⟨r1, s2, s3, g, jo, nbW, W, hg, hjo, hW, r4, r5, r6, ?_, s8, r9, r10, r11⟩
  simp only [Bool.and_eq_true] at s7 r7 ⊢
  obtain ⟨⟨⟨⟨⟨c3, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩ := r7
  exact ⟨⟨⟨⟨⟨⟨⟨s7.1, s7.2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.k8Rest_of
