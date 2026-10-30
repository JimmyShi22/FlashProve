-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/TestsSplit.lean: THE SMALLNESS TEST: THE VERIFIER's THREE TESTS
BEHIND THE ADDING (`testsP`, Johnson/Desc/First/TailClaims/SelfRows.lean: what the run "K8.tests"
calls) RETURN WHEREVER THE KIND's SHARE OF THEM IS SILENT (`k8First`, `k8Second`,
Johnson/Desc/ProofFile/Honest/K8/Share.lean: the seven tests that ask "not 0" or "all different" of
weights) AND ALL THE OTHER GUARDS HOLD (`K8Rest`). A splitting of the verifier's own text in two; no
chance in it. None of the library's goals.

  `K8Rest nU tl F`   every guard of the three tests that is not among the share's seven, as the
                   verifier's text has it: the lengths of the vectors · the kept slots' size · the
                   window is what was kept · what the lookup heard, the joining object and the
                   wanted pieces are there · the shapes · the pieces tile · the points · the ties'
                   and planes' shapes · the two rows' weights are the powers of the batching element
                   · the planes' weights · the reads' shape and weights
  **`tests_of_share`**   k8First tl nU F = none → k8Second tl F = none → K8Rest nU tl F → ∃ Fc,
                   testsP nU tl F = .ok Fc
Limits. `K8Rest` IS A PREMISE: THAT AN HONEST RUN MEETS IT IS NOT SHOWN: it holds guards on public
numbers and five on values that ask "two computations agree" or "nothing has turned". One direction
alone.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.Share

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc.First.TailClaims

/-- Every guard of the three tests that is not among the share's seven. -/
def K8Rest (nU : Array Nat) (tl : HTailF2) (F : Fork) : Prop :=
  (nU == tl.nUF) = true ∧ (tl.lsTail.size == tl.slotB - tl.slotA) = true ∧
  selfSlots tl F = true ∧
  ∃ (g : Forest.Heard) (jo : Nat) (nbW : Nat) (W : List Want),
    tl.heard = some g ∧ tl.joinObj9 = some jo ∧ tl.wants = some (nbW, W) ∧
    (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.size == 2 * nbW + 2 && tl.forestHeld g &&
      [0, 1].all (tl.callHeld g nbW)) = true ∧
    tl.piecesTile (coefBody tl g F) W = true ∧ tl.pointsHeld g = true ∧
    ((((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW) {}).coef.size == tl.tau &&
      (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW + 1) {}).coef.size == tl.tau &&
      (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW + 1) {}).L.size == 2 * tl.mz &&
      tl.gamX.size == tl.NM && tl.gamV.size == tl.NM &&
      (List.range tl.NM).all (tl.tieShapeHeld (coefBody tl g F)) &&
      tl.shp.foldl (fun n s => n + s.m) 0 == tl.mz &&
      tl.planesShapeHeld (coefBody tl g F) g) = true ∧
    ((List.range tl.tau).all fun u =>
      (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW) {}).coef.getD u zeroE ==
          powE (coefBody tl g F).theta u &&
        (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW + 1) {}).coef.getD u zeroE ==
          (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW) {}).coef.getD u
            zeroE) = true ∧
    tl.planesWeightsHeld (coefBody tl g F) g jo = true ∧
    tl.readShapeHeld (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW) {}).L = true ∧
    tl.readWeightsHeld (coefBody tl g F)
      (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW) {}).L = true

/-- The share's first five, taken apart. -/
theorem first_none {tl : HTailF2} {nU : Array Nat} {F : Fork} (h : k8First tl nU F = none) :
    selfUnits tl nU F = true ∧ selfDigits tl F = true ∧ selfLinked tl F = true ∧
      selfPlanes tl F = true ∧ selfSymbols tl F = true := by
  cases e1 : selfUnits tl nU F <;> cases e2 : selfDigits tl F <;> cases e3 : selfLinked tl F <;>
    cases e4 : selfPlanes tl F <;> cases e5 : selfSymbols tl F <;>
    simp [k8First, e1, e2, e3, e4, e5] at h ⊢

/-- **The three tests return where the share is silent and the rest holds.** -/
theorem tests_of_share {nU : Array Nat} {tl : HTailF2} {F : Fork} (h1 : k8First tl nU F = none)
    (h2 : k8Second tl F = none) (R : K8Rest nU tl F) : ∃ Fc, testsP nU tl F = .ok Fc := by
  obtain ⟨r1, r2, r3, g, jo, nbW, W, hg, hjo, hW, r4, r5, r6, r7, r8, r9, r10, r11⟩ := R
  obtain ⟨a1, a2, a3, a4, a5⟩ := first_none h1
  have hc : coefficientsP tl F = .ok (coefBody tl g F) := by
    unfold coefficientsP
    rw [hg]
  have hb : W.all (tl.pieceWeightsHeld (coefBody tl g F) g
        (t2fKappaByText (coefBody tl g F).theta jo)) = true ∧
      (List.range tl.NM).all (tl.tieWeightsHeld (coefBody tl g F)
        (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW + 1) {}).L) = true := by
    unfold k8Second at h2
    rw [hc, hg, hjo, hW] at h2
    cases e1 : W.all (tl.pieceWeightsHeld (coefBody tl g F) g
        (t2fKappaByText (coefBody tl g F).theta jo)) with
    | false =>
      simp only [e1, Bool.not_false, ↓reduceIte, reduceCtorEq] at h2
    | true =>
      cases e2 : (List.range tl.NM).all (tl.tieWeightsHeld (coefBody tl g F)
          (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW + 1) {}).L) with
      | false =>
        simp only [e1, e2, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
          reduceCtorEq] at h2
      | true => exact ⟨rfl, rfl⟩
  have hs : selfTestP tl nU F = .ok () := by
    unfold selfTestP
    simp [r1, r2, r3, a1, a2, a3, a4, a5]
    rfl
  have hk : rkSelfTestP tl (coefBody tl g F) = .ok () := by
    unfold rkSelfTestP
    simp only [hg, hjo, hW, r4, r5, r6, r7, r8, r9, r10, r11, hb.1, hb.2, Bool.and_self,
      ↓reduceIte, pure_bind]
    rfl
  refine ⟨coefBody tl g F, ?_⟩
  unfold testsP
  simp only [hs, hc, hk, bind, Except.bind, pure, Except.pure]

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.first_none
#print axioms ProofFile.Honest.K8.tests_of_share
#print axioms ProofFile.Honest.K8.K8Rest
