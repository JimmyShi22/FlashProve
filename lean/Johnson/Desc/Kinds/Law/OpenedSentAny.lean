-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/OpenedSentAny.lean: Law/OpenedSent.lean's sent_opened FOR EVERY DRAW: THE OUTPUT HEAD's 35 FORMS ARE WORTH 0, AND ITS CLAIM ON THE WEIGHTS IS TRUE, BEHIND AN HONEST SENDING OF ALL ITS ROUNDS, WHATEVER CANONICAL ELEMENTS ARE
DRAWN. WHY: sent_opened's draws, all the element 1, are a CORNER OF THE CUBE, AND THE WORST: the corner of position 2^lt - 1 and of feature 2^lPd - 1: at the toys' record a position that
the request does not check and a feature that is padding: there WeightTrue's right side, logitForms' second form, the head's two end values and the squares' end forms are 0 - 0 WHATEVER THE CELLS ARE.
  sent_opened_any   head_sendsC's own letters for the draws (pts · gam epsS down om epsP epsN epsL · rsS rsP rsN rsL, their lengths, each canonical): there are rounds rs, canonical, SHAPED AS Head.lean's TABLE SAYS WITH ALL THAT IS
                    DRAWN AMONG THE GIVEN DRAWS, at which hear F rs = some (H, G, []) · THE CHALLENGES HEARD ARE THE GIVEN ONES (pV = pts; the four sumchecks' r) · no draw is bad under the block's one rule · G WellLaid · HeadTruth (what the head's own sumcheck's hidden scalars are) ∧ WeightTrue ∧ all 35 forms 0 at G.
WHAT IT IS NOT. As Law/OpenedSent.lean: a toy's stone: the tape is built in Lean. Nothing on soundness.
IMPORTED, NOT THIS FILE's: head_sendsC; row_true.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.OpenedSent

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE zeroE oneE)
open OnBytes.Model (Aff Fork World)
open OnBytes.Desc.First.P1 (mle)
open Norm (lt ls d lPd T S2)
open Came (val vsG vsG_length)
open Part.MaskedSum (ownSlots)

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In]

/-- All the given draws, in head_sendsC's order. -/
def drawsOf (pts : List E) (gam epsS down om epsP epsN epsL : E) (rsS rsP rsN rsL : List E) :
    List E :=
  pts ++ (gam :: down :: epsS :: rsS) ++ (om :: epsP :: rsP) ++ (epsN :: rsN) ++ (epsL :: rsL)

/-- **BEHIND AN HONEST SENDING OF ALL THE BLOCK's ROUNDS, WHATEVER IS DRAWN.** -/
theorem sent_opened_any (c : NCells) (mask : Nat → E) {F : Fork} (hW : WellLaid F)
    (hH : (dataOf c).Holds) (hC : HonestHead c.toCells) (hreq : Request.ok = true) (hy : y < V)
    (hw : WeightsOk) (hzt : (FinalNorm.zt).size = lt) (hls : ls ≤ lPd) (hdS : S2 ∣ d)
    (hblock : ∀ x, x < d →
      FinalNorm.ew .remLow x = FinalNorm.ewh .remLow (x / S2) * eq FinalNorm.zl (x % S2))
    (pts : List E) (hpts : pts.length = lt)
    (gam epsS down om epsP epsN epsL : E) (rsS rsP rsN rsL : List E)
    (hrS : rsS.length = (zS pts.toArray).size + 1) (hrP : rsP.length = pts.toArray.size + 1)
    (hrN : rsN.length = (FinalNorm.zt).size + 1) (hrL : rsL.length = zP.size + 1)
    (okp : ∀ x ∈ pts, okE x = true) (okg : okE gam = true) (okeS : okE epsS = true)
    (okd : okE down = true) (oko : okE om = true) (okeP : okE epsP = true)
    (okeN : okE epsN = true) (okeL : okE epsL = true)
    (okrS : ∀ x ∈ rsS, okE x = true) (okrP : ∀ x ∈ rsP, okE x = true)
    (okrN : ∀ x ∈ rsN, okE x = true) (okrL : ∀ x ∈ rsL, okE x = true) {m : Nat}
    (hF : Fresh F (9 + (ownSlots (callOf 0 (zS pts.toArray) 2).all + 2 +
      (7 + (1 + (ownSlots (callOf 1 pts.toArray 4).all + 4 +
        (1 + (ownSlots (callOf 1 FinalNorm.zt 2).all + 2 +
          (1 + (ownSlots (callOf 1 zP 2).all + 2 + m)))))))))) :
    ∃ (rs : List Fmt.RoundView) (H : HeardAll) (G : Fork),
      Canonical rs ∧ hear F rs = some (H, G, []) ∧ Sound.NoBad (Came.rowRuleC c mask F) rs ∧
      WellLaid G ∧
      Shaped (drawsOf pts gam epsS down om epsP epsN epsL rsS rsP rsN rsL) rs rounds ∧
      (H.1.pV = pts.toArray ∧ H.1.gam = gam ∧ H.1.om = om ∧
        H.1.squares.r = (rsS.take (zS pts.toArray).size).toArray ∧
        H.1.products.r = (rsP.take pts.toArray.size).toArray ∧
        H.2.1.normed.r = (rsN.take (FinalNorm.zt).size).toArray ∧
        H.2.2.logits.r = (rsL.take zP.size).toArray) ∧
      (let _ : Norm.Heard := H.1
       let _ : FinalNorm.Heard := H.2.1
       let _ : Heard := H.2.2
       let _ : FinalNorm.Reads := normReadsAtCells c
       let _ : Reads := readsAt c.toCells
       HeadTruth c.toCells G mask noEnt ∧ WeightTrue c.toCells G mask noEnt ∧
        ∀ name fs, claims.lookup name = some fs → ∀ f, f ∈ fs → atWorld G mask noEnt f = 0) := by
  obtain ⟨rs, H, G, hShape, hcan, hhear, hNT, hST, _, hWG, ePV, eg, eo, eS, eP, eN, eL, hval⟩ :=
    head_sendsC c mask hW hH pts hpts gam epsS down om epsP epsN epsL rsS rsP rsN rsL hrS hrP hrN
      hrL okp okg okeS okd oko okeP okeN okeL okrS okrP okrN okrL hF
  have hRT : RowTruth c mask F rs :=
    ⟨hNT, fun pre tN tL Hn Fa Fb F1 SN SL a b c' d' =>
      ⟨(hST pre tN tL Hn Fa Fb F1 SN SL a b c' d').1,
        logits_form _ _ _ _ (hST pre tN tL Hn Fa Fb F1 SN SL a b c' d').2⟩⟩
  refine ⟨rs, H, G, hcan, hhear, Came.row_true c mask F hW hhear hRT, hWG, hShape hzt,
    ⟨ePV, eg, eo, eS, eP, eN, eL⟩, ?_⟩
  obtain ⟨⟨w1, w2, w3, w4, w5, w6, w7⟩, ⟨n0, n1, n2, n3⟩, ⟨l0, l1, l2, l3⟩⟩ :=
    hval G (worldE G mask noEnt) (OnBytes.PscRun.Later.refl _) (fun _ _ _ => rfl)
  have sPt : pts.toArray.size = lt := by simpa using hpts
  have sPV : H.1.pV.size = lt := by rw [ePV]; exact sPt
  have sS : H.1.squares.r.size = lPd + lt := by
    rw [eS, List.size_toArray, List.length_take, hrS, zS_size _ sPt]
    omega
  have sP : H.1.products.r.size = lt := by
    rw [eP, List.size_toArray, List.length_take, hrP, sPt]
    omega
  have sN : H.2.1.normed.r.size = lt := by
    rw [eN, List.size_toArray, List.length_take, hrN, hzt]
    omega
  have szP : zP.size = lt + lPd := by
    unfold zP
    rw [Array.size_append, hzt]
    simp [halves]
  have sL : H.2.2.logits.r.size = lt + lPd := by
    rw [eL, List.size_toArray, List.length_take, hrL, szP]
    omega
  obtain ⟨Fa, Fb, lr, hNorm, _, _, _, hsL, _⟩ := Came.hear_parts hW hhear
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h4, _, _⟩ := norm_parts hW hNorm
  have h6 : okE (H.1.P.getD 6 {}).var.const = true := batch_okConst h4 6
  have ok1 : okE (H.2.2.logits.end_ 1).var.const = true := sumcheck_okEnds hsL 1
  letI : Norm.Heard := H.1
  letI : FinalNorm.Heard := H.2.1
  letI : Heard := H.2.2
  letI : FinalNorm.Reads := normReadsAtCells c
  letI : Reads := readsAt c.toCells
  have hN : NormTruthW (worldE G mask noEnt) c :=
    { sums := w1, prods := w2, sqRow := w3, sq0 := w4 0 (by omega), sq1 := w4 1 (by omega)
      prClaimed := w5, prRow := w6, prEnd := w7, nmRow := n1
      nm0 := by rw [vsG_length, hzt] at n2; exact n2
      nm1 := by rw [vsG_length, hzt] at n3; exact n3 }
  have hT : HeadTruth c.toCells G mask noEnt :=
    headTruth_of_values c.toCells G mask noEnt hzt sL l0 l1
      (by rw [vsG_length, szP] at l2; exact l2) (by rw [vsG_length, szP] at l3; exact l3) ok1
  exact ⟨hT, opened_all H G c mask hreq hy hw hzt hls hdS hblock sPV sS sP sN hH hC hN h6 hT⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.sent_opened_any
