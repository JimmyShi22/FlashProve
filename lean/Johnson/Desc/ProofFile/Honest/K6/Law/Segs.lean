-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/Segs.lean: NOT a law on a distribution, and nothing on a side
or a run: WHAT THE DECLARED ROUNDS OF THE SUB-PROTOCOL "the output head's own rounds" ARE, PART BY
PART, GENERAL IN THE PLACE's PUBLIC NUMBERS p: proofs, no evaluation. CONDITIONAL where it says so.

  1  `headSegs`, `laySeg`, `headSeg`   the verifier's table of rounds as eight stretches, one for
     each part of the row (Honest/K6/Part.lean); a stretch as a member of a side has it: declared,
     each round with no oracle message
  2  `head_rounds_segs`, `headSegs_cut`, `headSegs_sent`   the stretches, one behind the other, ARE
     the verifier's table (Johnson/Desc/Kinds/Head.lean: `rounds`); their lengths are `headCut p`;
     what they send is `headSent p` (Honest/K6/Law/Rounds.lean): that table and the verifier's
     table of rounds agree
  3  `headSeg_small`   the premises of the two small laws of Honest/Small/ at the stretches 0, 1, 3,
     4
  4  `shapeOk_point`, `headSeg_sums`, `headSeg_beta`   THREE OF THE FOUR PREMISES ON PUBLIC DATA OF
     THE MASKED SUMCHECK's LAW (Honest/SumLaw/SumExact.lean, by other authors), at the row's four
     calls and the stretches 2, 5, 6, 7: the library's test on the shape (`shapeOk`); what the
     rounds state (`StatedBy`); that the round "PSC Y" samples an element that the format marks as
     never 0 (`betaMarked`, Honest/SumLaw/BetaMarked.lean). On the fourth, `drawsFit` at the
     declared rounds, nothing is stated here: it is a premise of the field `exact` itself
     (`ExactMember`, Honest/Small/Field.lean)
  5  `stated_laySeg`, `headSegs_sums_sent`, `at_Y`, `beta_laySeg`   steps to these

Called. `declare_stated`, `scalarsOf_point`, `sent_sumcheck`, `headSent`:
Honest/K6/Law/Rounds.lean, called. `betaMarked`, `firstMarked_of`: Honest/SumLaw/BetaMarked.lean,
called.

Limits. All of it speaks of `Head.Par.rounds`, the kind's own text: that the description's own
block at the place, as its makers have wrapped it, has these rounds and no oracle message is a
premise of Honest/K6/Law/Row.lean's structure. `headSeg p i` at i above 7 is the empty list, in
silence. Nothing on what a round draws but at "PSC Y". Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.BetaMarked
import Johnson.Desc.ProofFile.Honest.K6.Law.Rounds
import Johnson.Desc.ProofFile.Honest.Small.Cut
import Johnson.Desc.ProofFile.Honest.Small.StatedBy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Oracle)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Part.MaskedSum (Call shapeOk)
open ProofFile.Honest.Small ProofFile.Honest.SumLaw

/-! ## 1 The stretches -/

/-- The verifier's table of rounds, cut as the row is cut: eight stretches. -/
def headSegs (p : Head.Par) : List (List Round) :=
  [drawPoint.rounds (headLt p), sendThenBatch.rounds 9 9,
   ⟨"PSC epsilon", 1, 1, false, 0⟩ :: List.replicate (headLPd p + headLt p)
     ⟨"PSC round", 2, 1, false, 0⟩ ++ [⟨"PSC Y", 2, 1, true, 0⟩, ⟨"PSC values", 2, 0, false, 0⟩],
   [⟨"LINE", 0, 1, false, 0⟩], sendThenBatch.rounds 7, sumcheck.rounds (headLt p) 4,
   sumcheck.rounds (headLt p) 2, sumcheck.rounds (headLt p + headLPd p) 2]

/-- A stretch as a member has it: declared, each round with no oracle message. -/
def laySeg (p : Head.Par) (s : List Round) : List (Fmt.DeclaredRound × List Oracle) :=
  (p.declare s).map fun d => (d, [])

/-- The stretch number i as a member has it. -/
def headSeg (p : Head.Par) (i : Nat) : List (Fmt.DeclaredRound × List Oracle) :=
  laySeg p ((headSegs p).getD i [])

/-- **The verifier's table of rounds is the eight stretches, one behind the other.** No premise. -/
theorem head_rounds_segs (p : Head.Par) : p.rounds = p.declare (headSegs p).flatten := by
  letI := p.sizes
  have hN0 : Norm.lNI = 0 := rfl
  have hN1 : Norm.NI = 1 := rfl
  show p.declare (Norm.rounds ++ FinalNorm.rounds ++ sumcheck.rounds (Norm.lt + Norm.lPd) 2) = _
  congr 1
  show _ = drawPoint.rounds Norm.lt ++ (sendThenBatch.rounds 9 9 ++
    ((⟨"PSC epsilon", 1, 1, false, 0⟩ :: List.replicate (Norm.lPd + Norm.lt)
      ⟨"PSC round", 2, 1, false, 0⟩ ++
        [⟨"PSC Y", 2, 1, true, 0⟩, ⟨"PSC values", 2, 0, false, 0⟩]) ++
    ([⟨"LINE", 0, 1, false, 0⟩] ++ (sendThenBatch.rounds 7 ++ (sumcheck.rounds Norm.lt 4 ++
      (sumcheck.rounds Norm.lt 2 ++ (sumcheck.rounds (Norm.lt + Norm.lPd) 2 ++ [])))))))
  simp only [Norm.rounds, FinalNorm.rounds, hN0, hN1, level.rounds, beq_self_eq_true, if_true,
    Nat.mul_one, Nat.zero_add]
  simp
  rfl

/-- The stretches' lengths are the cut's. No premise. -/
theorem headSegs_cut (p : Head.Par) : (headSegs p).map (·.length) = headCut p := by
  simp [headSegs, headCut, drawPoint.rounds, sendThenBatch.rounds, sumcheck.rounds]

/-! ## 2 What the stretches state: for all sizes -/

/-- CONDITIONAL. A stretch, laid, states round by round what its rounds send, and no oracle message.
-/
theorem stated_laySeg (p : Head.Par) (s : List Round) (ns : List Nat)
    (h : s.map (·.sent) = ns) : StatedBy ns (laySeg p s) := by
  subst h
  unfold laySeg
  rw [← zip_map_nil]
  exact declare_stated p s

/-- **The premises of the two small laws (Honest/Small/Quiet.lean, Scalars.lean) at the declared
rounds, for all sizes.** No premise. -/
theorem headSeg_small (p : Head.Par) :
    statedOf (headSeg p 0) = List.replicate 1 ([], []) ∧
    statedOf (headSeg p 1) = [(List.replicate 9 .e, [])] ∧
    statedOf (headSeg p 3) = List.replicate 1 ([], []) ∧
    statedOf (headSeg p 4) = [(List.replicate 7 .e, [])] :=
  ⟨stated_quiet_one_of (stated_laySeg p _ [0] rfl), stated_scalars_of (stated_laySeg p _ [9] rfl),
    stated_quiet_one_of (stated_laySeg p _ [0] rfl), stated_scalars_of (stated_laySeg p _ [7] rfl)⟩

/-- What the four sums' stretches send is what their calls' shapes count. -/
theorem headSegs_sums_sent (p : Head.Par) :
    ((headSegs p).getD 2 []).map (·.sent) = scalarsOf (headSquaresJob p).shape ∧
    ((headSegs p).getD 5 []).map (·.sent) = scalarsOf (headProductsJob p).shape ∧
    ((headSegs p).getD 6 []).map (·.sent) = scalarsOf (headNormedJob p).shape ∧
    ((headSegs p).getD 7 []).map (·.sent) = scalarsOf (headLogitsJob p).shape := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show _ = scalarsOf (pointShape 0 (headLPd p + headLt p) 2)
    rw [scalarsOf_point]
    simp [headSegs]
  · show (sumcheck.rounds (headLt p) 4).map (·.sent) = scalarsOf (pointShape 1 (headLt p) 4)
    rw [scalarsOf_point, sent_sumcheck]
  · show (sumcheck.rounds (headLt p) 2).map (·.sent) = scalarsOf (pointShape 1 (headLt p) 2)
    rw [scalarsOf_point, sent_sumcheck]
  · show (sumcheck.rounds (headLt p + headLPd p) 2).map (·.sent) =
      scalarsOf (pointShape 1 (headLt p + headLPd p) 2)
    rw [scalarsOf_point, sent_sumcheck]

/-- What the eight stretches of the verifier's table send is `headSent` (Honest/K6/Law/Rounds.lean):
the two tables agree. No premise. -/
theorem headSegs_sent (p : Head.Par) : (headSegs p).map (·.map (·.sent)) = headSent p := by
  obtain ⟨e2, e5, e6, e7⟩ := headSegs_sums_sent p
  show [[0], [9], ((headSegs p).getD 2 []).map (·.sent), [0], [7],
    ((headSegs p).getD 5 []).map (·.sent), ((headSegs p).getD 6 []).map (·.sent),
    ((headSegs p).getD 7 []).map (·.sent)] = _
  rw [e2, e5, e6, e7]
  rfl

/-- **What the rounds state (`StatedBy`), at the four calls, for all sizes.** No premise. -/
theorem headSeg_sums (p : Head.Par) :
    StatedBy (scalarsOf (headSquaresJob p).shape) (headSeg p 2) ∧
    StatedBy (scalarsOf (headProductsJob p).shape) (headSeg p 5) ∧
    StatedBy (scalarsOf (headNormedJob p).shape) (headSeg p 6) ∧
    StatedBy (scalarsOf (headLogitsJob p).shape) (headSeg p 7) := by
  obtain ⟨e2, e5, e6, e7⟩ := headSegs_sums_sent p
  exact ⟨stated_laySeg p _ _ e2, stated_laySeg p _ _ e5, stated_laySeg p _ _ e6,
    stated_laySeg p _ _ e7⟩

/-- CONDITIONAL. **The library's test on a call's shape (`shapeOk`) at the row's form of a call**:
it passes, where the call has an end value. -/
theorem shapeOk_point (lead n ends : Nat) (h : 1 ≤ ends) :
    shapeOk (pointShape lead n ends) = true := by
  simp [shapeOk, pointShape, VerifiableInference.Desc.Part.MaskedSum.Var.d, h]

/-- The round behind a first round and n more. -/
theorem at_Y (e r y v : Round) (n : Nat) :
    (e :: List.replicate n r ++ [y, v])[n + 1]? = some y := by
  show (List.replicate n r ++ [y, v])[n]? = some y
  rw [List.getElem?_append_right (by simp)]
  simp

/-- At a stretch of the masked sumcheck's form the round number n + 1 is "PSC Y", whose one element
the format marks as never 0. -/
theorem beta_laySeg (p : Head.Par) (lead n ends : Nat) (e r v : Round) :
    betaMarked (pointShape lead n ends)
      (laySeg p (e :: List.replicate n r ++ [⟨"PSC Y", 2, 1, true, 0⟩, v])) = true := by
  show ((laySeg p (e :: List.replicate n r ++ [⟨"PSC Y", 2, 1, true, 0⟩, v]))[
    (List.replicate n (VerifiableInference.Desc.Part.MaskedSum.Var.point OnBytes.zeroE 3)).length
      + 1]?).any _ = true
  rw [List.length_replicate]
  unfold laySeg Head.Par.declare
  rw [List.getElem?_map, List.getElem?_map, at_Y]
  exact firstMarked_of _ rfl rfl rfl

/-- **The mark at "PSC Y" (`betaMarked`), at the four calls, for all sizes.** No premise. -/
theorem headSeg_beta (p : Head.Par) :
    betaMarked (headSquaresJob p).shape (headSeg p 2) = true ∧
    betaMarked (headProductsJob p).shape (headSeg p 5) = true ∧
    betaMarked (headNormedJob p).shape (headSeg p 6) = true ∧
    betaMarked (headLogitsJob p).shape (headSeg p 7) = true :=
  ⟨beta_laySeg p _ _ _ _ _ _, beta_laySeg p _ _ _ _ _ _, beta_laySeg p _ _ _ _ _ _,
    beta_laySeg p _ _ _ _ _ _⟩

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.head_rounds_segs
#print axioms ProofFile.Honest.K6.headSegs_cut
#print axioms ProofFile.Honest.K6.stated_laySeg
#print axioms ProofFile.Honest.K6.headSeg_small
#print axioms ProofFile.Honest.K6.headSegs_sums_sent
#print axioms ProofFile.Honest.K6.headSegs_sent
#print axioms ProofFile.Honest.K6.headSeg_sums
#print axioms ProofFile.Honest.K6.shapeOk_point
#print axioms ProofFile.Honest.K6.at_Y
#print axioms ProofFile.Honest.K6.beta_laySeg
#print axioms ProofFile.Honest.K6.headSeg_beta
