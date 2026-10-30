-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BodyStepAt.lean: THE VALUES' HALF OF ONE STAGE, AT bodyAll's OWN PIECES
(Johnson/Prover/Link/BodyAll.lean): what the laws on a fold and on a switch ask of the shown values
is met by sRF | sAns | sNext | sCol | sGS. Statements and proofs.

  fold_at      FoldFront · the claim in front is true at μOf s P, read with the record's own layout,
               whose numbers are the stage's · the further table is W's packing, and there is room
               ⟹ the single rows that the fold returns ON sRF, SHOWN WITHOUT DIGEST, are true at the
               three folded messages at sGam
  gam_at       sGam is the point that the switch's laws read off the fold's rounds as shown
  ans_at       the answer that sRS shows reads as gAns, where the two stages fit
  next_at      μOf of sNext is gMsg: the message of the switch's laws' end
  cols_at      every keyed column of sGS stands in the range and is col at its position
  next_packs, next_pairs   where a fold follows: sNext's further table is the next W's packing: so
               Pairs holds again
  col_later, col_last      sCol is stageColW of sNext, or lastCol at the last switch

Not shown here. Every premise on the form is asked. Nothing on soundness; nothing on how a value of
BCoins is chosen; nothing on what any value that is sent discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.BodyHelps
import Johnson.Prover.Link.BodyStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)

variable (p : P12) (K : BCoins) (last : Bool) (j : ℕ) (cur next : Fmt.M1.Stage) (l : Laid) (o : ℕ)
  (t : T12) (P : PS) (col : ℕ → List UInt64) (row : GroupRow) (D : ℕ → Fmt.Drawn)

theorem gam_at : sGam K j cur o P row D =
    readP ((sgOf cur).h + (sgOf cur).g)
      (((sRF K j cur o P row D).map noDigest).tail.map drawnOf) := by
  unfold sGam
  rw [← List.map_tail, map_drawnOf_noDigest]

/-- **The fold's output on sRF is true at the three folded messages.** -/
theorem fold_at {L : GroupLayout} {c : IoppStage} {n : ℕ × ℕ} {id : ℕ}
    (H : FoldFront p j cur t row L c n id) (hk : c.k = (sgOf cur).h + (sgOf cur).g)
    (hh : c.h = (sgOf cur).h)
    (hZ : (t.st.codes.mask.getD c.maskCode default).ell = (sgOf cur).Z.l)
    (hLk : L.k = (sgOf cur).h + (sgOf cur).g) (hLh : L.h = (sgOf cur).h)
    (hin : (Slf.idf (E := GE) (J := (sgOf cur).cIn.J)).Holds (stmGk (sgOf cur) L.k L.h row)
      (μOf (sgOf cur) P))
    (hl : (sgOf cur).h + 2 * (sgOf cur).g + 1 ≤ (sgOf cur).Z.l)
    (hpk : P.fM = packedN (sgOf cur) (K.W (sgOf cur) j)) :
    (Slf.idf (E := GE) (J := (sgOf cur).cMid.J)).Holds
      (stmS (sgOf cur) (foldOut t row L c id ((sRF K j cur o P row D).map noDigest)))
      (foldMsg (sgOf cur) (μOf (sgOf cur) P) (φOf (sgOf cur) P) (sGam K j cur o P row D)) := by
  have hin' : (Slf.idf (E := GE) (J := (sgOf cur).cIn.J)).Holds (stmG (sgOf cur) row)
      (μOf (sgOf cur) P) := by
    have e : stmGk (sgOf cur) L.k L.h row = stmG (sgOf cur) row := by rw [stmG_eq, hLk, hLh]
    rw [← e]
    exact hin
  have hR := shows_noDigest _ _ _ _ (foldRV_shows (sgOf cur) (vecG (sgOf cur) row)
    (μOf (sgOf cur) P) (K.W (sgOf cur) j) fun n => D (o + n))
  have i2 := (claimOf_shows _ _ _ _ zeroE hR).2.1
  have hF := fold_V (sgOf cur) (μOf (sgOf cur) P) (φOf (sgOf cur) P) (K.W (sgOf cur) j) _ H
    (noDigest ⟨[.e (ofE (hMu (sVars GE 2 ((sgOf cur).h + (sgOf cur).g)) (K.W (sgOf cur) j)))],
      D (o + 0)⟩) _ hk hh hZ hin' (pairs_packedN (sgOf cur) hl _ P hpk)
    (foldRV_sigma (sgOf cur) (K.W (sgOf cur) j) _) hR
  rw [← i2] at hF
  rw [gam_at]
  exact hF

theorem ans_at (hf : CsFit (sgOf cur) (sgOf next)) :
    readE (E.ofTriple (ofE (sAns p K j cur next l o t P row D))) =
      gAns hf
        (foldMsg (sgOf cur) (μOf (sgOf cur) P) (φOf (sgOf cur) P) (sGam K j cur o P row D))
        (foldTl (sgOf cur) (ρOf (sgOf cur) P) (ψOf (sgOf cur) P) (sGam K j cur o P row D)) (K.fr j)
        (readP _ (((D (o + 1 + ((sgOf cur).h + (sgOf cur).g))).elems.map E.ofTriple).take
          (Send.cube (sT1 p K j cur l o t P row D).st.codes
            (switchTargetStage ((stageAt p (j + 1) next).getD default).code
              ((stageAt p (j + 1) next).getD default).maskCode ((sgOf next).h + (sgOf next).g)
              (sgOf next).h 1).shape).bits),
          unitOf (readE (((D (o + 1 + ((sgOf cur).h + (sgOf cur).g))).elems.map E.ofTriple).getD
            (Send.cube (sT1 p K j cur l o t P row D).st.codes
              (switchTargetStage ((stageAt p (j + 1) next).getD default).code
                ((stageAt p (j + 1) next).getD default).maskCode ((sgOf next).h + (sgOf next).g)
                (sgOf next).h 1).shape).bits zeroE))) := by
  rw [readE_ofTriple, toE_ofE]
  exact ansAt_fit hf _ _ _ _ _

theorem next_at (hf : CsFit (sgOf cur) (sgOf next)) :
    μOf (sgOf next) (sNext K last j cur next o P row D) =
      gMsg hf
        (foldMsg (sgOf cur) (μOf (sgOf cur) P) (φOf (sgOf cur) P) (sGam K j cur o P row D))
        (foldTl (sgOf cur) (ρOf (sgOf cur) P) (ψOf (sgOf cur) P) (sGam K j cur o P row D))
        (K.fr j) :=
  muOf_next hf _ _ _ _

theorem cols_at (cut : List Fmt.DeclaredRound) (c : ℕ × ℕ × List UInt64)
    (h : c ∈ keyed p cut (sGS cur o col D)) : c.2.1 < 2 ^ (sgOf cur).C.a ∧ c.2.2 = col c.2.1 :=
  mem_keyed_group p cut _ _ col c h

theorem next_packs : (sNext K false j cur next o P row D).fM =
    packedN (sgOf next) (K.W (sgOf next) (j + 1)) := rfl

theorem next_pairs (hl : (sgOf next).h + 2 * (sgOf next).g + 1 ≤ (sgOf next).Z.l) :
    Pairs (sgOf next) (sgOf next).Z.l (K.W (sgOf next) (j + 1))
      (φOf (sgOf next) (sNext K false j cur next o P row D)) :=
  pairs_packedN (sgOf next) hl _ _ (next_packs K j cur next o P row D)

theorem col_later : sCol K false j cur next o P row D =
    stageColW (sgOf next) (sNext K false j cur next o P row D).tabM
      (sNext K false j cur next o P row D).tabZ (sNext K false j cur next o P row D).tM
      (sNext K false j cur next o P row D).tZ (sNext K false j cur next o P row D).fM
      (sNext K false j cur next o P row D).fT := rfl

theorem col_last : sCol K true j cur next o P row D =
    lastCol (sgOf next) (sNext K true j cur next o P row D) := rfl

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.gam_at
#print axioms Johnson.Prover.Link.fold_at
#print axioms Johnson.Prover.Link.ans_at
#print axioms Johnson.Prover.Link.next_at
#print axioms Johnson.Prover.Link.cols_at
#print axioms Johnson.Prover.Link.next_packs
#print axioms Johnson.Prover.Link.next_pairs
#print axioms Johnson.Prover.Link.col_later
#print axioms Johnson.Prover.Link.col_last
