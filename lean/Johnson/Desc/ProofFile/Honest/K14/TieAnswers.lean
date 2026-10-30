-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/TieAnswers.lean: kind K14: THE OUT-OF-DOMAIN (OOD) ANSWERS THAT
THIS KIND's TEXT OF A SENDING SHOWS IN ITS SECOND ROUND ARE THOSE THAT THE SHARED SENDING's TEXT
SHOWS, AT THE SAME COINS, NUMBER BY NUMBER: WHERE THE JOB's SHAPES FIT AND THE JOB's VECTORS ARE THE
SAME IN BOTH ROUNDS (SameData). Statements with their proofs. An equation at each value of the
coins: no distribution occurs.

  words_tie       rows that agree wherever they are read (RowsAgree, Honest/K14/TieDefs.lean) give
                  the same two tables by index, below the tables' sizes: at codes whose lengths fit
                  and messages of admitted shapes (lengthsFit, Johnson/Desc/Own/Lin.lean;
                  sentShapeFits, Johnson/Desc/Own/Sent.lean)
  sendRows_same   where the job's vectors are the same in front of the part's first challenge and
                  behind it (SameData, Honest/K14/ExactDefs.lean), so are the rows that are laid
  answers_tie     **the second round's items**: sendShownAt (Honest/K14/SendingsPlay.lean) is the
                  list of the shared text's answers at the rows laid at the stand IN FRONT of the
                  part; with 0 as the first new message's number
  shapes_of_fit   the test on a job's shapes gives the test on each message's

How. shown_read (Honest/K14/SendingsAnswers.lean) reads this kind's answers as the library's at any
rows with the same tables; stAt_front and answers_round (Honest/K14/SendingsViaAnswers.lean) bring
the shared text's to the same form.
What is assumed. sendShapeFits J = true; SameData at the challenges heard: without it this kind's
second round can lay other rows than its first, and the equation can fail.
Limits. Nothing on columns. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.TieRows
import Johnson.Desc.ProofFile.Honest.K14.SendingsViaAnswers
import Johnson.Desc.ProofFile.Honest.K1.CoinLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E zeroE ceilLog2)
open OnBytes.Slice (GE GF rdE ofE toE)
open VerifiableInference.Desc (K1.Par K1.Msg.of)
open Johnson.Prover.Send (shapeAt answers)
open ProofFile.Honest.K1 (rowsR stAt seedsAt two_logEll_base two_logEll_mask)

/-- **Rows that agree wherever they are read give the same two tables by index**, below the tables'
sizes: at codes whose lengths fit (lengthsFit) and messages of admitted shapes (sentShapeFits). -/
theorem words_tie (P : K1.Par) (L : Nat → Laid) (V : Nat → Johnson.Prover.Send.Rows)
    (h : RowsAgree P L V)
    (hlen : VerifiableInference.Desc.Own.lengthsFit P.codes = true)
    (hsh : ∀ k, k < P.sent.size →
      VerifiableInference.Desc.Own.sentShapeFits P.codes (shapeAt P k) = true)
    (k : Nat) (hk : k < P.sent.size) (part : OnBytes.Part) (i : Nat)
    (hi : i < (K1.Msg.of P.codes (shapeAt P k)).size part) :
    rdE.val (wordsOf P.sent L k part i) = (V k).word (shapeAt P k) part i := by
  have hs0 := hsh k hk
  simp only [VerifiableInference.Desc.Own.sentShapeFits, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq, decide_eq_true_eq] at hs0
  cases part with
  | main =>
    show rdE.val (if i % 2 ^ ceilLog2 (shapeAt P k).mainRows < (shapeAt P k).mainRows then
        (L k).main (i % 2 ^ ceilLog2 (shapeAt P k).mainRows)
          (i / 2 ^ ceilLog2 (shapeAt P k).mainRows) else zeroE) =
      (if i % 2 ^ ceilLog2 (shapeAt P k).mainRows < (shapeAt P k).mainRows then
        (V k).main ((shapeAt P k).mainDeg == 3)
          (i % 2 ^ ceilLog2 (shapeAt P k).mainRows) (i / 2 ^ ceilLog2 (shapeAt P k).mainRows)
        else 0)
    by_cases hr : i % 2 ^ ceilLog2 (shapeAt P k).mainRows < (shapeAt P k).mainRows
    · rw [if_pos hr, if_pos hr]
      have hne : (shapeAt P k).mainRows ≠ 0 := by omega
      have hc : (shapeAt P k).code < P.codes.base.size := by
        rcases hs0.1.1.2 with e | e
        · exact absurd e hne
        · exact e
      have h2 := two_logEll_base P.codes (shapeAt P k).code hlen hc
      have hj : i / 2 ^ ceilLog2 (shapeAt P k).mainRows <
          (P.codes.base.getD (shapeAt P k).code default).ell := by
        have hK : ((shapeAt P k).mainRows != 0) = true := bne_iff_ne.2 hne
        have hK' : ((shapeAt P k).mainRows == 0) = false := beq_eq_false_iff_ne.2 hne
        have hs : (K1.Msg.of P.codes (shapeAt P k)).size .main =
            2 ^ ceilLog2 (shapeAt P k).mainRows *
              2 ^ (P.codes.base.getD (shapeAt P k).code default).logEll := by
          rw [← Nat.pow_add]
          show (if ((shapeAt P k).mainRows != 0) = true then
            2 ^ (if ((shapeAt P k).mainRows == 0) = true then 0 else
              ceilLog2 (shapeAt P k).mainRows +
                (P.codes.base.getD (shapeAt P k).code default).logEll) else 0) = _
          rw [if_pos hK, hK', if_neg Bool.false_ne_true]
        rw [hs, h2] at hi
        exact Nat.div_lt_of_lt_mul hi
      rw [← h.main k hk _ hr _ hj]
      unfold Johnson.Prover.Send.Rows.main
      rw [h.overE k hk hne]
      rfl
    · rw [if_neg hr, if_neg hr, rdE.zero]
  | mask =>
    show rdE.val (if i % 2 ^ ceilLog2 (shapeAt P k).maskRows < (shapeAt P k).maskRows then
        (L k).mask (i % 2 ^ ceilLog2 (shapeAt P k).maskRows)
          (i / 2 ^ ceilLog2 (shapeAt P k).maskRows) else zeroE) =
      (if i % 2 ^ ceilLog2 (shapeAt P k).maskRows < (shapeAt P k).maskRows then
        (V k).mask (i % 2 ^ ceilLog2 (shapeAt P k).maskRows)
          (i / 2 ^ ceilLog2 (shapeAt P k).maskRows) else 0)
    by_cases hr : i % 2 ^ ceilLog2 (shapeAt P k).maskRows < (shapeAt P k).maskRows
    · rw [if_pos hr, if_pos hr]
      have hne : (shapeAt P k).maskRows ≠ 0 := by omega
      have hc : (shapeAt P k).maskCode < P.codes.mask.size := by
        rcases hs0.1.2 with e | e
        · exact absurd e hne
        · exact e
      have h2 := two_logEll_mask P.codes (shapeAt P k).maskCode hlen hc
      have hj : i / 2 ^ ceilLog2 (shapeAt P k).maskRows <
          (P.codes.mask.getD (shapeAt P k).maskCode default).ell := by
        have hK : ((shapeAt P k).maskRows != 0) = true := bne_iff_ne.2 hne
        have hK' : ((shapeAt P k).maskRows == 0) = false := beq_eq_false_iff_ne.2 hne
        have hs : (K1.Msg.of P.codes (shapeAt P k)).size .mask =
            2 ^ ceilLog2 (shapeAt P k).maskRows *
              2 ^ (P.codes.mask.getD (shapeAt P k).maskCode default).logEll := by
          rw [← Nat.pow_add]
          show (if ((shapeAt P k).maskRows != 0) = true then
            2 ^ (if ((shapeAt P k).maskRows == 0) = true then 0 else
              ceilLog2 (shapeAt P k).maskRows +
                (P.codes.mask.getD (shapeAt P k).maskCode default).logEll) else 0) = _
          rw [if_pos hK, hK', if_neg Bool.false_ne_true]
        rw [hs, h2] at hi
        exact Nat.div_lt_of_lt_mul hi
      exact (h.mask k hk _ hr _ hj).symm
    · rw [if_neg hr, if_neg hr, rdE.zero]

/-- Where the job's vectors are the same in front of the first challenge and behind it, so are the
rows. -/
theorem sendRows_same (J : SendJob) (a : Ask) (h : List Fmt.Drawn) (hsame : SameData J h)
    (x₀ : Fmt.Drawn) (cs : Array E) :
    J.rows { input := a, heard := h ++ [x₀], own := () } cs =
      J.rows { input := a, heard := h, own := () } cs := by
  funext k
  unfold SendJob.rows
  rw [hsame a x₀ k]

/-- What the test on a sending's shapes says of the codes' lengths and of each message's shape. -/
theorem shapes_of_fit (J : SendJob) (hfit : sendShapeFits J = true) :
    VerifiableInference.Desc.Own.lengthsFit J.Q.codes = true ∧
      ∀ k, k < J.Q.sent.size →
        VerifiableInference.Desc.Own.sentShapeFits J.Q.codes (shapeAt J.Q k) = true := by
  have h0 := hfit
  unfold sendShapeFits at h0
  rw [Bool.and_eq_true, Bool.and_eq_true] at h0
  refine ⟨h0.1.1, fun k hk => ?_⟩
  have hf := msg_fits J hfit k hk
  cases hs : J.sort k with
  | plain high =>
    rw [hs] at hf
    simp only [msgShapeFits, Bool.and_eq_true] at hf
    exact hf.1.1
  | fresh k' h =>
    rw [hs] at hf
    simp only [msgShapeFits, Bool.and_eq_true] at hf
    exact hf.1.1.1.1.1.1

/-- **The second round's items in the two texts are the same**, where the job's shapes fit and the
job's vectors are the same in both rounds (SameData). -/
theorem answers_tie (J : SendJob) (hfit : sendShapeFits J = true) (c : Cs (sendingPart J).takes)
    (a : Ask) (h : List Fmt.Drawn) (hsame : SameData J h) (x₀ x₁ : Fmt.Drawn) :
    sendShownAt J c a (h ++ [x₀]) =
      (answers J.Q (stAt J.Q 0) 0
        (Johnson.Prover.Send.held (fun _ _ _ => 0) 0 J.Q (rowsR J.Q (rideBySort J)
          (vecData J { input := a, heard := h, own := () }) (recount (due_tie J hfit) c)))
        (seedsAt J.Q [x₀, x₁])).map fun y => (Said.answer (toE y)).got := by
  obtain ⟨hlen, hsh⟩ := shapes_of_fit J hfit
  obtain ⟨e1, e2⟩ := stAt_front J.Q 0
  rw [shown_read J c a h x₀ [] (stFront J.Q 0) rfl
    (rowsR J.Q (rideBySort J) (vecData J { input := a, heard := h, own := () })
      (recount (due_tie J hfit) c)) (fun _ _ _ => 0)
    (fun k hk part j hj => by
      rw [sendRows_same J a h hsame x₀]
      exact words_tie J.Q _ _ (rows_tie J hfit c _) hlen hsh k hk part j hj)]
  unfold Desc.K14.Honest.answersAt
  rw [e2, ← e1]
  show (answers J.Q (stAt J.Q 0) 0 _ (seedsAt J.Q [x₀, x₁])).map Fmt.ItemValue.answer = _
  rw [← answers_round J.Q (stAt J.Q 0), List.map_map, List.map_map]
  refine List.map_congr_left fun y _ => ?_
  show Fmt.ItemValue.answer (ofE (toE y)) = Fmt.ItemValue.answer (ofE (toE (ofE (toE y))))
  rw [OnBytes.Slice.toE_ofE]

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.words_tie
#print axioms ProofFile.Honest.K14.sendRows_same
#print axioms ProofFile.Honest.K14.shapes_of_fit
#print axioms ProofFile.Honest.K14.answers_tie
