-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/BookAtOmegaHead.lean: kind K14: AT THE PROOF FILE's IOP AS WRITTEN
IN LEAN (below: the description), FOR ALL PUBLIC FILES Z THAT PASS THE LIBRARY's TEST InScope AND
EVERY PUBLIC PART Zp OF WHICH THE LIBRARY's LaidAt HOLDS: THE SHARED LIST HAS THE FORM SharedForm
(Honest/K14/BookAtShared.lean), AND ONE TEST ON PUBLIC NUMBERS ACCEPTS (headNumbersB), which gives
the numbers' premises of Honest/K14/BookAtOmega.lean's statements. One definition with code;
statements with their proofs.

  headNumbersB codes S   **one test on public numbers**: omegaNumbersB at o_omega's count and
                  o_sp's count as the part counts them · o_sp has an entry that is no pad · the
                  library's freshPublicB
  headNumbers_give   what its yes gives at every plan with these codes and this shape
  headNumbers_written, numbers_bite   **headNumbersB accepts at the written sizes**: o_omega's run
                  has 42,853 coins, o_sp's 216; **omegaNumbersB can fail**: it rejects there at a
                  first coin greater by one, and at a length smaller by one. (Its clauses on the
                  two notices have no such example; headNumbersB is shown to reject nowhere.)
  form_at_files, numbers_at_files   SharedForm and the test, at the description

Kin. sendings_of_laid (Honest/K14/SendingsAtHead.lean) has also the library's SpShape at 63 and the
tail 152 at the description's plan; here freshPublicB is evaluated anew inside headNumbersB: two
ways to one fact.
What is assumed. InScope Z, LaidAt.
What is not claimed. Anything on a book: Honest/K14/SharedSendsWritten.lean. Nothing on what is or
is not hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.BookAtOmega
import Johnson.Desc.ProofFile.Honest.K14.BudRows
import Johnson.Desc.ProofFile.Honest.K14.SendingsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.K12.Seat (tests last)
open VerifiableInference.PlanWritten (proofSizedFull)
open OnBytes (Codes OracleNotice)
open VerifierAndGoals (InScope)
open P5J (LaidAt F0T TS)
open AtPublicFiles.TreeReads (sized_at written_proof)
open Desc.K14.Honest (flatOf_carried)

/-- **One test on public numbers.** -/
def headNumbersB (codes : Codes) (S : OnBytes.Params.LinShape) : Bool :=
  omegaNumbersB codes (Desc.K14.withOmega S).toList (dueOf codes S.omega (.plain S.omegaRowsHigh))
      ((codes.mask.getD S.sharedSplit.maskCode default).ell - 1 + 1 +
        (codes.mask.getD S.sharedSplit.maskCode default).r) &&
    decide (0 < (codes.mask.getD S.sharedSplit.maskCode default).ell - 1) &&
    Desc.K14.Honest.freshPublicB codes S ((codes.mask.getD S.sharedSplit.maskCode default).ell - 1)
      (codes.mask.getD S.sharedSplit.maskCode default).r

/-- What its yes gives, at every plan with these codes and this shape, where the shape splits. -/
theorem headNumbers_give (A : SendPub) (hs : A.P.S.sharedSplitNeeded = true)
    (h : headNumbersB A.P.codes A.P.S = true) :
    omegaNumbersB A.P.codes (Desc.K14.withOmega A.P.S).toList (spFirstCoin A)
        (spEntries A + 1 + (spMaskCode A).r) = true ∧ 0 < spEntries A ∧
      Desc.K14.Honest.freshPublicB A.P.codes A.P.S (spEntries A) (spMaskCode A).r = true := by
  unfold headNumbersB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rw [spFirstCoin_eq A hs]
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **The test accepts at the written sizes**; the two counts there. -/
theorem headNumbers_written : headNumbersB proofSizedFull.codes proofSizedFull.batch.shape = true ∧
    dueOf proofSizedFull.codes proofSizedFull.batch.shape.omega
      (.plain proofSizedFull.batch.shape.omegaRowsHigh) = 42853 ∧
    (proofSizedFull.codes.mask.getD proofSizedFull.batch.shape.sharedSplit.maskCode default).ell -
      1 + 1 + (proofSizedFull.codes.mask.getD
        proofSizedFull.batch.shape.sharedSplit.maskCode default).r = 216 := by decide +kernel

/-- **IT CAN FAIL**: at the written sizes omegaNumbersB accepts at 42,853 and 216, and rejects at a
first coin greater by one, and at a length smaller by one. -/
theorem numbers_bite :
    omegaNumbersB proofSizedFull.codes (Desc.K14.withOmega proofSizedFull.batch.shape).toList
        42853 216 = true ∧
      omegaNumbersB proofSizedFull.codes (Desc.K14.withOmega proofSizedFull.batch.shape).toList
        42854 216 = false ∧
      omegaNumbersB proofSizedFull.codes (Desc.K14.withOmega proofSizedFull.batch.shape).toList
        42853 215 = false := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- The description's shared list has the form that the book's makers read. -/
theorem form_at_files (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    SharedForm (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder := by
  obtain ⟨⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩, -⟩ := made_of_laid L
  obtain ⟨-, hs, -⟩ := sendings_of_laid scope L
  refine sharedForm_of_flat (xs := (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder)
    (flatOf_carried Zp.p.chains (qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8 (tests Np) last hb) hb hs
    fun y hy => ⟨no_later b1 b2 b3 b4 b5 b6 b7 b8 hb y hy,
      no_later_u b1 b2 b3 b4 b5 b6 b7 b8 hb y ?_⟩
  exact List.mem_of_mem_drop (i := 3) (by rw [List.drop_drop]; exact hy)

/-- The test on the numbers accepts at the description's plan. -/
theorem numbers_at_files (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    headNumbersB (qAt Zp Np).codes (qAt Zp Np).S = true := by
  show headNumbersB Zp.p.chains.made.sized.proof.codes
    Zp.p.chains.made.sized.proof.batch.shape = true
  rw [sized_at scope L, written_proof]
  exact headNumbers_written.1

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.headNumbers_give
#print axioms ProofFile.Honest.K14.headNumbers_written
#print axioms ProofFile.Honest.K14.numbers_bite
#print axioms ProofFile.Honest.K14.form_at_files
#print axioms ProofFile.Honest.K14.numbers_at_files
