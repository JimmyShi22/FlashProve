-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/ScriptPublic.lean: the closing of a segment (K10): the public clauses that the closing's exchange asks of the jobs of
the shared sending (the kind K1) whose messages are members of a closing's group: the fields ride, padOk and word of
`TieByShared` (Johnson/Desc/ProofFile/Honest/K10/Pay/XchTieByShared.lean), and what `FreshByShared` (Pay/XchFreshField.lean) asks of
the first segment's fresh mask, at the jobs of the base prover (AtFullSide/K1/RecordAtBase.lean), under the library's hypothesis.

  `wordS`, `wordB`, `word_first_written`, `word_later_written`   a closed test, by Lean's kernel, at the written plans: a message has no main row
                        or is sampled; each later sending has a message. `word_can_fail`: the test says no at a shape with a main
                        row and no sample
  `ride_first_written`  at the written plan of the first segment's sending: no table rides in the messages 0, 1, 2; in message 3 the
                        table of a fold of 8 row variables and height 0
  `plan_two`, `ride_two`, `plan_later`   under the hypothesis the jobs' plans and rides are the written ones
  **`public_opening`**    the job of the first segment's sending, n < 3: the three clauses
  **`public_later`**      the job of a segment's later sending (l < 25; d: the digits' or the reads'), every message n of it: the three
                        clauses; and it has a message
  **`fresh_opening`**     the first segment's fresh mask: the job's ride at message 3 is ⟨8, 0⟩; its mask coins start at 8411 of 8958:
                        so there is room for 2 k + 1 coins at every k ≤ 273

By: `eG_atAll`, `parL_written`, `ride_two_head`, `fits_two_head`, `fits_fifty_head`, `room_first_written`, `pad_le_of_fits`
(Johnson/Desc/K1/Law/TiesAtAll.lean; Johnson/Desc/ProofFile/Honest/K1/Law/FitsWritten.lean, RideAtPlans.lean, RoomAtW.lean;
Honest/K1/PadLaw.lean).

Limits. Public numbers alone. That a closing's own count of row variables at the first segment is 8, and its height 0, is not said
here. The hypothesis and the maker's return are premises. Closed facts by Lean's kernel. The full size and the older hash alone.
No property is claimed.
-/
import AtFullSide.K1.RecordAtBase
import Johnson.Desc.ProofFile.Honest.K1.Law.RoomAtW
import Johnson.Desc.ProofFile.Honest.K1.PadLaw
import Johnson.Desc.ProofFile.Honest.AtHeadGround

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K10
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest
open ProofFile.Honest.K1 (jobTwoAt jobLaterAt rideOf firstFold stepsOf maskStart dueR Ride pad_le_of_fits)
open Johnson.Prover.Send (shapeAt)

/-! ## 1 At the written plans -/

/-- A shape has no main row, or is sampled. -/
def wordS (s : OnBytes.OracleShape) : Bool := s.mainRows == 0 || s.answers != 0

/-- The test at a plan's message number n. -/
def wordB (P : VerifiableInference.Desc.K1.Par) (n : Nat) : Bool := wordS (shapeAt P n)

theorem word_of {P : VerifiableInference.Desc.K1.Par} {n : Nat} (h : wordB P n = true) :
    (shapeAt P n).mainRows = 0 ∨ (shapeAt P n).answers ≠ 0 := by
  unfold wordB wordS at h
  rcases Eq.mp (Bool.or_eq_true _ _) h with k | k
  · exact Or.inl (beq_iff_eq.1 k)
  · exact Or.inr (bne_iff_ne.1 k)

set_option maxRecDepth 1000000 in
/-- The first segment's sending, messages 0, 1, 2. -/
theorem word_first_written : ((List.range 3).all (wordB VerifiableInference.Desc.K1.parGF)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The fifty later sendings: each has a message, and the test says yes at each of its messages. -/
theorem word_later_written : ((List.range 25).all fun l => [false, true].all fun d =>
    decide (0 < (VerifiableInference.Desc.K1.placeL l d).sent.size) &&
      (List.range (VerifiableInference.Desc.K1.placeL l d).sent.size).all
        (wordB (VerifiableInference.Desc.K1.placeL l d))) = true := by
  decide +kernel

/-- The test can fail: a shape with a main row and no sample. -/
theorem word_can_fail : wordS { mainRows := 1, answers := 0 } = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Which messages of the first segment's sending bear a riding table. -/
theorem ride_first_written :
    ((List.range 3).all fun n => (rideOf (firstFold VerifiableInference.Desc.K1.qFull) n).isNone) = true ∧
      rideOf (firstFold VerifiableInference.Desc.K1.qFull) 3 = some ⟨8, 0⟩ := by
  decide +kernel

/-! ## 2 Under the hypothesis -/

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The plan of the first segment's sending is the written one. -/
theorem plan_two (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A) :
    (jobTwoAt S A.Z A.G).P = VerifiableInference.Desc.K1.parGF := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  show VerifiableInference.Desc.K1.firstPar A.G.first (VerifiableInference.Desc.K1.gpOf A.Z) = _
  rw [eG]
  exact VerifiableInference.Desc.K1.eG_atAll h O (VerifiableInference.Desc.K1.pin1_atAll h)

/-- Its ride is the written one. -/
theorem ride_two (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A) :
    (jobTwoAt S A.Z A.G).ride = rideOf (firstFold VerifiableInference.Desc.K1.qFull) := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  show rideOf (firstFold A.G.first) = _
  rw [eG]
  exact K1.ride_two_head h O

/-- The plan of a later sending is the written one. -/
theorem plan_later (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A) (l : Nat) (d : Bool) :
    (jobLaterAt S A.Z A.G l d).P = VerifiableInference.Desc.K1.placeL l d := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have e : (jobLaterAt S A.Z A.G l d).P = VerifiableInference.Desc.K1.parL A.Z A.G l d := by
    cases d <;> rfl
  rw [e, eG]
  exact K1.parL_written h O l d

/-- **THE FIRST SEGMENT's SENDING, MESSAGES 0, 1, 2.** -/
theorem public_opening (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A) {n : Nat} (hn : n < 3) :
    (jobTwoAt S A.Z A.G).ride n = none ∧
      (stepsOf (jobTwoAt S A.Z A.G).P.codes (shapeAt (jobTwoAt S A.Z A.G).P n) none).pad ≤
        ((jobTwoAt S A.Z A.G).P.codes.base.getD (shapeAt (jobTwoAt S A.Z A.G).P n).code default).ell ∧
      ((shapeAt (jobTwoAt S A.Z A.G).P n).mainRows = 0 ∨ (shapeAt (jobTwoAt S A.Z A.G).P n).answers ≠ 0) := by
  have eP := plan_two h hA
  have eR := ride_two h hA
  have hr : rideOf (firstFold VerifiableInference.Desc.K1.qFull) n = none :=
    Option.isNone_iff_eq_none.1 (List.all_eq_true.1 ride_first_written.1 n (List.mem_range.2 hn))
  have hs : n < VerifiableInference.Desc.K1.parGF.sent.size := by
    rw [K1.room_first_written.1]
    omega
  have hp := pad_le_of_fits _ _ _ K1.fits_first_written hs
  rw [hr] at hp
  rw [eP, eR]
  exact ⟨hr, hp, word_of (List.all_eq_true.1 word_first_written n (List.mem_range.2 hn))⟩

/-- **A SEGMENT's LATER SENDING, EVERY MESSAGE.** -/
theorem public_later (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A) {l : Nat} (hl : l < 25)
    (d : Bool) :
    0 < (jobLaterAt S A.Z A.G l d).P.sent.size ∧ ∀ n, n < (jobLaterAt S A.Z A.G l d).P.sent.size →
      (jobLaterAt S A.Z A.G l d).ride n = none ∧
        (stepsOf (jobLaterAt S A.Z A.G l d).P.codes (shapeAt (jobLaterAt S A.Z A.G l d).P n) none).pad ≤
          ((jobLaterAt S A.Z A.G l d).P.codes.base.getD (shapeAt (jobLaterAt S A.Z A.G l d).P n).code default).ell ∧
        ((shapeAt (jobLaterAt S A.Z A.G l d).P n).mainRows = 0 ∨
          (shapeAt (jobLaterAt S A.Z A.G l d).P n).answers ≠ 0) := by
  have eP := plan_later h hA l d
  have t := List.all_eq_true.1 (List.all_eq_true.1 word_later_written l (List.mem_range.2 hl)) d (by cases d <;> simp)
  rw [Bool.and_eq_true] at t
  have hf : K1.sendFits (VerifiableInference.Desc.K1.placeL l d) (rideOf none) = true := by
    have e := List.all_eq_true.1 K1.fits_later_written l (List.mem_range.2 hl)
    rw [Bool.and_eq_true] at e
    cases d with
    | true => exact e.2
    | false => exact e.1
  rw [eP]
  refine ⟨of_decide_eq_true t.1, fun n hn => ⟨rfl, pad_le_of_fits _ _ _ hf hn,
    word_of (List.all_eq_true.1 t.2 n (List.mem_range.2 hn))⟩⟩

/-- **THE FIRST SEGMENT's FRESH MASK.** -/
theorem fresh_opening (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A) :
    (jobTwoAt S A.Z A.G).ride 3 = some ⟨8, 0⟩ ∧
      maskStart (jobTwoAt S A.Z A.G).P (jobTwoAt S A.Z A.G).ride 3 = 8411 ∧
      (dueR (jobTwoAt S A.Z A.G).P (jobTwoAt S A.Z A.G).ride).e = 8958 ∧
      ∀ k, k ≤ 273 → maskStart (jobTwoAt S A.Z A.G).P (jobTwoAt S A.Z A.G).ride 3 + (2 * k + 1) ≤
        (dueR (jobTwoAt S A.Z A.G).P (jobTwoAt S A.Z A.G).ride).e := by
  rw [plan_two h hA, ride_two h hA]
  obtain ⟨-, -, -, r4, r5⟩ := K1.room_first_written
  refine ⟨ride_first_written.2, r4, r5, fun k hk => ?_⟩
  rw [r4, r5]
  omega

end AtFullSide.K10

#print axioms AtFullSide.K10.word_of
#print axioms AtFullSide.K10.word_first_written
#print axioms AtFullSide.K10.word_later_written
#print axioms AtFullSide.K10.word_can_fail
#print axioms AtFullSide.K10.ride_first_written
#print axioms AtFullSide.K10.plan_two
#print axioms AtFullSide.K10.ride_two
#print axioms AtFullSide.K10.plan_later
#print axioms AtFullSide.K10.public_opening
#print axioms AtFullSide.K10.public_later
#print axioms AtFullSide.K10.fresh_opening
