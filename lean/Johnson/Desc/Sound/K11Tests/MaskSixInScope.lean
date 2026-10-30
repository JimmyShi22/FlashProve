-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/K11Tests/MaskSixInScope.lean: SIX FACTS ON NUMBERS FOR THE TEST ON THE MASK ROW
OF THE OUTPUT HEAD's SEGMENT (24) HOLD AT ALL PUBLIC FILES IN THE GOALS' SCOPE, UNDER THE FIRST
ENTRY PIN AND TWO MORE NAMED PREMISES. They are the fields maskNo, maskLt, maskNum, maskSeat,
maskOwn and maskBits of other files' list (Johnson/K11R/) of what is left beneath a named condition
for the merge of the claims on the committed table (kind K11), AT THE LETTERS m := 0, O' := 181,
L := LFull. Statements and proofs. The closed facts are by Lean's kernel.

CLOSED, AT THE WRITTEN VALUES:
  no_full       the first message with mask rows of segment 24 is its message 0
  counts_full   segment 24 sends one message at each of its moments 0, 1, 2
  msgs346_full  in front of the border 346 the blocks have told 185 oracle messages in 76 trees
  seat181_full  the written list of seats has (73, 2) at number 181
  own_full      (73, 2) is a sampled tenant of segment 24's group
  bits181_full  the written message number 181 has a number of mask rows with bit count 0
  NEGATIVE TWINS: seat180_not: number 180 is another seat · own_not: (76, 0) is no tenant of that
  group · msgs340_not: at the border 340 the counts are others.
  THAT THE SIX FIT TOGETHER (181 + (1 + 1) + (1 + 1) = 185 + 0) is maskNum_in_scope's last step.
IN SCOPE:
  shape_in_scope · maskNo_in_scope · maskLt_in_scope · maskNum_in_scope · maskSeat_at ·
  maskOwn_in_scope · maskBits_in_scope

PREMISES THAT ARE NOT PAID HERE: hy, the first entry pin (in the entry tests' first thirteen rows) ·
hG, the blank ground has the public part's own request shape · hT, CountsAre told
(Johnson/HB/LLHARD/ToldCounts.lean): the blocks tell the written counts.

Limits. That the premises can be met together is not shown here. The full size alone. Nothing on a
verifier's state. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.MaskMaker
import Johnson.Top.H0.MergeLaw.MaskFront
import Johnson.HB.LLHARD.LaidWritten
import Johnson.HB.LLHARD.ToldCounts
import Johnson.P5T.PlanSeatsTie
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Goal.Numbers.RequestWritten
import Johnson.Desc.Sound.MgAt.K11Members
import Johnson.Desc.Sound.MgAt.K11Places

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LT28.K11Tests

open OnBytes (ceilLog2)
open VerifiableInference.Desc
open VerifiableInference.Desc.First (Numbers flatPlacesOf)
open VerifiableInference.Desc.First.MergeLaw (maskNoOf firstCount momentCount)
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.Desc.K13.Law (LFull MFull countsFull CountsAre told_at msgs_at)
open VerifiableInference.Desc.K12.Door (msgsOfChain)
open VerifiableInference.Desc.Sound (Mem seatOf xAt linksFull)
open VerifiableInference.Desc.Sound.MgAt (mergeAt k11_hp)
open VerifiableInference.PlanWritten (madePinnedAt request_shape_written)
open VerifiableInference.PlanWritten.Joined (first_written_in_scope sends_in_scope)

/-! ## 1 Closed facts, by the kernel -/

theorem no_full : maskNoOf shapeFull 24 = some 0 := by decide +kernel

theorem counts_full : firstCount shapeFull 24 = 1 ∧ momentCount shapeFull 24 1 = 1 ∧
    momentCount shapeFull 24 2 = 1 := by decide +kernel

theorem msgs346_full : countsFull[346]? = some (185, 76) := by decide +kernel

theorem seat181_full : LFull.places[181]? = some (73, 2) := by decide +kernel

theorem own_full : ((73, 2) : ℕ × ℕ) ∈ P5T.N0Full.group 24 := by decide +kernel

theorem bits181_full : (MFull[181]?).map (fun y => ceilLog2 y.maskRows) = some 0 := by
  decide +kernel

/-- The negative twins. -/
theorem seat180_not : LFull.places[180]? ≠ some (73, 2) := by decide +kernel

theorem own_not : ((76, 0) : ℕ × ℕ) ∉ P5T.N0Full.group 24 := by decide +kernel

theorem msgs340_not : countsFull[340]? ≠ some (185, 76) := by decide +kernel

/-! ## 2 In scope -/

section
variable {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}

/-- The request's shape, as read back, is the written one. -/
theorem shape_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    Z.first.shape = shapeFull :=
  (first_written_in_scope hW h hy).2.2.1.trans request_shape_written

/-- **maskNo**, at m := 0. -/
theorem maskNo_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    maskNoOf Z.first.shape 24 = some 0 := by
  rw [shape_in_scope hW h hy]
  exact no_full

/-- **maskLt**, at m := 0. -/
theorem maskLt_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    0 < firstCount Z.first.shape 24 := by
  rw [shape_in_scope hW h hy, counts_full.1]
  exact Nat.one_pos

/-- **maskNum**, at m := 0 and O' := 181. -/
theorem maskNum_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) {G₀ : ProofFile.Ground}
    (hG : G₀.first.shape = Z.first.shape) (N : Numbers) {told : List (List Oracle)}
    (hT : CountsAre told) :
    181 + (firstCount Z.first.shape 24 + 1) +
        (momentCount G₀.first.shape 24 1 + momentCount G₀.first.shape 24 2) =
      (N.withTold (flatPlacesOf linksFull true) told).msgsAt (some mergeAt) + 0 := by
  have e := told_at N hT (k := 346) (by decide)
  rw [msgs346_full, k11_hp] at e
  have e1 : (N.withTold (flatPlacesOf linksFull true) told).msgsAt (some mergeAt) = 185 :=
    (Prod.mk.inj (Option.some.inj e)).1.symm
  rw [hG, shape_in_scope hW h hy, counts_full.1, counts_full.2.1, counts_full.2.2, e1]

/-- **maskBits**, at O' := 181. -/
theorem maskBits_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    ((msgsOfChain Z.made.proof.1)[181]?).map (fun y => ceilLog2 y.maskRows) = some 0 := by
  rw [msgs_at (congrArg Prod.fst (sends_in_scope hW h hy))]
  exact bits181_full

end

/-- The member that xAt finds at a seat sits there. -/
theorem seat_of_xAt {ms : List Mem} {p : ℕ × ℕ} {x : Mem} (hx : xAt ms p = some x) :
    seatOf x = p := by
  unfold xAt at hx
  have h1 : decide (seatOf x = p) = true :=
    List.find?_some (p := fun y => decide (seatOf y = p)) hx
  exact of_decide_eq_true h1

/-- **maskSeat**, at O' := 181 and L := LFull. -/
theorem maskSeat_at {ms : List Mem} {xM : Mem} (hx : xAt ms (73, 2) = some xM) :
    LFull.places[181]? = some (seatOf xM) := by
  rw [seat_of_xAt hx]
  exact seat181_full

/-- **maskOwn.** -/
theorem maskOwn_in_scope {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub} {D} {r}
    (hW : VerifierAndGoals.InScope W = true) (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) {ms : List Mem} {xM : Mem}
    (hx : xAt ms (73, 2) = some xM) (s : OnBytes.Params.ReqShape) (t : ℕ → ℕ) (n : ℕ)
    (ps : List Place) (told : List (List Oracle)) :
    seatOf xM ∈
      (((P5T.numbersOf (P5T.planSeats Z Z.D.1)).withRows s t n).withTold ps told).group 24 := by
  rw [seat_of_xAt hx, (P5T.seats_in_scope hW h hy hl).2.2]
  exact own_full

end LT28.K11Tests

#print axioms LT28.K11Tests.no_full
#print axioms LT28.K11Tests.counts_full
#print axioms LT28.K11Tests.msgs346_full
#print axioms LT28.K11Tests.seat181_full
#print axioms LT28.K11Tests.own_full
#print axioms LT28.K11Tests.bits181_full
#print axioms LT28.K11Tests.seat180_not
#print axioms LT28.K11Tests.own_not
#print axioms LT28.K11Tests.msgs340_not
#print axioms LT28.K11Tests.shape_in_scope
#print axioms LT28.K11Tests.maskNo_in_scope
#print axioms LT28.K11Tests.maskLt_in_scope
#print axioms LT28.K11Tests.maskNum_in_scope
#print axioms LT28.K11Tests.maskBits_in_scope
#print axioms LT28.K11Tests.seat_of_xAt
#print axioms LT28.K11Tests.maskSeat_at
#print axioms LT28.K11Tests.maskOwn_in_scope
