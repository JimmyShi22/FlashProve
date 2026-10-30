-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/K11Tests/LettersSevenInScope.lean: SEVEN FACTS ON THE LETTERS OF THE MERGE OF THE
CLAIMS ON THE COMMITTED TABLE (kind K11) HOLD AT ALL PUBLIC FILES IN THE GOALS' SCOPE, UNDER THE
FIRST ENTRY PIN. They are the fields roomLeft, idxSeat, idxShape, idxRows, niIs, ellPow and inM of
the list of what is left beneath the named condition for that kind, AT THE LETTERS
k := 0, ni := 256, L := LFull. Statements and proofs. The closed facts are by Lean's kernel.

THE TOOL:
  pair_at_seat      the member that xAt finds at a seat has, with that seat, one of the written
                    pairs (shape, seat) of the first chain's entries with a sample
  shapeI_in_scope · shapeM_in_scope   so the member at (1, 0) has the written message number 4's
                    shape, and the member at (73, 2) number 181's
CLOSED, AT THE WRITTEN VALUES:
  pairsI_full · pairsM_full   every written pair at (1, 0) | (73, 2) has that shape
  thereI_full · thereM_full   and there is such a pair: the two facts above are not idle
  pairsI_not                  the negative twin: number 5's shape it has not
  numsI_full    message 4: one mask row; its mask code's length is 256, with logarithm 8
  numsM_full    message 181: one mask row; its mask code's length is 8192
  free_full     the fresh ledger of message 4 has 255 free entries
THE SEVEN: roomLeft_in_scope (GENERAL IN fvs: at most 24 of 24 flags are set) · idxSeat_at and
  indexNo_at_cut (CALLS of other files' theorems) · idxShape_in_scope · idxRows_in_scope ·
  niIs_in_scope · ellPow_in_scope · inM_in_scope (for every n ≤ 8192)

PREMISES THAT ARE NOT PAID HERE: hy, the first entry pin · hn of inM_in_scope (the field has the
merge's number of slots there) · hi of idxSeat_at and indexNo_at_cut (the index masks' seat).

Limits. That the premises can be met together is not shown here. The full size alone. Nothing on a
verifier's state. Nothing on soundness.

-/
import Johnson.Desc.Sound.K11Tests.ToldAtCut
import Johnson.Top.H0.Fill.D1At
import Johnson.Top.H0.MergeLaw.MaskRow
import Johnson.Top.H0.Walk.FrameEntriesDefs
import Johnson.HB.LLHARD.PlanAtQFull
import Johnson.P5T.MembersByMake
import Johnson.Desc.Ok.PlanWritten.SizedTestLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LT28.K11Tests

open OnBytes (OracleShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.FillP1 (free0Of)
open VerifiableInference.Desc.First.MergeLaw (posMask)
open VerifiableInference.Desc.K13.Law (LFull MFull msgs_at indexSeat_written planIndexSeat_gives
  indexNo_of)
open VerifiableInference.Desc.K12.Door (msgsOfChain)
open VerifiableInference.Desc.Sound (Mem seatOf xAt InMsg)
open VerifiableInference.PlanWritten (madePinnedAt cutFirstFull codes_written)
open VerifiableInference.PlanWritten.Joined (first_written_in_scope sends_in_scope)
open Johnson.Desc.First.Walk.Tied (rowsBefore)
open Johnson.G (codesFull2)
open Johnson.Pack (pMask)

/-! ## 1 Closed facts, by the kernel -/

/-- The written pairs (shape, seat) of the first chain's entries with a sample. -/
def pairsW : List (OracleShape × (ℕ × ℕ)) :=
  (P5T.psFull.filter (·.smpd)).map fun p => (p.shape, p.seat)

theorem pairsI_full :
    (pairsW.all fun y => y.2 != (1, 0) || decide (MFull[4]? = some y.1)) = true := by
  decide +kernel

theorem pairsM_full :
    (pairsW.all fun y => y.2 != (73, 2) || decide (MFull[181]? = some y.1)) = true := by
  decide +kernel

theorem thereI_full : (pairsW.any fun y => y.2 == (1, 0)) = true := by decide +kernel

theorem thereM_full : (pairsW.any fun y => y.2 == (73, 2)) = true := by decide +kernel

/-- The negative twin. -/
theorem pairsI_not :
    (pairsW.all fun y => y.2 != (1, 0) || decide (MFull[5]? = some y.1)) = false := by
  decide +kernel

theorem numsI_full : (MFull[4]?).map (fun s =>
    (s.maskRows, (pMask codesFull2 s).ell, (pMask codesFull2 s).logEll)) = some (1, 256, 8) := by
  decide +kernel

theorem numsM_full : (MFull[181]?).map (fun s => (s.maskRows, (pMask codesFull2 s).ell)) =
    some (1, 8192) := by decide +kernel

theorem free_full : free0Of codesFull2 MFull 4 = 255 := by decide +kernel

/-! ## 2 The tool -/

section
variable {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub} {D : OnBytes.Maker.WholeD}
  {r : LPFD.Full.RunPF}

/-- The codes, as read back, are the written ones. -/
theorem codes_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    Z.first.codes = codesFull2 :=
  (first_written_in_scope hW h hy).1.trans codes_written

/-- **The member that xAt finds at a seat has one of the written pairs.** -/
theorem pair_at_seat (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) (rad : ℕ → ℕ → ℕ) {t : ℕ × ℕ}
    {x : Mem} (hx : xAt (P5T.msAtR Z rad) t = some x) : ((x.1.l.get x.2).1, t) ∈ pairsW := by
  have hs := seat_of_xAt hx
  have hm : x ∈ P5T.msAtR Z rad := by
    unfold xAt at hx
    exact List.mem_of_find?_eq_some hx
  have a : ((x.1.l.get x.2).1, seatOf x) ∈
      (P5T.msAtR Z rad).map (fun x => ((x.1.l.get x.2).1, seatOf x)) :=
    List.mem_map.2 ⟨x, hm, rfl⟩
  have b := (P5T.memsSame_atR Z rad _).1 a
  rw [(P5T.seats_in_scope hW h hy hl).1, hs] at b
  exact b

/-- The member at (1, 0) has the written message number 4's shape. -/
theorem shapeI_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) (rad : ℕ → ℕ → ℕ) {x : Mem}
    (hx : xAt (P5T.msAtR Z rad) (1, 0) = some x) : MFull[4]? = some (x.1.l.get x.2).1 := by
  have a := List.all_eq_true.1 pairsI_full _ (pair_at_seat hW h hy hl rad hx)
  rcases Eq.mp (Bool.or_eq_true _ _) a with c | c
  · have c' : (((1, 0) : ℕ × ℕ) != (1, 0)) = true := c
    exact absurd c' (by decide)
  · exact of_decide_eq_true c

/-- The member at (73, 2) has the written message number 181's shape. -/
theorem shapeM_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) (rad : ℕ → ℕ → ℕ) {x : Mem}
    (hx : xAt (P5T.msAtR Z rad) (73, 2) = some x) : MFull[181]? = some (x.1.l.get x.2).1 := by
  have a := List.all_eq_true.1 pairsM_full _ (pair_at_seat hW h hy hl rad hx)
  rcases Eq.mp (Bool.or_eq_true _ _) a with c | c
  · have c' : (((73, 2) : ℕ × ℕ) != (73, 2)) = true := c
    exact absurd c' (by decide)
  · exact of_decide_eq_true c

/-! ## 3 The seven -/

/-- **roomLeft**, at the index masks' message's number 4; general in fvs. -/
theorem roomLeft_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) (fvs : List Bool) :
    0 < free0Of Z.first.codes (msgsOfChain Z.made.proof.1) 4 - rowsBefore fvs 24 := by
  rw [codes_in_scope hW h hy, msgs_at (congrArg Prod.fst (sends_in_scope hW h hy)), free_full]
  have b : rowsBefore fvs 24 ≤ 24 := by
    unfold rowsBefore
    exact (List.length_filter_le _ _).trans (List.length_take_le _ _)
  omega

/-- **idxShape.** -/
theorem idxShape_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) (rad : ℕ → ℕ → ℕ) {xI : Mem}
    (hx : xAt (P5T.msAtR Z rad) (1, 0) = some xI) :
    (msgsOfChain Z.made.proof.1)[4]? = some (xI.1.l.get xI.2).1 := by
  rw [msgs_at (congrArg Prod.fst (sends_in_scope hW h hy))]
  exact shapeI_in_scope hW h hy hl rad hx

/-- The three numbers of the member at (1, 0). -/
theorem numsI_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) (rad : ℕ → ℕ → ℕ) {xI : Mem}
    (hx : xAt (P5T.msAtR Z rad) (1, 0) = some xI) :
    (xI.1.l.get xI.2).1.maskRows = 1 ∧ (pMask Z.first.codes (xI.1.l.get xI.2).1).ell = 256 ∧
      (pMask Z.first.codes (xI.1.l.get xI.2).1).logEll = 8 := by
  have n := numsI_full
  rw [shapeI_in_scope hW h hy hl rad hx] at n
  have e := Prod.mk.inj (Option.some.inj n)
  rw [codes_in_scope hW h hy]
  exact ⟨e.1, (Prod.mk.inj e.2).1, (Prod.mk.inj e.2).2⟩

/-- **idxRows**, at k := 0. -/
theorem idxRows_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) (rad : ℕ → ℕ → ℕ) {xI : Mem}
    (hx : xAt (P5T.msAtR Z rad) (1, 0) = some xI) : (xI.1.l.get xI.2).1.maskRows = 2 ^ 0 :=
  (numsI_in_scope hW h hy hl rad hx).1

/-- **niIs**, at k := 0 and ni := 256. -/
theorem niIs_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) (rad : ℕ → ℕ → ℕ) {xI : Mem}
    (hx : xAt (P5T.msAtR Z rad) (1, 0) = some xI) :
    2 ^ (0 + (pMask Z.first.codes (xI.1.l.get xI.2).1).logEll) = 256 := by
  rw [(numsI_in_scope hW h hy hl rad hx).2.2]
  decide

/-- **ellPow.** -/
theorem ellPow_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) (rad : ℕ → ℕ → ℕ) {xI : Mem}
    (hx : xAt (P5T.msAtR Z rad) (1, 0) = some xI) :
    (pMask Z.first.codes (xI.1.l.get xI.2).1).ell =
      2 ^ (pMask Z.first.codes (xI.1.l.get xI.2).1).logEll := by
  rw [(numsI_in_scope hW h hy hl rad hx).2.1, (numsI_in_scope hW h hy hl rad hx).2.2]
  decide

/-- **inM**, for every number of slots up to 8192. -/
theorem inM_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) (rad : ℕ → ℕ → ℕ) {xM : Mem}
    (hx : xAt (P5T.msAtR Z rad) (73, 2) = some xM) {n : ℕ} (hn : n ≤ 8192) :
    ∀ j, j < n → InMsg Z.first.codes (xM.1.l.get xM.2).1 (posMask 0 j).1 (posMask 0 j).2.1
      (posMask 0 j).2.2 := by
  intro j hj
  have m := numsM_full
  rw [shapeM_in_scope hW h hy hl rad hx] at m
  have e := Prod.mk.inj (Option.some.inj m)
  show InMsg Z.first.codes (xM.1.l.get xM.2).1 true (j % 2 ^ 0) (j / 2 ^ 0)
  unfold InMsg
  rw [if_pos rfl, codes_in_scope hW h hy, e.1, e.2, Nat.pow_zero, Nat.div_one]
  exact ⟨Nat.mod_lt _ Nat.one_pos, Nat.lt_of_lt_of_le hj hn⟩

end

/-- **idxSeat**, at L := LFull: a call. -/
theorem idxSeat_at {N : Numbers} (hi : N.index = (1, 0)) (hn : N.indexNo = 4) :
    LFull.places[N.indexNo]? = some N.index := planIndexSeat_gives (indexSeat_written hi hn)

/-- The index masks' message's number, where the cut is the written one: a call. -/
theorem indexNo_at_cut {N : Numbers} (hi : N.index = (1, 0)) {St Cl : Type}
    {bs : List (Block St Cl)} (hc : VerifiableInference.PlanWritten.cutOf bs = cutFirstFull)
    (ps : List Place) : (N.withTold ps (Sound.toldOf bs)).indexNo = 4 :=
  indexNo_of hi (counts_of_cut hc).2 ps

end LT28.K11Tests

#print axioms LT28.K11Tests.pairsI_full
#print axioms LT28.K11Tests.pairsM_full
#print axioms LT28.K11Tests.thereI_full
#print axioms LT28.K11Tests.thereM_full
#print axioms LT28.K11Tests.pairsI_not
#print axioms LT28.K11Tests.numsI_full
#print axioms LT28.K11Tests.numsM_full
#print axioms LT28.K11Tests.free_full
#print axioms LT28.K11Tests.codes_in_scope
#print axioms LT28.K11Tests.pair_at_seat
#print axioms LT28.K11Tests.shapeI_in_scope
#print axioms LT28.K11Tests.shapeM_in_scope
#print axioms LT28.K11Tests.roomLeft_in_scope
#print axioms LT28.K11Tests.idxShape_in_scope
#print axioms LT28.K11Tests.numsI_in_scope
#print axioms LT28.K11Tests.idxRows_in_scope
#print axioms LT28.K11Tests.niIs_in_scope
#print axioms LT28.K11Tests.ellPow_in_scope
#print axioms LT28.K11Tests.inM_in_scope
#print axioms LT28.K11Tests.idxSeat_at
#print axioms LT28.K11Tests.indexNo_at_cut
