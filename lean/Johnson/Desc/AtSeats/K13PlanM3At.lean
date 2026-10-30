-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/K13PlanM3At.lean: KIND K13's PREMISE hPl, PAID AT THE CLOSED
CONSTANT (P5J.mgAtAll) UNDER THE ACCEPT OF THE ENTRY TESTS' TWO COMPARISONS WITH WRITTEN VALUES.
hPl is the binder PlanM3 (d12Of f).L (d12Of f).M hA.𝔇.ms hA.𝔇.cs hA.𝔇.N of k13_kind_row, a
theorem that is not in this tree:
five facts on the list of rounds with each round's error bound
(Johnson/Desc/K13/Law/PlanTestsM3.lean: hL, hshape, hcode, hlen, hbelow).

OBJECT. The five fields at the constant's own letters: L, M: the seats and the shapes of the first
chain's oracle messages (f's, tied by two equations hLs, hMs); ms: the sampled oracle messages,
made off the seats that P5T.planSeats lists (P5J.At.ms); cs: the first chain's codes (P5J.At.cs);
N: the table's numbers (P5J.At.N: laid off these seats and off what the first chain's
sub-protocols tell).
USER. planM3_atAll was written for k13_kind_row's caller (the binder hPl falls; hP1 and hP2 come
in); no other file of this tree names it. planM3_written is called in K13KindTight.lean and
K13KindRowB.lean beside this file and in Johnson/Desc/K1/Law/PlanM3AtAll.lean. Beside, the two small
numbers to which Johnson/Desc/AtSeats/K13KindRow3.lean brings hbase down, both called in
K13KindRowB.lean:
hi : hA.𝔇.N.index.1 ≤ 1 (under hP1) and hn : 1 ≤ inFront355 cF (under hP2).
LETTERS. o, Zl, D, r₀, Zp, Np, cF, x₀, f: the row's own.

The two premises that come in, each a test with code on public data:
  hP1  madePinnedAt … = true (Johnson/Desc/Ok/PlanWritten/MadeTest.lean): sizes, lists of rounds
       and sendings are the written ones.
  hP2  cutIs (F0T o Zp Np cF) = true (Johnson/Desc/Ok/PlanWritten/CutTest.lean): the cut of the
       three chains into sub-protocols is the written one.
That "the value is laid" gives both accepts is pins_of_laid (Johnson/Goal/Skeleton/PinsOfLaid.lean)
with cutIs_of_laid (CutIsOfLaid.lean beside it). This file calls neither,
so both stand as premises here.

Field by field: the closed fact, whose it is, and its negative test.
  hL      indexSeat_written (Johnson/HB/LLHARD/PlanAtQFull.lean) · indexSeat_rejects
  hshape  HERE. The test reads of a member its shape and its seat alone; by
          memsSame_atR these pairs are those of the listed seats with a sample; the radii fall
          out: planIndexShape_atR (proved, general; no example). Then Lean's kernel at the written
          seats: indexShape_written · indexShape_sits (a member does sit at the index masks'
          seat: the accept is not for want of a member) · indexShape_rejects,
          indexShape_seat_rejects
  hcode   indexCode_written (the same file) · indexCode_rejects
  hlen    lengthsOk_of_pub (Johnson/Goal/Numbers/LengthsOkWritten.lean: the maker of the public part
          refuses otherwise: proved, general) · lengthsOk_rejects
  hbelow  planBelow_cut (Johnson/HB/LLHARD/CountsAtCut.lean) with planBelow_withTold ·
          planBelow_cut_rejects
  the numbers: N.index = (1, 0) by N0Full_seats and seats_in_scope (Johnson/P5T/PlanSeatsTie.lean)
          · N.indexNo = 4 by indexNo_of at treesAre_cut.
Main names.
  told_of_cut       what the first chain's sub-protocols tell is the written cut's list
  planM3_written    the five fields at LFull, MFull and the constant's ms, cs, N
  **planM3_atAll**  hPl, to the letter, from hA, hLs, hMs (two fields of the row's hR), hP1, hP2



  index_atAll, indexTree_atAll   N.index = (1, 0); so hi
  inFront355_of_cut, inFront_written, inFront_rejects, inFront355_atAll   the rounds that the first
                    355 sub-protocols declare are the written cut's; their number, by Lean's kernel;
                    the negative test (one sub-protocol fewer: another number); so hn

By evaluations in Lean's kernel (decide +kernel): the four facts named indexShape_…, inFront_written
and inFront_rejects; at each the recursion limit is raised (maxRecDepth 1000000), as in the files of
closed facts beneath.
What is not claimed. That hP1 or hP2 accept at any files. No member of the head hA. Nothing on
soundness.

-/
import Johnson.Desc.AtSeats.K13LawAt9F
import Johnson.Desc.AtSeats.K13LawTop
import Johnson.P5J.MgAtAll
import Johnson.HB.LLHARD.PlanInScope
import Johnson.HB.LLHARD.CountsAtCut
import Johnson.Goal.Numbers.LengthsOkWritten
import Johnson.P5T.PlanSeatsTie
import Johnson.P5T.MembersByMake
import Johnson.Desc.Ok.PlanWritten.CutTestLaws
import Johnson.Desc.First.CutAtNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law

open OnBytes OnBytes.Maker Johnson.G
open VerifiableInference.Desc (Chain Place Oracle)
open VerifiableInference.Desc.First (S Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound (Mem seatOf linksFull)
open VerifiableInference.PlanWritten (madePinnedAt cutIs cutIs_eq cutOf cutFirstFull
  toldRounds_flat)
open ProofFile (Cl)

/-! ## hshape over the listed seats -/

/-- The test planIndexShapeB, on the listed seats with a sample. -/
def indexShapeP (ps : List P5T.PSeat) (M : List OracleShape) (seat : ℕ × ℕ) (no : ℕ) : Bool :=
  (ps.filter (·.smpd)).all fun p => !(p.seat == seat) || (M[no]? == some p.shape)

/-- **At the members made off the listed seats the test reads these seats alone**: no radius. -/
theorem planIndexShape_atR (Z : ProofFile.Pub) (rad : ℕ → ℕ → ℕ) (M : List OracleShape) (N : Numbers) :
    planIndexShapeB (P5T.msAtR Z rad) M N =
      indexShapeP (P5T.planSeats Z Z.D.1) M N.index N.indexNo := by
  have e1 : planIndexShapeB (P5T.msAtR Z rad) M N =
      (((P5T.msAtR Z rad).map fun x => ((x.1.l.get x.2).1, seatOf x)).all
        fun y => !(y.2 == N.index) || (M[N.indexNo]? == some y.1)) := by
    unfold planIndexShapeB
    rw [List.all_map]
    rfl
  have e2 : indexShapeP (P5T.planSeats Z Z.D.1) M N.index N.indexNo =
      ((((P5T.planSeats Z Z.D.1).filter (·.smpd)).map fun p => (p.shape, p.seat)).all
        fun y => !(y.2 == N.index) || (M[N.indexNo]? == some y.1)) := by
    unfold indexShapeP
    rw [List.all_map]
    rfl
  rw [e1, e2, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun h y hy => h y ((P5T.memsSame_atR Z rad y).2 hy),
    fun h y hy => h y ((P5T.memsSame_atR Z rad y).1 hy)⟩

set_option maxRecDepth 1000000 in
/-- **The accept at the written values.** -/
theorem indexShape_written : indexShapeP P5T.psFull MFull (1, 0) 4 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- It does not accept for want of a member: a seat with a sample is the index masks'. -/
theorem indexShape_sits :
    ((P5T.psFull.filter (·.smpd)).any fun p => p.seat == (1, 0)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the oracle message's number one more. -/
theorem indexShape_rejects : indexShapeP P5T.psFull MFull (1, 0) 5 = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: at W's seat the shape is another. -/
theorem indexShape_seat_rejects : indexShapeP P5T.psFull MFull (82, 0) 4 = false := by
  decide +kernel

/-! ## What the sub-protocols tell -/

/-- **Where the first chain's cut is the written one, what its sub-protocols tell is the written
cut's list.** -/
theorem told_of_cut {cF : Chain S Cl} (h : cutOf cF.blocksInOrder = cutFirstFull) :
    P5J.At.told cF = cutFirstFull.map fun r => r.2.2.2.2.1.flatMap (·.2) := by
  rw [P5J.At.told_is, ← h]
  unfold cutOf
  rw [List.map_map]
  exact List.map_congr_left fun b _ => (toldRounds_flat b).symm

/-! ## The five fields -/

/-- The index masks' seat, at the constant's numbers: tree 1, tenant 0. -/
theorem index_written {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} (cF : Chain S Cl) (hW : VerifierAndGoals.InScope W = true)
    (hp : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Zp)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r))
    (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    (P5J.At.N Zp cF).index = (1, 0) := by
  show (P5T.numbersOf (P5T.planSeats Zp Zp.D.1)).index = (1, 0)
  rw [(P5T.seats_in_scope hW hp hP1 hl).2.2]
  exact congrArg Prod.fst P5T.N0Full_seats

/-- **The five fields at the written L and M and the constant's own ms, cs, N.** -/
theorem planM3_written {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {cF : Chain S Cl} (hW : VerifierAndGoals.InScope W = true)
    (hp : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Zp)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r))
    (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (hc : cutOf cF.blocksInOrder = cutFirstFull) (lay : ByteArray) :
    PlanM3 LFull MFull (P5J.At.ms Zp lay) (P5J.At.cs Zp) (P5J.At.N Zp cF) := by
  have hs := (P5T.seats_in_scope hW hp hP1 hl).1
  have ht := told_of_cut hc
  have hi : (P5J.At.N Zp cF).index = (1, 0) := index_written cF hW hp hl hP1
  have hn : (P5J.At.N Zp cF).indexNo = 4 :=
    indexNo_of (N := (P5T.numbersOf (P5J.At.pseats Zp)).withRows (P5J.At.shape Zp)
      (First.possAt cF.blocksInOrder P5J.At.links.length) P5J.At.links.length) hi
      (ht ▸ treesAre_cut) P5J.At.ps
  have hcs : P5J.At.cs Zp = codesFull2 := (likeFull_in_scope hW hp hP1).codes
  refine ⟨planIndexSeat_gives (indexSeat_written hi hn), planIndexShape_gives ?_,
    planIndexCode_gives ?_, lengthsOk_of_pub hp, ?_⟩
  · show planIndexShapeB (P5T.msAtR Zp (P5J.At.rad Zp lay)) MFull (P5J.At.N Zp cF) = true
    rw [planIndexShape_atR, hs, hi, hn]
    exact indexShape_written
  · rw [hcs]
    exact indexCode_written hn
  · refine planBelow_withTold _ P5J.At.ps (P5J.At.told cF) ?_
    rw [ht, show P5J.At.ps.length = 358 from places_fit.1]
    exact planBelow_cut

/-- **hPl of k13_kind_row [not in this library], to the letter.** -/
theorem planM3_atAll {o : ProofFile.SecondHashFunctionArgument} {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
    (hA : P5J.AtMgA o Zl D r₀ Zp Np cF x₀) {f : First.FoldData}
    (hLs : P5J.At.laid? Zp = some f.L) (hMs : f.M = (P5J.At.d12 Zp f.L).M)
    (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (hP2 : cutIs (P5J.F0T o Zp Np cF) = true) :
    PlanM3 (d12Of f).L (d12Of f).M hA.𝔇.ms hA.𝔇.cs hA.𝔇.N := by
  have hL : f.L = LFull :=
    Option.some.inj (hLs.symm.trans (laid_in_scope hA.scope hA.laid.pub hP1))
  have hM : f.M = MFull := hMs.trans (msgs_in_scope hA.scope hA.laid.pub hP1)
  show PlanM3 f.L f.M (P5J.At.ms Zp Zl.lay) (P5J.At.cs Zp) (P5J.At.N Zp cF)
  rw [hL, hM]
  exact planM3_written hA.scope hA.laid.pub
    (hA.laid.run ▸ LPFD.Full.laidPOf_of hA.laid.value hA.laid.planOk hA.laid.data hA.laid.asks)
    hP1 (cutIs_eq hP2).1 Zl.lay

/-! ## The two small numbers of hbase -/

/-- The index masks' seat at the constant. -/
theorem index_atAll {o : ProofFile.SecondHashFunctionArgument} {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
    (hA : P5J.AtMgA o Zl D r₀ Zp Np cF x₀)
    (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    hA.𝔇.N.index = (1, 0) :=
  index_written cF hA.scope hA.laid.pub
    (hA.laid.run ▸ LPFD.Full.laidPOf_of hA.laid.value hA.laid.planOk hA.laid.data hA.laid.asks) hP1

/-- **hi.** -/
theorem indexTree_atAll {o : ProofFile.SecondHashFunctionArgument} {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
    (hA : P5J.AtMgA o Zl D r₀ Zp Np cF x₀)
    (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    hA.𝔇.N.index.1 ≤ 1 :=
  Nat.le_of_eq (congrArg Prod.fst (index_atAll hA hP1))

/-- The rounds that the first 355 sub-protocols declare, off the cut. -/
theorem inFront355_of_cut {cF : Chain S Cl} (h : cutOf cF.blocksInOrder = cutFirstFull) :
    inFront355 cF = ((cutFirstFull.map (·.2.2.1)).take 355).sum := by
  unfold inFront355
  rw [List.map_take, First.roundsLen_cut, h]

set_option maxRecDepth 1000000 in
/-- Their number at the written cut. -/
theorem inFront_written : ((cutFirstFull.map (·.2.2.1)).take 355).sum = 48270 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test: with one sub-protocol fewer the number is another. -/
theorem inFront_rejects : ((cutFirstFull.map (·.2.2.1)).take 354).sum ≠ 48270 := by decide +kernel

/-- **hn.** -/
theorem inFront355_atAll {o : ProofFile.SecondHashFunctionArgument} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S Cl}
    (hP2 : cutIs (P5J.F0T o Zp Np cF) = true) : 1 ≤ inFront355 cF := by
  rw [inFront355_of_cut (cF := cF) (cutIs_eq hP2).1, inFront_written]
  decide

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.planIndexShape_atR
#print axioms VerifiableInference.Desc.K13.Law.indexShape_written
#print axioms VerifiableInference.Desc.K13.Law.indexShape_sits
#print axioms VerifiableInference.Desc.K13.Law.indexShape_rejects
#print axioms VerifiableInference.Desc.K13.Law.indexShape_seat_rejects
#print axioms VerifiableInference.Desc.K13.Law.told_of_cut
#print axioms VerifiableInference.Desc.K13.Law.index_written
#print axioms VerifiableInference.Desc.K13.Law.planM3_written
#print axioms VerifiableInference.Desc.K13.Law.planM3_atAll
#print axioms VerifiableInference.Desc.K13.Law.index_atAll
#print axioms VerifiableInference.Desc.K13.Law.indexTree_atAll
#print axioms VerifiableInference.Desc.K13.Law.inFront355_of_cut
#print axioms VerifiableInference.Desc.K13.Law.inFront_written
#print axioms VerifiableInference.Desc.K13.Law.inFront_rejects
#print axioms VerifiableInference.Desc.K13.Law.inFront355_atAll
