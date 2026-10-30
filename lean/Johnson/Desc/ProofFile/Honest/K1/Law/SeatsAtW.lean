-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/SeatsAtW.lean: THREE FIELDS OF THE RECORD OF PREMISES K1Seated
(Honest/K1/Seated.lean) AT W's SENDING (number 356 of the first chain's flat list), UNDER THE
LIBRARY's HEAD: seats, numbered, sits: in the record's own text, at the sort .w, at the head's
numbers, list of seats and members (P5J.At.N, P5J.At.seats, P5J.At.ms) and at the plan K1.parW
Zp.first (wGp Zp) 4 wMsgFull. PUBLIC DATA ALONE. Twelve theorems; no definition (it names
sampledNos, SeatsAtTwo.lean).

The road is SeatsAtTwo.lean's and SeatsAtFifty.lean's, once more. The library ties each letter to a
written constant under its head: the plan is K1.parWF (parW_written, FitsAtW.lean); the numbers' w
is N0Full's and the list of seats is seatsFull (atAll_letters,
Johnson/Desc/K1/Law/TestsAtAll.lean); the plan's seats are psFull (seats_in_scope,
Johnson/P5T/PlanSeatsTie.lean; memsSame_atR, Johnson/P5T/MembersByMake.lean); the two counts in
front of border 356 are 197 messages and 82 trees (nums_atAll, Johnson/Desc/K1/Law/TiesAtAll.lean).
At these constants the three fields are closed facts, evaluated in Lean's kernel.

  - place356W: the written list of places has the written plan's place at number 356: the sealed
    IM.place_356 (Johnson/IMR/SendsK1.lean) through IM.placesW_full (Johnson/IMR/K8Owed.lean).
  - sampled356W: of the written plan's messages just number 0 has an answer: so none of the tests
    below runs over an empty list.
  - seats356W, numbered356W, sits356W: the three closed facts.
  - seats356W_bites, numbered356W_bites, sits356W_bites: NEGATIVE TESTS: the bent test says no: the
    other pin's seat; one tree further; one answer more in the shape.
  - nums_w: UNDER h, O: the table counts 197 messages in front of the place, and the chain's blocks
    state 82 trees in front of the member. treesNo is no premise: treesNo_atN (TreesNoTold.lean).
  - seats_w, numbered_w, sits_w: UNDER h (the library's head: A HYPOTHESIS) and O (the description
    opened): THE THREE FIELDS. numbered ends in the table's own count of messages in front of the
    place, where the record has the job's first number: firstNo joins them.

Kin in the library. seatsW_written (Johnson/Desc/K1/Law/TiesWritten.lean): seatsFull[197 + j]? =
some (seatOfMsg parWF 82 j) at every message of the plan: numbered356W's first half by content.
W_sits_atAll (TiesAtAll.lean): the library's own two tests on W's seat.

Limits. THE PLAN IS THE DESCRIPTION's PUBLIC PART's: that it is the plan of the prover that a
filling makes is another file's. THE FULL SIZE ALONE. Evaluations in Lean's kernel (decide
+kernel): no compiled code. Nothing on data. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.SeatsAtTwo
import Johnson.Desc.ProofFile.Honest.K1.Law.TreesNoTold
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsAtW
import Johnson.IMR.SendsK1
import Johnson.IMR.K8Owed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S Numbers sameMembers)
open VerifiableInference.Desc.Sound (Mem SitsAt seatOf)
open VerifiableInference.Desc.K1 (parWF psF seatOfMsg)
open VerifiableInference.Desc.K13.Law (seatsFull wMsgFull)
open P5T (N0Full psFull)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)
open Johnson.Prover.Send (shapeAt)

/-! ## 1 At the written constants -/

/-- The written list of places has the written plan's place at number 356. -/
theorem place356W : psF[356]? = some parWF.place := by
  have e := IM.place_356
  rw [IM.placesW_full] at e
  exact e

/-- Of the written plan's messages just number 0 has an answer. -/
theorem sampled356W : sampledNos parWF = [0] := by decide +kernel

/-- The seat that the written numbers pin at W's sending is just the written plan's sampled
message's seat, behind 82 trees. -/
theorem seats356W :
    sameMembers [N0Full.w] ((sampledNos parWF).map (seatOfMsg parWF 82)) = true := by
  decide +kernel

/-- That seat stands in the written list of seats, first at 197 + the message's own number. -/
theorem numbered356W : ((sampledNos parWF).all fun n =>
    seatsFull.contains (seatOfMsg parWF 82 n) &&
      decide (seatsFull.idxOf (seatOfMsg parWF 82 n) = 197 + n)) = true := by decide +kernel

/-- At that seat a sampled seat of the written plan's list stands, and each that stands there has
the message's shape. -/
theorem sits356W : ((sampledNos parWF).all fun n =>
    ((psFull.filter (·.smpd)).any fun p => decide (p.seat = seatOfMsg parWF 82 n)) &&
      (psFull.filter (·.smpd)).all fun p =>
        decide (p.seat = seatOfMsg parWF 82 n → p.shape = shapeAt parWF n)) = true := by
  decide +kernel

/-- A negative test: at the other pin's seat the test on the seats says no. -/
theorem seats356W_bites :
    sameMembers [N0Full.index] ((sampledNos parWF).map (seatOfMsg parWF 82)) = false := by
  decide +kernel

/-- A negative test: one tree further, the test on the numbers says no at each sampled message. -/
theorem numbered356W_bites : ((sampledNos parWF).all fun n =>
    !(seatsFull.contains (seatOfMsg parWF 83 n) &&
      decide (seatsFull.idxOf (seatOfMsg parWF 83 n) = 197 + n))) = true := by decide +kernel

/-- A negative test on the shapes' half: at the true seat, with one answer more in the message's
shape, the test on the members says no at each sampled message. -/
theorem sits356W_bites : ((sampledNos parWF).all fun n =>
    !((psFull.filter (·.smpd)).all fun p =>
      decide (p.seat = seatOfMsg parWF 82 n →
        p.shape = { shapeAt parWF n with answers := (shapeAt parWF n).answers + 1 }))) = true := by
  decide +kernel

/-! ## 2 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- The two counts in front of number 356. -/
theorem nums_w (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    (P5J.At.N Zp cF).msgsAt (some parWF.place) = 197 ∧ treesTo cF.blocksInOrder 356 = 82 := by
  have e : (P5J.At.N Zp cF).msgsAt psF[356]? = 197 ∧ (P5J.At.N Zp cF).treesAt psF[356]? = 82 :=
    (K1.nums_atAll h O (K1.pin1_atAll h) (K1.pin2_atAll h)).2.2.1
  rw [place356W] at e
  exact ⟨e.1, (treesNo_atN Zp cF place356W).trans e.2⟩

/-- **seats**, in the record's own text, at the sort .w. -/
theorem seats_w (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ y, y ∈ pinsAtSort (P5J.At.N Zp cF) .w ↔
      ∃ n, n < (K1.parW Zp.first (wGp Zp) 4 wMsgFull).sent.size ∧
        (shapeAt (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n).answers ≠ 0 ∧
        y = seatAtMember cF.blocksInOrder 356 (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n := by
  intro y
  have eT := (nums_w h O).2
  have eW : (P5J.At.N Zp cF).w = N0Full.w :=
    congrArg (·.w) (K1.atAll_letters h O (K1.pin1_atAll h)).1
  unfold seatAtMember
  rw [eT, parW_written h O]
  show y ∈ [(P5J.At.N Zp cF).w] ↔ _
  rw [eW, mem_of_same seats356W y, List.mem_map]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, (mem_sampledNos.1 hn).1, (mem_sampledNos.1 hn).2, rfl⟩
  · rintro ⟨n, h1, h2, rfl⟩
    exact ⟨n, mem_sampledNos.2 ⟨h1, h2⟩, rfl⟩

/-- **numbered**, in the record's own text, with the table's count of messages in front of the place
where the record has the job's first number. -/
theorem numbered_w (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ n, n < (K1.parW Zp.first (wGp Zp) 4 wMsgFull).sent.size →
      (shapeAt (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n).answers ≠ 0 →
      seatAtMember cF.blocksInOrder 356 (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n ∈ P5J.At.seats Zp ∧
        (P5J.At.seats Zp).idxOf
            (seatAtMember cF.blocksInOrder 356 (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n) =
          (P5J.At.N Zp cF).msgsAt (some (K1.parW Zp.first (wGp Zp) 4 wMsgFull).place) + n := by
  have eT := (nums_w h O).2
  have eM := (nums_w h O).1
  unfold seatAtMember
  rw [eT, parW_written h O, (K1.atAll_letters h O (K1.pin1_atAll h)).2.1, eM]
  intro n h1 h2
  have hw := List.all_eq_true.1 numbered356W n (mem_sampledNos.2 ⟨h1, h2⟩)
  rw [Bool.and_eq_true, decide_eq_true_eq] at hw
  exact ⟨List.contains_iff_mem.1 hw.1, hw.2⟩

/-- **sits**, in the record's own text. -/
theorem sits_w (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ n, n < (K1.parW Zp.first (wGp Zp) 4 wMsgFull).sent.size →
      (shapeAt (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n).answers ≠ 0 →
      (∃ m ∈ P5J.At.ms Zp Z.lay,
          SitsAt m (seatAtMember cF.blocksInOrder 356 (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n).1
            (seatAtMember cF.blocksInOrder 356 (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n).2) ∧
      ∀ m ∈ P5J.At.ms Zp Z.lay,
          SitsAt m (seatAtMember cF.blocksInOrder 356 (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n).1
            (seatAtMember cF.blocksInOrder 356 (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n).2 →
          (m.1.l.get m.2).1 = shapeAt (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n := by
  have eT := (nums_w h O).2
  have eP := (P5T.seats_in_scope h.scope h.laid.pub (K1.pin1_atAll h) (K1.laidP_atAll h)).1
  have hM : ∀ y : OnBytes.OracleShape × (Nat × Nat),
      y ∈ (P5J.At.ms Zp Z.lay).map (fun m => ((m.1.l.get m.2).1, seatOf m)) ↔
        y ∈ (psFull.filter (·.smpd)).map fun p => (p.shape, p.seat) := by
    intro y
    have e := P5T.memsSame_atR Zp (P5J.At.rad Zp Z.lay) y
    rw [eP] at e
    exact e
  unfold seatAtMember
  rw [eT, parW_written h O]
  intro n h1 h2
  have hw := List.all_eq_true.1 sits356W n (mem_sampledNos.2 ⟨h1, h2⟩)
  rw [Bool.and_eq_true, List.any_eq_true, List.all_eq_true] at hw
  obtain ⟨⟨p, hp, hps⟩, hall⟩ := hw
  constructor
  · obtain ⟨m, hm, e⟩ := List.mem_map.1
      ((hM (p.shape, p.seat)).2 (List.mem_map.2 ⟨p, hp, rfl⟩))
    refine ⟨m, hm, ?_⟩
    have e2 : seatOf m = p.seat := congrArg Prod.snd e
    show m.1.seat m.2 = _
    exact e2.trans (of_decide_eq_true hps)
  · intro m hm hs
    obtain ⟨q, hq, e⟩ := List.mem_map.1
      ((hM ((m.1.l.get m.2).1, seatOf m)).1 (List.mem_map.2 ⟨m, hm, rfl⟩))
    have e1 : q.shape = (m.1.l.get m.2).1 := congrArg Prod.fst e
    have e2 : q.seat = seatOf m := congrArg Prod.snd e
    have hs' : seatOf m = seatOfMsg parWF 82 n := hs
    rw [← e1]
    exact of_decide_eq_true (hall q hq) (e2.trans hs')

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.place356W
#print axioms ProofFile.Honest.K1.sampled356W
#print axioms ProofFile.Honest.K1.seats356W
#print axioms ProofFile.Honest.K1.numbered356W
#print axioms ProofFile.Honest.K1.sits356W
#print axioms ProofFile.Honest.K1.seats356W_bites
#print axioms ProofFile.Honest.K1.numbered356W_bites
#print axioms ProofFile.Honest.K1.sits356W_bites
#print axioms ProofFile.Honest.K1.nums_w
#print axioms ProofFile.Honest.K1.seats_w
#print axioms ProofFile.Honest.K1.numbered_w
#print axioms ProofFile.Honest.K1.sits_w
