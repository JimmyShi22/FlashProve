-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/SeatsAtTwo.lean: THREE FIELDS OF THE RECORD K1Seated
(Honest/K1/Seated.lean) AT THE FIRST SEGMENT's OPENING, NUMBER 2 OF THE FIRST CHAIN, UNDER THE
LIBRARY's HEAD: seats, numbered, sits: in the record's own text, at the head's numbers, list of
seats and members (P5J.At.N, P5J.At.seats, P5J.At.ms) and at the plan of the description's own
ground (K1.firstPar Bs.G₀.first (K1.gpOf Zp)). PUBLIC DATA ALONE. One definition with code,
statements and their proofs.

HOW. The seal ties each letter to a written constant under the head
(Johnson/Desc/K1/Law/TiesAtAll.lean, TestsAtAll.lean, PinsAtHead.lean;
Johnson/P5T/PlanSeatsTie.lean, MembersByMake.lean): the plan is parGF; the numbers' seats are
N0Full's; the index masks' seat is (1, 0); the list of seats is seatsFull; the plan's seats are
psFull; no tree and no message is counted in front of number 2. At these constants the three fields
are closed facts, by Lean's kernel.

  sampledNos                     the numbers of a plan's sampled messages, with code
  placeW, seatsW, numberedW, sitsW   the closed facts at the written constants
  seats_two, numbered_two, sits_two  THE THREE FIELDS

Limits. THE HEAD IS A HYPOTHESIS; O (how the description is opened) is a binder, as in the seal's
own laws; treesNo is taken as a premise in the record's own text. THE PLAN IS THE DESCRIPTION's
GROUND's: that it is the plan of the prover that a filling makes is another file's. numbered ends in
the table's own count of messages in front of the place, where the record has the job's first
number: firstNo joins them. Number 2 alone. THE FULL SIZE ALONE. Evaluations in Lean's kernel
(decide +kernel): no compiled code. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Seated
import Johnson.Desc.K1.Law.TiesAtAll
import Johnson.Desc.K1.Law.PinsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S Numbers sameMembers)
open VerifiableInference.Desc.Sound (Mem SitsAt seatOf)
open VerifiableInference.Desc.K1 (parGF psF seatOfMsg)
open VerifiableInference.Desc.K13.Law (seatsFull)
open P5T (N0Full psFull)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)
open Johnson.Prover.Send (shapeAt)

/-! ## 1 At the written constants -/

/-- The numbers of a plan's sampled messages. -/
def sampledNos (P : K1.Par) : List Nat :=
  (List.range P.sent.size).filter fun n => decide ((shapeAt P n).answers ≠ 0)

theorem mem_sampledNos {P : K1.Par} {n : Nat} :
    n ∈ sampledNos P ↔ n < P.sent.size ∧ (shapeAt P n).answers ≠ 0 := by
  unfold sampledNos
  rw [List.mem_filter, List.mem_range, decide_eq_true_eq]

theorem mem_of_same {a b : List (Nat × Nat)} (h : sameMembers a b = true) (x : Nat × Nat) :
    x ∈ a ↔ x ∈ b := by
  unfold sameMembers at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  exact ⟨fun hx => List.contains_iff_mem.1 (h.1 x hx),
    fun hx => List.contains_iff_mem.1 (h.2 x hx)⟩

set_option maxRecDepth 1000000 in
/-- The written list of places has the written plan's place at number 2. -/
theorem placeW : psF[2]? = some parGF.place := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The seats that the written numbers pin at the opening are just the written plan's sampled
messages' seats, behind no tree. -/
theorem seatsW : sameMembers (N0Full.sent 0 0 ++ [(1, 0)])
    ((sampledNos parGF).map (seatOfMsg parGF 0)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Each of these seats stands in the written list of seats, first at the message's own number. -/
theorem numberedW : ((sampledNos parGF).all fun n =>
    seatsFull.contains (seatOfMsg parGF 0 n) &&
      decide (seatsFull.idxOf (seatOfMsg parGF 0 n) = n)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- At each of these seats a sampled seat of the written plan's list stands, and each that stands
there has the message's shape. -/
theorem sitsW : ((sampledNos parGF).all fun n =>
    ((psFull.filter (·.smpd)).any fun p => decide (p.seat = seatOfMsg parGF 0 n)) &&
      (psFull.filter (·.smpd)).all fun p =>
        decide (p.seat = seatOfMsg parGF 0 n → p.shape = shapeAt parGF n)) = true := by
  decide +kernel

/-! ## 2 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- No tree is stated in front of number 2. -/
theorem trees_two (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (treesNo : treesTo cF.blocksInOrder 2 =
      (P5J.At.N Zp cF).treesAt (some (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).place)) :
    treesTo cF.blocksInOrder 2 = 0 := by
  rw [treesNo, K1.eG_atAll h O (K1.pin1_atAll h), ← placeW]
  exact (K1.nums_atAll h O (K1.pin1_atAll h) (K1.pin2_atAll h)).1.2

/-- **seats**, in the record's own text. -/
theorem seats_two (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (treesNo : treesTo cF.blocksInOrder 2 =
      (P5J.At.N Zp cF).treesAt (some (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).place)) :
    ∀ y, y ∈ pinsAtSort (P5J.At.N Zp cF) .opening ↔
      ∃ n, n < (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).sent.size ∧
        (shapeAt (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n).answers ≠ 0 ∧
        y = seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n := by
  intro y
  have eT := trees_two h O treesNo
  have eS : (P5J.At.N Zp cF).sent = N0Full.sent :=
    congrArg (·.sent) (K1.atAll_letters h O (K1.pin1_atAll h)).1
  have eI : (P5J.At.N Zp cF).index = (1, 0) := K1.index_atAll h O (K1.pin1_atAll h)
  unfold seatAtMember
  rw [eT, K1.eG_atAll h O (K1.pin1_atAll h)]
  show y ∈ (P5J.At.N Zp cF).sent 0 0 ++ [(P5J.At.N Zp cF).index] ↔ _
  rw [eS, eI, mem_of_same seatsW y, List.mem_map]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, (mem_sampledNos.1 hn).1, (mem_sampledNos.1 hn).2, rfl⟩
  · rintro ⟨n, h1, h2, rfl⟩
    exact ⟨n, mem_sampledNos.2 ⟨h1, h2⟩, rfl⟩

/-- **numbered**, in the record's own text, with the table's count of messages in front of the place
where the record has the job's first number. -/
theorem numbered_two (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (treesNo : treesTo cF.blocksInOrder 2 =
      (P5J.At.N Zp cF).treesAt (some (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).place)) :
    ∀ n, n < (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).sent.size →
      (shapeAt (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n).answers ≠ 0 →
      seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n ∈ P5J.At.seats Zp ∧
        (P5J.At.seats Zp).idxOf
            (seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n) =
          (P5J.At.N Zp cF).msgsAt (some (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).place) + n := by
  have eT := trees_two h O treesNo
  have eM : (P5J.At.N Zp cF).msgsAt psF[2]? = 0 :=
    (K1.nums_atAll h O (K1.pin1_atAll h) (K1.pin2_atAll h)).1.1
  unfold seatAtMember
  rw [eT, K1.eG_atAll h O (K1.pin1_atAll h), (K1.atAll_letters h O (K1.pin1_atAll h)).2.1,
    ← placeW, eM]
  intro n h1 h2
  have hw := List.all_eq_true.1 numberedW n (mem_sampledNos.2 ⟨h1, h2⟩)
  rw [Bool.and_eq_true, decide_eq_true_eq] at hw
  exact ⟨List.contains_iff_mem.1 hw.1, by rw [hw.2, Nat.zero_add]⟩

/-- **sits**, in the record's own text. -/
theorem sits_two (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (treesNo : treesTo cF.blocksInOrder 2 =
      (P5J.At.N Zp cF).treesAt (some (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).place)) :
    ∀ n, n < (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).sent.size →
      (shapeAt (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n).answers ≠ 0 →
      (∃ m ∈ P5J.At.ms Zp Z.lay,
          SitsAt m (seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n).1
            (seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n).2) ∧
      ∀ m ∈ P5J.At.ms Zp Z.lay,
          SitsAt m (seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n).1
            (seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n).2 →
          (m.1.l.get m.2).1 = shapeAt (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n := by
  have eT := trees_two h O treesNo
  have eP := (P5T.seats_in_scope h.scope h.laid.pub (K1.pin1_atAll h) (K1.laidP_atAll h)).1
  have hM : ∀ y : OnBytes.OracleShape × (Nat × Nat),
      y ∈ (P5J.At.ms Zp Z.lay).map (fun m => ((m.1.l.get m.2).1, seatOf m)) ↔
        y ∈ (psFull.filter (·.smpd)).map fun p => (p.shape, p.seat) := by
    intro y
    have e := P5T.memsSame_atR Zp (P5J.At.rad Zp Z.lay) y
    rw [eP] at e
    exact e
  unfold seatAtMember
  rw [eT, K1.eG_atAll h O (K1.pin1_atAll h)]
  intro n h1 h2
  have hw := List.all_eq_true.1 sitsW n (mem_sampledNos.2 ⟨h1, h2⟩)
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
    have hs' : seatOf m = seatOfMsg parGF 0 n := hs
    rw [← e1]
    exact of_decide_eq_true (hall q hq) (e2.trans hs')

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.placeW
#print axioms ProofFile.Honest.K1.seatsW
#print axioms ProofFile.Honest.K1.numberedW
#print axioms ProofFile.Honest.K1.sitsW
#print axioms ProofFile.Honest.K1.seats_two
#print axioms ProofFile.Honest.K1.numbered_two
#print axioms ProofFile.Honest.K1.sits_two
#print axioms ProofFile.Honest.K1.sampledNos
#print axioms ProofFile.Honest.K1.mem_sampledNos
#print axioms ProofFile.Honest.K1.mem_of_same
#print axioms ProofFile.Honest.K1.trees_two
