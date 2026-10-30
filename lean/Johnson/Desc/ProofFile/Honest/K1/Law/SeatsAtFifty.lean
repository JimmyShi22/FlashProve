-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/SeatsAtFifty.lean: THREE FIELDS OF THE RECORD OF PREMISES
K1Seated (Honest/K1/Seated.lean) AT EACH OF THE FIFTY LATER SENDINGS OF THE FIRST CHAIN, UNDER THE
LIBRARY's HEAD: seats, numbered, sits: in the record's own text, at the head's numbers, list of
seats and members (P5J.At.N, P5J.At.seats, P5J.At.ms) and at the plan of the description's own
ground (K1.parL Zp Bs.G₀ l d). PUBLIC DATA ALONE. Eleven theorems; no definition of its own (it
names sampledNos, SeatsAtTwo.lean).

The road is SeatsAtTwo.lean's, fifty times. The library ties each letter to a written constant under
its head: the plan is K1.placeL l d (parL_written, FitsWritten.lean); the numbers' seats are
N0Full's and the list of seats is seatsFull (atAll_letters, Johnson/Desc/K1/Law/TestsAtAll.lean);
the plan's seats are psFull (seats_in_scope, Johnson/P5T/PlanSeatsTie.lean; memsSame_atR,
Johnson/P5T/MembersByMake.lean); the two counts in front of a border are the written list's entry
(nums_of, Johnson/Desc/K1/Law/TiesAtAll.lean). At these constants the three fields are closed facts,
evaluated in Lean's kernel.

  - countsW50: the written list of counts has an entry at each of the fifty borders, and its trees
    are baseL3 l d (of the messages it says nothing: they are read off the same entry). seatsW50,
    numberedW50, sitsW50: the three closed facts.
  - numberedW50_bites, seatsW50_bites, sitsW50_bites: NEGATIVE TESTS: at EACH of the fifty the bent
    test says no: one tree further; the moments exchanged; one answer more in the shape.
  - nums_fifty: UNDER h, O, hl : l < 25: the table counts the written number of messages in front of
    the place, and the chain's blocks state baseL3 l d trees in front of the member. treesNo is no
    premise: treesNo_atN (TreesNoTold.lean) at place_fifty (Johnson/Desc/K1/Law/CallsE.lean).
  - seats_fifty, numbered_fifty, sits_fifty: UNDER h (the library's head: A HYPOTHESIS), O (the
    description opened), hl : l < 25, at both d: THE THREE FIELDS. seats at the sort that the place
    has: "reads l" (d = false), "digits l" (d = true). numbered ends in the table's own count of
    messages in front of the place, where the record has the job's first number: firstNo joins them.

Kin in the library. later_seats, later_seats_of, sampled_at
(Johnson/Desc/AtSeats/PlanRestAtCut.lean): seatsW50 by content: there over all the plan's messages,
each of which is sampled. hP_of (Johnson/Desc/K1/Law/CallsC.lean): the like as a law, without
evaluation. bases_counts (PlanRestAtCut.lean): countsW50's second half.

Limits. THE PLAN IS THE DESCRIPTION's GROUND's: that it is the plan of the prover that a filling
makes is another file's. THE FULL SIZE ALONE. W's sending is not here. Evaluations in Lean's kernel
(decide +kernel): no compiled code. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.SeatsAtTwo
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsWritten
import Johnson.Desc.ProofFile.Honest.K1.Law.TreesNoTold
import Johnson.Desc.K1.Law.CallsE

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S Numbers sameMembers)
open VerifiableInference.Desc.Sound (Mem SitsAt seatOf)
open VerifiableInference.Desc.K1 (psF seatOfMsg placeL baseL3 momL fiftyB fifty_of)
open VerifiableInference.Desc.K13.Law (seatsFull countsFull)
open P5T (N0Full psFull)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)
open Johnson.Prover.Send (shapeAt)
open IM (k1Ix k1PlaceL)

/-! ## 1 At the written constants -/

/-- The written counts at each of the fifty borders: the trees are baseL3's. -/
theorem countsW50 : fiftyB (fun l d => countsFull[14 * l + k1Ix l d + 2]? ==
    some ((((countsFull[14 * l + k1Ix l d + 2]?).map (·.1)).getD 0), baseL3 l d)) = true := by
  decide +kernel

/-- The seats that the written numbers give segment l at the moment are just the written plan's
sampled messages' seats, behind baseL3 l d trees. -/
theorem seatsW50 : fiftyB (fun l d => sameMembers (N0Full.sent l (momL d))
    ((sampledNos (placeL l d)).map (seatOfMsg (placeL l d) (baseL3 l d)))) = true := by
  decide +kernel

/-- Each of these seats stands in the written list of seats, first at the written count of messages
in front and the message's own number. -/
theorem numberedW50 : fiftyB (fun l d => (sampledNos (placeL l d)).all fun n =>
    seatsFull.contains (seatOfMsg (placeL l d) (baseL3 l d) n) &&
      decide (seatsFull.idxOf (seatOfMsg (placeL l d) (baseL3 l d) n) =
        (((countsFull[14 * l + k1Ix l d + 2]?).map (·.1)).getD 0) + n)) = true := by
  decide +kernel

/-- At each of these seats a sampled seat of the written plan's list stands, and each that stands
there has the message's shape. -/
theorem sitsW50 : fiftyB (fun l d => (sampledNos (placeL l d)).all fun n =>
    ((psFull.filter (·.smpd)).any fun p =>
        decide (p.seat = seatOfMsg (placeL l d) (baseL3 l d) n)) &&
      (psFull.filter (·.smpd)).all fun p =>
        decide (p.seat = seatOfMsg (placeL l d) (baseL3 l d) n →
          p.shape = shapeAt (placeL l d) n)) = true := by
  decide +kernel

/-- A negative test: AT EACH OF THE FIFTY, one tree further, the test on the numbers says no. -/
theorem numberedW50_bites : fiftyB (fun l d => !((sampledNos (placeL l d)).all fun n =>
    seatsFull.contains (seatOfMsg (placeL l d) (baseL3 l d + 1) n) &&
      decide (seatsFull.idxOf (seatOfMsg (placeL l d) (baseL3 l d + 1) n) =
        (((countsFull[14 * l + k1Ix l d + 2]?).map (·.1)).getD 0) + n))) = true := by
  decide +kernel

/-- A negative test: AT EACH OF THE FIFTY, with the moments exchanged, the test on the seats says
no. -/
theorem seatsW50_bites : fiftyB (fun l d => !(sameMembers (N0Full.sent l (momL (!d)))
    ((sampledNos (placeL l d)).map (seatOfMsg (placeL l d) (baseL3 l d))))) = true := by
  decide +kernel

/-- A negative test on the shapes' half: AT EACH OF THE FIFTY, at the true seats, with one answer
more in the message's shape, the test on the members says no. -/
theorem sitsW50_bites : fiftyB (fun l d => !((sampledNos (placeL l d)).all fun n =>
    (psFull.filter (·.smpd)).all fun p =>
      decide (p.seat = seatOfMsg (placeL l d) (baseL3 l d) n →
        p.shape = { shapeAt (placeL l d) n with
          answers := (shapeAt (placeL l d) n).answers + 1 }))) = true := by
  decide +kernel

/-! ## 2 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- The two counts in front of each of the fifty. -/
theorem nums_fifty (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {l : ℕ} (hl : l < 25) (d : Bool) :
    (P5J.At.N Zp cF).msgsAt (some (k1PlaceL l d)) =
        (((countsFull[14 * l + k1Ix l d + 2]?).map (·.1)).getD 0) ∧
      treesTo cF.blocksInOrder (K1.noL l d) = baseL3 l d := by
  have hk : 14 * l + k1Ix l d + 2 ≤ 358 := by
    have : k1Ix l d ≤ 6 := by
      unfold k1Ix
      split <;> split <;> omega
    omega
  have hc := eq_of_beq (fifty_of countsW50 l hl d)
  have e := K1.nums_of (K1.atAll_letters h O (K1.pin1_atAll h)).1
    (LPFK9.blockPlaces_full h.scope h.reads O) (K1.atAll_counts (K1.pin2_atAll h)) hk hc
  have hp : psF[14 * l + k1Ix l d + 2]? = some (k1PlaceL l d) := K1.place_fifty l hl d
  rw [hp] at e
  exact ⟨e.1, (treesNo_atN Zp cF (K1.place_fifty l hl d)).trans e.2⟩

/-- **seats**, in the record's own text, at the sort that the place has. -/
theorem seats_fifty (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {l : ℕ} (hl : l < 25) (d : Bool) :
    ∀ y, y ∈ pinsAtSort (P5J.At.N Zp cF) (cond d (.digits l) (.reads l)) ↔
      ∃ n, n < (K1.parL Zp Bs.G₀ l d).sent.size ∧ (shapeAt (K1.parL Zp Bs.G₀ l d) n).answers ≠ 0 ∧
        y = seatAtMember cF.blocksInOrder (K1.noL l d) (K1.parL Zp Bs.G₀ l d) n := by
  intro y
  have eT := (nums_fifty h O hl d).2
  have eS : (P5J.At.N Zp cF).sent = N0Full.sent :=
    congrArg (·.sent) (K1.atAll_letters h O (K1.pin1_atAll h)).1
  unfold seatAtMember
  rw [eT, parL_written h O l d]
  have e0 : pinsAtSort (P5J.At.N Zp cF) (cond d (.digits l) (.reads l)) =
      (P5J.At.N Zp cF).sent l (momL d) := by cases d <;> rfl
  rw [e0, eS, mem_of_same (fifty_of seatsW50 l hl d) y, List.mem_map]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, (mem_sampledNos.1 hn).1, (mem_sampledNos.1 hn).2, rfl⟩
  · rintro ⟨n, h1, h2, rfl⟩
    exact ⟨n, mem_sampledNos.2 ⟨h1, h2⟩, rfl⟩

/-- **numbered**, in the record's own text, with the table's count of messages in front of the place
where the record has the job's first number. -/
theorem numbered_fifty (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {l : ℕ} (hl : l < 25) (d : Bool) :
    ∀ n, n < (K1.parL Zp Bs.G₀ l d).sent.size → (shapeAt (K1.parL Zp Bs.G₀ l d) n).answers ≠ 0 →
      seatAtMember cF.blocksInOrder (K1.noL l d) (K1.parL Zp Bs.G₀ l d) n ∈ P5J.At.seats Zp ∧
        (P5J.At.seats Zp).idxOf (seatAtMember cF.blocksInOrder (K1.noL l d) (K1.parL Zp Bs.G₀ l d) n) =
          (P5J.At.N Zp cF).msgsAt (some (K1.parL Zp Bs.G₀ l d).place) + n := by
  obtain ⟨eM, eT⟩ := nums_fifty h O hl d
  have ep : (K1.parL Zp Bs.G₀ l d).place = k1PlaceL l d := by cases d <;> rfl
  unfold seatAtMember
  rw [eT, ep, eM, parL_written h O l d, (K1.atAll_letters h O (K1.pin1_atAll h)).2.1]
  intro n h1 h2
  have hw := List.all_eq_true.1 (fifty_of numberedW50 l hl d) n (mem_sampledNos.2 ⟨h1, h2⟩)
  rw [Bool.and_eq_true, decide_eq_true_eq] at hw
  exact ⟨List.contains_iff_mem.1 hw.1, hw.2⟩

/-- **sits**, in the record's own text. -/
theorem sits_fifty (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {l : ℕ} (hl : l < 25) (d : Bool) :
    ∀ n, n < (K1.parL Zp Bs.G₀ l d).sent.size → (shapeAt (K1.parL Zp Bs.G₀ l d) n).answers ≠ 0 →
      (∃ m ∈ P5J.At.ms Zp Z.lay,
          SitsAt m (seatAtMember cF.blocksInOrder (K1.noL l d) (K1.parL Zp Bs.G₀ l d) n).1
            (seatAtMember cF.blocksInOrder (K1.noL l d) (K1.parL Zp Bs.G₀ l d) n).2) ∧
      ∀ m ∈ P5J.At.ms Zp Z.lay,
          SitsAt m (seatAtMember cF.blocksInOrder (K1.noL l d) (K1.parL Zp Bs.G₀ l d) n).1
            (seatAtMember cF.blocksInOrder (K1.noL l d) (K1.parL Zp Bs.G₀ l d) n).2 →
          (m.1.l.get m.2).1 = shapeAt (K1.parL Zp Bs.G₀ l d) n := by
  have eT := (nums_fifty h O hl d).2
  have eP := (P5T.seats_in_scope h.scope h.laid.pub (K1.pin1_atAll h) (K1.laidP_atAll h)).1
  have hM : ∀ y : OnBytes.OracleShape × (Nat × Nat),
      y ∈ (P5J.At.ms Zp Z.lay).map (fun m => ((m.1.l.get m.2).1, seatOf m)) ↔
        y ∈ (psFull.filter (·.smpd)).map fun p => (p.shape, p.seat) := by
    intro y
    have e := P5T.memsSame_atR Zp (P5J.At.rad Zp Z.lay) y
    rw [eP] at e
    exact e
  unfold seatAtMember
  rw [eT, parL_written h O l d]
  intro n h1 h2
  have hw := List.all_eq_true.1 (fifty_of sitsW50 l hl d) n (mem_sampledNos.2 ⟨h1, h2⟩)
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
    have hs' : seatOf m = seatOfMsg (placeL l d) (baseL3 l d) n := hs
    rw [← e1]
    exact of_decide_eq_true (hall q hq) (e2.trans hs')

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.countsW50
#print axioms ProofFile.Honest.K1.seatsW50
#print axioms ProofFile.Honest.K1.numberedW50
#print axioms ProofFile.Honest.K1.sitsW50
#print axioms ProofFile.Honest.K1.numberedW50_bites
#print axioms ProofFile.Honest.K1.seatsW50_bites
#print axioms ProofFile.Honest.K1.sitsW50_bites
#print axioms ProofFile.Honest.K1.nums_fifty
#print axioms ProofFile.Honest.K1.seats_fifty
#print axioms ProofFile.Honest.K1.numbered_fifty
#print axioms ProofFile.Honest.K1.sits_fifty
