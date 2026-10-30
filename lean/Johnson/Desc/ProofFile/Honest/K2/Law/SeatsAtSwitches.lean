-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SeatsAtSwitches.lean: the kind "the code switch" (K2): THREE
PUBLIC FIELDS OF THE RECORD `K2SeatedL` (Honest/K2/SeatedL.lean), seats, numbered AND sits, IN THE
RECORD's OWN TEXT, AT THE REAL TABLE's NUMBERS, UNDER THE LIBRARY's HEAD AND THE OPENING, AT EACH
SWITCH OF THE PLAN: at the member's number where the written list of places first bears the place,
at seg := the place's link, first := the table's own count of messages in front of the place. After
the shared sending's K1/Law/SeatsAtFifty.lean, of other authors, statement by statement. One
definition, public numbers; seven closed facts by evaluation in Lean's kernel, three of them
negative tests; lemmas.

  `countsAtSwitch`  the written counts there: messages in front; trees in front
  `countsWS`        BY LEAN's KERNEL: the number is at most 358, the written list of counts has an
                    entry there, and the trees in front are 3 l + 1 at link l
  `seatsWS`, `numberedWS`, `sitsWS`   BY LEAN's KERNEL, at the 25 written places: the three tests
  `numberedWS_bites`, `seatsWS_bites`, `sitsWS_bites`   NEGATIVE TESTS, AT EACH PLACE: one tree
                    further · at the moment 1 · with one answer more in the shape
  `nums_switch`     under the head: the table's two counts in front of the place are the written
                    ones
  `seats_switch`, `numbered_switch`, `sits_switch`   THE ENDS

By, of other authors, sealed: `nums_of` (Johnson/Desc/K1/Law/TiesAtAll.lean) · `atAll_letters`,
`atAll_counts`, `pin1_atAll`, `pin2_atAll`, `laidP_atAll` (Johnson/Desc/K1/Law/) ·
`blockPlaces_full` · `seats_in_scope`, `memsSame_atR` · `treesNo_atN`
(Honest/K1/Law/TreesNoTold.lean) · `sampledNos`, `mem_sampledNos`, `mem_of_same`
(Honest/K1/Law/SeatsAtTwo.lean). Ours: `switchNo` (Honest/K2/Law/SwitchNo.lean): the number where
the written list of places first bears the switch's place · `k2_placeAt_at_head`
(Honest/K2/Law/RecordAtHead.lean) · `places_at_head` (Honest/K2/Law/PlacesWritten.lean).

Limits. PUBLIC NUMBERS, SEATS AND SHAPES ALONE: no coin, input or run occurs. The full size and the
format's second hash function alone. The head and the opening are premises; that they can be met is not
said. It rests on closed facts by evaluation in Lean's kernel at written lists. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.RecordAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchNo
import Johnson.Desc.ProofFile.Honest.K1.Law.SeatsAtFifty

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S Numbers sameMembers)
open VerifiableInference.Desc.Sound (Mem SitsAt)
open VerifiableInference.Desc.K1 (psF seatOfMsg)
open VerifiableInference.Desc.K13.Law (seatsFull countsFull)
open P5T (N0Full psFull)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)
open Johnson.Prover.Send (shapeAt)
open ProofFile.Honest.K1 (seatAtMember sampledNos mem_sampledNos mem_of_same)

/-! ## 1 At the written constants -/

/-- The written counts there: the messages in front; the trees in front. -/
def countsAtSwitch (p : SwitchPlace) : Nat × Nat := (countsFull[switchNo p]?).getD (0, 0)

set_option maxRecDepth 1000000 in
/-- The number is at most 358, the written list of counts has an entry there, and the trees in front
are 3 l + 1 at link l. -/
theorem countsWS : (placesW.all fun p => decide (switchNo p ≤ 358) &&
    (countsFull[switchNo p]? == some (countsAtSwitch p)) &&
    ((countsAtSwitch p).2 == 3 * p.link + 1)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The seats that the written numbers give the place's link at the moment 0 are just the sending's
sampled messages' seats, behind the written count of trees. -/
theorem seatsWS : (placesW.all fun p => sameMembers (N0Full.sent p.link 0)
    ((sampledNos (switchPar p)).map (seatOfMsg (switchPar p) (countsAtSwitch p).2))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Each of these seats stands in the written list of seats, first at the written count of messages
in front and the message's own number. -/
theorem numberedWS : (placesW.all fun p => (sampledNos (switchPar p)).all fun n =>
    seatsFull.contains (seatOfMsg (switchPar p) (countsAtSwitch p).2 n) &&
      decide (seatsFull.idxOf (seatOfMsg (switchPar p) (countsAtSwitch p).2 n) =
        (countsAtSwitch p).1 + n)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- At each of these seats a sampled seat of the written plan's list stands, and each that stands
there has the message's shape. -/
theorem sitsWS : (placesW.all fun p => (sampledNos (switchPar p)).all fun n =>
    ((psFull.filter (·.smpd)).any fun y =>
        decide (y.seat = seatOfMsg (switchPar p) (countsAtSwitch p).2 n)) &&
      (psFull.filter (·.smpd)).all fun y =>
        decide (y.seat = seatOfMsg (switchPar p) (countsAtSwitch p).2 n →
          y.shape = shapeAt (switchPar p) n)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: AT EACH PLACE, one tree further, the test on the numbers says no. -/
theorem numberedWS_bites : (placesW.all fun p => !((sampledNos (switchPar p)).all fun n =>
    seatsFull.contains (seatOfMsg (switchPar p) ((countsAtSwitch p).2 + 1) n) &&
      decide (seatsFull.idxOf (seatOfMsg (switchPar p) ((countsAtSwitch p).2 + 1) n) =
        (countsAtSwitch p).1 + n))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: AT EACH PLACE, at the moment 1, the test on the seats says no. -/
theorem seatsWS_bites : (placesW.all fun p => !(sameMembers (N0Full.sent p.link 1)
    ((sampledNos (switchPar p)).map (seatOfMsg (switchPar p) (countsAtSwitch p).2)))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test on the shapes' half: AT EACH PLACE, at the true seats, with one answer more in
the message's shape, the test on the members says no. -/
theorem sitsWS_bites : (placesW.all fun p => !((sampledNos (switchPar p)).all fun n =>
    (psFull.filter (·.smpd)).all fun y =>
      decide (y.seat = seatOfMsg (switchPar p) (countsAtSwitch p).2 n →
        y.shape = { shapeAt (switchPar p) n with
          answers := (shapeAt (switchPar p) n).answers + 1 }))) = true := by
  decide +kernel

/-! ## 2 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)} {p : SwitchPlace}

/-- The two counts in front of a switch of the plan. -/
theorem nums_switch (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) (hp : p ∈ switchPlaces Zp Bs.G₀) :
    (P5J.At.N Zp cF).msgsAt (some p.place) = (countsAtSwitch p).1 ∧
      treesTo cF.blocksInOrder (switchNo p) = (countsAtSwitch p).2 := by
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  have t := List.all_eq_true.1 countsWS p hpW
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at t
  have e := K1.nums_of (K1.atAll_letters h O (K1.pin1_atAll h)).1
    (LPFK9.blockPlaces_full h.scope h.reads O) (K1.atAll_counts (K1.pin2_atAll h)) t.1.1
    (eq_of_beq t.1.2)
  have hq : psF[switchNo p]? = some p.place := k2_placeAt_at_head h O hp
  rw [hq] at e
  exact ⟨e.1, (K1.treesNo_atN Zp cF (k2_placeAt_at_head h O hp)).trans e.2⟩

/-- **seats**, in the record's own text. -/
theorem seats_switch (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) (hp : p ∈ switchPlaces Zp Bs.G₀) :
    ∀ y, y ∈ (P5J.At.N Zp cF).sent p.link 0 ↔
      ∃ n, n < (switchPar p).sent.size ∧ (shapeAt (switchPar p) n).answers ≠ 0 ∧
        y = seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n := by
  intro y
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  have eT := (nums_switch h O hp).2
  have eS : (P5J.At.N Zp cF).sent = N0Full.sent :=
    congrArg (·.sent) (K1.atAll_letters h O (K1.pin1_atAll h)).1
  unfold seatAtMember
  rw [eT, eS, mem_of_same (List.all_eq_true.1 seatsWS p hpW) y, List.mem_map]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, (mem_sampledNos.1 hn).1, (mem_sampledNos.1 hn).2, rfl⟩
  · rintro ⟨n, h1, h2, rfl⟩
    exact ⟨n, mem_sampledNos.2 ⟨h1, h2⟩, rfl⟩

/-- **numbered**, in the record's own text, with the table's count of messages in front of the place
where the record has the letter first. -/
theorem numbered_switch (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) (hp : p ∈ switchPlaces Zp Bs.G₀) :
    ∀ n, n < (switchPar p).sent.size → (shapeAt (switchPar p) n).answers ≠ 0 →
      seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n ∈ P5J.At.seats Zp ∧
        (P5J.At.seats Zp).idxOf (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n) =
          (P5J.At.N Zp cF).msgsAt (some p.place) + n := by
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  obtain ⟨eM, eT⟩ := nums_switch h O hp
  unfold seatAtMember
  rw [eT, eM, (K1.atAll_letters h O (K1.pin1_atAll h)).2.1]
  intro n h1 h2
  have hw := List.all_eq_true.1 (List.all_eq_true.1 numberedWS p hpW) n
    (mem_sampledNos.2 ⟨h1, h2⟩)
  rw [Bool.and_eq_true, decide_eq_true_eq] at hw
  exact ⟨List.contains_iff_mem.1 hw.1, hw.2⟩

/-- **sits**, in the record's own text. -/
theorem sits_switch (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) (hp : p ∈ switchPlaces Zp Bs.G₀) :
    ∀ n, n < (switchPar p).sent.size → (shapeAt (switchPar p) n).answers ≠ 0 →
      (∃ m ∈ P5J.At.ms Zp Z.lay,
          SitsAt m (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n).1
            (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n).2) ∧
      ∀ m ∈ P5J.At.ms Zp Z.lay,
          SitsAt m (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n).1
            (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n).2 →
          (m.1.l.get m.2).1 = shapeAt (switchPar p) n := by
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  have eT := (nums_switch h O hp).2
  have eP := (P5T.seats_in_scope h.scope h.laid.pub (K1.pin1_atAll h) (K1.laidP_atAll h)).1
  have hM : ∀ y : OnBytes.OracleShape × (Nat × Nat),
      y ∈ (P5J.At.ms Zp Z.lay).map (fun m => ((m.1.l.get m.2).1, Sound.seatOf m)) ↔
        y ∈ (psFull.filter (·.smpd)).map fun u => (u.shape, u.seat) := by
    intro y
    have e := P5T.memsSame_atR Zp (P5J.At.rad Zp Z.lay) y
    rw [eP] at e
    exact e
  unfold seatAtMember
  rw [eT]
  intro n h1 h2
  have hw := List.all_eq_true.1 (List.all_eq_true.1 sitsWS p hpW) n (mem_sampledNos.2 ⟨h1, h2⟩)
  rw [Bool.and_eq_true, List.any_eq_true, List.all_eq_true] at hw
  obtain ⟨⟨u, hu, hus⟩, hall⟩ := hw
  constructor
  · obtain ⟨m, hm, e⟩ := List.mem_map.1
      ((hM (u.shape, u.seat)).2 (List.mem_map.2 ⟨u, hu, rfl⟩))
    refine ⟨m, hm, ?_⟩
    have e2 : Sound.seatOf m = u.seat := congrArg Prod.snd e
    show m.1.seat m.2 = _
    exact e2.trans (of_decide_eq_true hus)
  · intro m hm hs
    obtain ⟨v, hv, e⟩ := List.mem_map.1
      ((hM ((m.1.l.get m.2).1, Sound.seatOf m)).1 (List.mem_map.2 ⟨m, hm, rfl⟩))
    have e1 : v.shape = (m.1.l.get m.2).1 := congrArg Prod.fst e
    have e2 : v.seat = Sound.seatOf m := congrArg Prod.snd e
    have hs' : Sound.seatOf m = seatOfMsg (switchPar p) (countsAtSwitch p).2 n := hs
    rw [← e1]
    exact of_decide_eq_true (hall v hv) (e2.trans hs')

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.countsAtSwitch
#print axioms ProofFile.Honest.K2.Law.countsWS
#print axioms ProofFile.Honest.K2.Law.seatsWS
#print axioms ProofFile.Honest.K2.Law.numberedWS
#print axioms ProofFile.Honest.K2.Law.sitsWS
#print axioms ProofFile.Honest.K2.Law.numberedWS_bites
#print axioms ProofFile.Honest.K2.Law.seatsWS_bites
#print axioms ProofFile.Honest.K2.Law.sitsWS_bites
#print axioms ProofFile.Honest.K2.Law.nums_switch
#print axioms ProofFile.Honest.K2.Law.seats_switch
#print axioms ProofFile.Honest.K2.Law.numbered_switch
#print axioms ProofFile.Honest.K2.Law.sits_switch
