-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/BookAtPlace.lean: the kind "the code switch" (K2): the field book of FreshAsks
(Honest/K2/Fresh.lean), in its own text, at each of the 25 places of the kind, at the book that
bookWhole returns at the head's description and at that description's order of places. Eleven places
are AtFullSide/K2/BookAtSwitches.lean's; the other fourteen are here.

  restLinksW         by Lean's kernel: the written places whose links are not 2, 4, ..., 22 have
                     these fourteen links
  ownerRestBentW     by Lean's kernel, a control: at the finish one entry beyond the part's coins
                     makes the test say no
  ownerRest_written  the owner's entries and the test at each of the fourteen (OwnerRest/R*.lean)
  book_at_place      the field, at every place of the kind

Limits. The head, the opening and the book's return are hypotheses here. It reads the book's numbers:
that a part lays, spends or carries what these say is not said. The merges are mergesByName's. The
closed facts are Lean's kernel's.
-/
import AtFullSide.K2.OwnerRest.R01
import AtFullSide.K2.OwnerRest.R03
import AtFullSide.K2.OwnerRest.R05
import AtFullSide.K2.OwnerRest.R07
import AtFullSide.K2.OwnerRest.R09
import AtFullSide.K2.OwnerRest.R11
import AtFullSide.K2.OwnerRest.R13
import AtFullSide.K2.OwnerRest.R15
import AtFullSide.K2.OwnerRest.R17
import AtFullSide.K2.OwnerRest.R19
import AtFullSide.K2.OwnerRest.R21
import AtFullSide.K2.OwnerRest.R23
import AtFullSide.K2.OwnerRest.R24
import AtFullSide.K2.OwnerRest.R25
import AtFullSide.K2.BookAtSwitches

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open VerifiableInference.Desc (Chain Block)
open Johnson.G (proofSendsFull)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law (placesW places_at_head)
open AtFullSide.K14

set_option maxRecDepth 1000000 in
/-- The written places outside the eleven have these fourteen links. -/
theorem restLinksW : (placesW.filter fun p => !evenLink p).map (·.link) =
    [1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 24, 25] := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A control: at the finish one entry beyond the part's coins makes the test say no. -/
theorem ownerRestBentW : ((placesW.filter fun p => p.link == 25).all fun p =>
    restTest p ((⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨1000000, 1000000⟩, true) ::
      joinPieces restA25 restS25 restO25)) = false := by
  decide +kernel

/-- **The book's entries and the test at each of the fourteen.** -/
theorem ownerRest_written {p : SwitchPlace} (hpW : p ∈ placesW) (he : evenLink p = false) :
    ∃ L, ownerEntries p = L ∧ restTest p L = true := by
  have hm : p.link ∈ (placesW.filter fun p => !evenLink p).map (·.link) :=
    List.mem_map_of_mem (List.mem_filter.2 ⟨hpW, by rw [he]; rfl⟩)
  rw [restLinksW] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e | e | e | e | e | e | e | e | e
  · have m : p ∈ placesW.filter fun p => p.link == 1 :=
      List.mem_filter.2 ⟨hpW, beq_iff_eq.2 e⟩
    exact ⟨_, ownerEntries_join (of_decide_eq_true (List.all_eq_true.1 wantsW01 p m))
      (of_decide_eq_true (List.all_eq_true.1 segW01 p m))
      (of_decide_eq_true (List.all_eq_true.1 smallW01 p m)),
      List.all_eq_true.1 ownerRestW01 p m⟩
  · have m : p ∈ placesW.filter fun p => p.link == 3 :=
      List.mem_filter.2 ⟨hpW, beq_iff_eq.2 e⟩
    exact ⟨_, ownerEntries_join (of_decide_eq_true (List.all_eq_true.1 wantsW03 p m))
      (of_decide_eq_true (List.all_eq_true.1 segW03 p m))
      (of_decide_eq_true (List.all_eq_true.1 smallW03 p m)),
      List.all_eq_true.1 ownerRestW03 p m⟩
  · have m : p ∈ placesW.filter fun p => p.link == 5 :=
      List.mem_filter.2 ⟨hpW, beq_iff_eq.2 e⟩
    exact ⟨_, ownerEntries_join (of_decide_eq_true (List.all_eq_true.1 wantsW05 p m))
      (of_decide_eq_true (List.all_eq_true.1 segW05 p m))
      (of_decide_eq_true (List.all_eq_true.1 smallW05 p m)),
      List.all_eq_true.1 ownerRestW05 p m⟩
  · have m : p ∈ placesW.filter fun p => p.link == 7 :=
      List.mem_filter.2 ⟨hpW, beq_iff_eq.2 e⟩
    exact ⟨_, ownerEntries_join (of_decide_eq_true (List.all_eq_true.1 wantsW07 p m))
      (of_decide_eq_true (List.all_eq_true.1 segW07 p m))
      (of_decide_eq_true (List.all_eq_true.1 smallW07 p m)),
      List.all_eq_true.1 ownerRestW07 p m⟩
  · have m : p ∈ placesW.filter fun p => p.link == 9 :=
      List.mem_filter.2 ⟨hpW, beq_iff_eq.2 e⟩
    exact ⟨_, ownerEntries_join (of_decide_eq_true (List.all_eq_true.1 wantsW09 p m))
      (of_decide_eq_true (List.all_eq_true.1 segW09 p m))
      (of_decide_eq_true (List.all_eq_true.1 smallW09 p m)),
      List.all_eq_true.1 ownerRestW09 p m⟩
  · have m : p ∈ placesW.filter fun p => p.link == 11 :=
      List.mem_filter.2 ⟨hpW, beq_iff_eq.2 e⟩
    exact ⟨_, ownerEntries_join (of_decide_eq_true (List.all_eq_true.1 wantsW11 p m))
      (of_decide_eq_true (List.all_eq_true.1 segW11 p m))
      (of_decide_eq_true (List.all_eq_true.1 smallW11 p m)),
      List.all_eq_true.1 ownerRestW11 p m⟩
  · have m : p ∈ placesW.filter fun p => p.link == 13 :=
      List.mem_filter.2 ⟨hpW, beq_iff_eq.2 e⟩
    exact ⟨_, ownerEntries_join (of_decide_eq_true (List.all_eq_true.1 wantsW13 p m))
      (of_decide_eq_true (List.all_eq_true.1 segW13 p m))
      (of_decide_eq_true (List.all_eq_true.1 smallW13 p m)),
      List.all_eq_true.1 ownerRestW13 p m⟩
  · have m : p ∈ placesW.filter fun p => p.link == 15 :=
      List.mem_filter.2 ⟨hpW, beq_iff_eq.2 e⟩
    exact ⟨_, ownerEntries_join (of_decide_eq_true (List.all_eq_true.1 wantsW15 p m))
      (of_decide_eq_true (List.all_eq_true.1 segW15 p m))
      (of_decide_eq_true (List.all_eq_true.1 smallW15 p m)),
      List.all_eq_true.1 ownerRestW15 p m⟩
  · have m : p ∈ placesW.filter fun p => p.link == 17 :=
      List.mem_filter.2 ⟨hpW, beq_iff_eq.2 e⟩
    exact ⟨_, ownerEntries_join (of_decide_eq_true (List.all_eq_true.1 wantsW17 p m))
      (of_decide_eq_true (List.all_eq_true.1 segW17 p m))
      (of_decide_eq_true (List.all_eq_true.1 smallW17 p m)),
      List.all_eq_true.1 ownerRestW17 p m⟩
  · have m : p ∈ placesW.filter fun p => p.link == 19 :=
      List.mem_filter.2 ⟨hpW, beq_iff_eq.2 e⟩
    exact ⟨_, ownerEntries_join (of_decide_eq_true (List.all_eq_true.1 wantsW19 p m))
      (of_decide_eq_true (List.all_eq_true.1 segW19 p m))
      (of_decide_eq_true (List.all_eq_true.1 smallW19 p m)),
      List.all_eq_true.1 ownerRestW19 p m⟩
  · have m : p ∈ placesW.filter fun p => p.link == 21 :=
      List.mem_filter.2 ⟨hpW, beq_iff_eq.2 e⟩
    exact ⟨_, ownerEntries_join (of_decide_eq_true (List.all_eq_true.1 wantsW21 p m))
      (of_decide_eq_true (List.all_eq_true.1 segW21 p m))
      (of_decide_eq_true (List.all_eq_true.1 smallW21 p m)),
      List.all_eq_true.1 ownerRestW21 p m⟩
  · have m : p ∈ placesW.filter fun p => p.link == 23 :=
      List.mem_filter.2 ⟨hpW, beq_iff_eq.2 e⟩
    exact ⟨_, ownerEntries_join (of_decide_eq_true (List.all_eq_true.1 wantsW23 p m))
      (of_decide_eq_true (List.all_eq_true.1 segW23 p m))
      (of_decide_eq_true (List.all_eq_true.1 smallW23 p m)),
      List.all_eq_true.1 ownerRestW23 p m⟩
  · have m : p ∈ placesW.filter fun p => p.link == 24 :=
      List.mem_filter.2 ⟨hpW, beq_iff_eq.2 e⟩
    exact ⟨_, ownerEntries_join (of_decide_eq_true (List.all_eq_true.1 wantsW24 p m))
      (of_decide_eq_true (List.all_eq_true.1 segW24 p m))
      (of_decide_eq_true (List.all_eq_true.1 smallW24 p m)),
      List.all_eq_true.1 ownerRestW24 p m⟩
  · have m : p ∈ placesW.filter fun p => p.link == 25 :=
      List.mem_filter.2 ⟨hpW, beq_iff_eq.2 e⟩
    exact ⟨_, ownerEntries_join (of_decide_eq_true (List.all_eq_true.1 wantsW25 p m))
      (of_decide_eq_true (List.all_eq_true.1 segW25 p m))
      (of_decide_eq_true (List.all_eq_true.1 smallW25 p m)),
      List.all_eq_true.1 ownerRestW25 p m⟩

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {B : ProverCoinCounts} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)} {p : SwitchPlace}

/-- **The field book, in its own text, at every place of the kind.** -/
theorem book_at_place (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    (hp : p ∈ switchPlaces Zp Bs.G₀) :
    ∀ q : Addr, bookFits p.sizes.codes (switchSent p.sizes p.others)
      (K2.switchFresh p.sizes p.others p.foldVars) (B.spentBy ⟨p.place, 0⟩ q)
      (B.knownBy (orderOf (F0T OnBytes.secondHashFunction Zp Np cF)) ⟨p.place, 0⟩ q) = true := by
  cases he : evenLink p with
  | true => exact book_at_switch h O hB hp he
  | false =>
    have hpW : p ∈ placesW := by
      rw [← places_at_head h.toAtMg O]
      exact hp
    obtain ⟨L, hL, t⟩ := ownerRest_written hpW he
    unfold restTest at t
    rw [Bool.and_eq_true] at t
    exact book_at_owner h hB hL t.1 t.2

end AtFullSide.K2

#print axioms AtFullSide.K2.restLinksW
#print axioms AtFullSide.K2.ownerRestBentW
#print axioms AtFullSide.K2.ownerRest_written
#print axioms AtFullSide.K2.book_at_place
