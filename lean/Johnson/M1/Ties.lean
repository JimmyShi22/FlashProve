-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- the written sendings are the description's own, at K1's 52.
/-
Johnson/M1/Ties.lean: the written list of sendings (Johnson/M1/Numbers.lean) held against what the
description's own lots announce: in the goals' scope, where the gate accepts, at every opening of
the maker's value, the public numbers of K1's 52 jobs are the list's, message for message, under the
written codes, and their first trees have the list's numbers. No property of the protocol is claimed
here.
-/
import Johnson.M1.AtDescriptionProved
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Desc.ProofFile.Honest.K2.Exact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.Seat (parsW lotPars treesAt)
open OnBytes.M1 (codesW sendsW treesBefore)
open VerifiableInference.PlanWritten (cutFirstFull cutOf)
open ProofFile.Honest.K2 (SwitchPlace switchSent switchPlaces)
open ProofFile.Honest.K2.Law (placesW)

/-- The numbers of K1's 52 sendings, in the order of the jobs: the first; each segment's two; W. -/
def lotIdx : List Nat := 0 :: ((List.range 25).flatMap fun l => [3 * l + 1, 3 * l + 2]) ++ [81]

set_option maxRecDepth 1000000 in
theorem lotIdx_52 : lotIdx.length = 52 ∧ parsW.length = 52 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The jobs' messages are the list's. -/
theorem pars_sent : ((lotIdx.zip parsW).all fun x => x.2.sent == OnBytes.M1.sentAt x.1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The jobs' codes are the written ones. -/
theorem pars_codes : (parsW.all fun P => decide (P.codes = codesW)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- In front of each job's place the cut has as many trees as the list in front of its number. -/
theorem pars_trees :
    ((lotIdx.zip parsW).all fun x => treesAt cutFirstFull x.2.place == treesBefore x.1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Every message of every sending lies in a tree. -/
theorem laid_all : ((List.range 82).all fun i =>
    (List.range (OnBytes.M1.sentAt i).size).all fun k =>
      (((Own.treesMade codesW (OnBytes.M1.sentAt i)).getD {}).tree[k]?).isSome) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The code switch's places have the written codes. -/
theorem places_codes : (placesW.zipIdx.all fun x => decide (x.1.sizes.codes = codesW)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The written list of the maker's sendings is the list of Johnson/M1/Numbers.lean. -/
theorem sends_written :
    (Johnson.G.proofSendsFull.1.sends.map fun x => x.sent.toArray) = sendsW := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- W's ride at the written shape: the message, the fold's row variables, those of its mask rows. -/
theorem w_ride : ((ProofFile.Honest.K1.wFold VerifiableInference.PlanWritten.proofSizedFull.batch.shape).map
    fun x => (x.1, x.2.layout.k, x.2.layout.h)) = some (1, 5, 1) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The code switches' sendings are among the 82. -/
theorem places_lt : (placesW.zipIdx.all fun x => decide (3 * (x.2 + 1) < 82)) = true := by
  decide +kernel

/-- A member of a list has a number. -/
theorem exists_zipIdx {α : Type} (l : List α) (n : Nat) (x : α) (h : x ∈ l) :
    ∃ k, (x, k) ∈ l.zipIdx n := by
  induction l generalizing n with
  | nil => cases h
  | cons a t ih =>
    rcases List.mem_cons.1 h with rfl | h'
    · exact ⟨n, List.mem_cons_self ..⟩
    · obtain ⟨k, hk⟩ := ih (n + 1) h'
      exact ⟨k, List.mem_cons_of_mem _ hk⟩

/-- A list without its doubles has no doubles. -/
theorem eraseDups_nodup (l : List Nat) : l.eraseDups.Nodup := by
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    cases l with
    | nil => simp
    | cons a t =>
      rw [List.eraseDups_cons]
      refine List.nodup_cons.2 ⟨fun hm => ?_, ih _ ?_ _ rfl⟩
      · have := List.mem_eraseDups.1 hm
        simp at this
      · have := List.length_filter_le (fun b => !b == a) t
        simp only [List.length_cons] at hn
        omega

/-- The list without its doubles is as long as the list has distinct members. -/
theorem eraseDups_length_le (l : List Nat) : l.eraseDups.length ≤ l.toFinset.card := by
  have h : l.toFinset = l.eraseDups.toFinset := by
    ext a
    rw [List.mem_toFinset, List.mem_toFinset, List.mem_eraseDups]
  rw [h, List.toFinset_card_of_nodup (eraseDups_nodup l)]

/-- The sending's public letter announces the sending. -/
theorem sendingPar_sent (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) :
    (ProofFile.Honest.K2.sendingPar codes sent).sent = sent := by
  simp [K1.Par.sent, ProofFile.Honest.K2.sendingPar]

section
variable {P : VerifierAndGoals.PublicFiles} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block First.S ProofFile.Cl)} {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- In scope, where the gate accepts, at an opening: the maker's pin. -/
theorem pins_of_live (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) :
    VerifiableInference.PlanWritten.madeRow Z = true ∧ cutOf F.first.blocksInOrder = cutFirstFull := by
  obtain ⟨_, h4⟩ := OnBytes.SendSim.Seat.plan_of_live hL O
  have hk := VerifiableInference.PlanWritten.key_in_scope_pure hS O.pub
  obtain ⟨hm, hc⟩ := LPFD.asks_pins h4 O.pub (decide_eq_true hk)
  exact ⟨hm, (VerifiableInference.PlanWritten.cutIs_eq hc).1⟩

/-- **The first chain's rows are the written cut.** -/
theorem cut_of_live (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) :
    cutOf F.first.blocksInOrder = cutFirstFull := (pins_of_live hS hL O).2

/-- **K1's jobs' numbers are the written ones.** -/
theorem pars_of_live (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) :
    (lotPars Z Bs.G₀).map (·.1) = parsW := by
  have hy := VerifiableInference.PlanWritten.pinnedAt_of_row (Z := Z)
    (by rw [(pins_of_live hS hL O).1, Bool.or_true])
  have hLZ := VerifiableInference.Desc.K13.Law.likeFull_in_scope hS O.pub hy
  have hg := VerifiableInference.Desc.K13.Law.gpOf_in_scope hS O.pub hy
  have hLG : K1.LikeFull Bs.G₀.first := by rw [O.first]; exact hLZ
  obtain ⟨pp, hR⟩ := H2K.Sizes.inScope_readFiles hS
  have hv := Johnson.AtFull.Desc.K1Lot.view_in_scope hS hR O.pub O.blank
  exact OnBytes.SendSim.Seat.lotPars_written hLG hLZ hg hv

/-- A member of the first chain has as many lists of oracle messages as rounds. -/
theorem shaped_of_live (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) :
    ∀ b ∈ F.first.blocksInOrder, b.oracles.length = b.rounds.length := fun b hb => by
  have PO := (F.planOk_ok).1 (OnBytes.SendSim.Seat.plan_of_live hL O).1
  have h := (PO.blocks₁ b hb).2
  unfold Block.shaped at h
  rw [Bool.and_eq_true] at h
  exact beq_iff_eq.1 h.1

/-- **The trees in front of a place of the description are the cut's.** -/
theorem trees_of_live (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) (a : Place) :
    OnBytes.SendSim.Seat.treesOf F.first.blocksInOrder (F.first.blocksInOrder.takeWhile (·.place != a)) =
      treesAt cutFirstFull a := by
  rw [OnBytes.SendSim.Seat.treesOf_cut _ (shaped_of_live hL O), cut_of_live hS hL O]

/-- **K1's 52, at the description**: each job announces the list's messages, under the written
codes, and its first tree in the description has the list's number. -/
theorem lots_tied (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) :
    ∀ x ∈ lotIdx.zip ((lotPars Z Bs.G₀).map (·.1)),
      x.2.sent = OnBytes.M1.sentAt x.1 ∧ x.2.codes = codesW ∧
      OnBytes.SendSim.Seat.treesOf F.first.blocksInOrder (F.first.blocksInOrder.takeWhile (·.place != x.2.place)) =
        treesBefore x.1 := by
  rw [pars_of_live hS hL O]
  intro x hx
  have h1 := List.all_eq_true.1 pars_sent x hx
  have h3 := List.all_eq_true.1 pars_trees x hx
  have h2 := List.all_eq_true.1 pars_codes x.2 (List.of_mem_zip hx).2
  exact ⟨beq_iff_eq.1 h1, of_decide_eq_true h2, (trees_of_live hS hL O _).trans (beq_iff_eq.1 h3)⟩

/-- **The code switch's places of the description are the written ones.** -/
theorem places_of_live (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) :
    switchPlaces Z Bs.G₀ = placesW := by
  have hm := (pins_of_live hS hL O).1
  have hy := VerifiableInference.PlanWritten.pinnedAt_of_row (Z := Z) (by rw [hm, Bool.or_true])
  have h1 := H2K5.Row.plans_front hS O.pub hy
  rw [ProofFile.Honest.K2.Law.switchPlaces_is, IM.prep_pinned O.pub hm O.blank,
    H2K5.Row.cuts_of_plans (show ProofFile.pubBy (ProofFile.PlainG.madeOf OnBytes.secondHashFunction) ProofFile.plainStarts
      P.pol P.lay P.KL = .ok Z from O.pub) h1, Johnson.AtFull.Desc.spots_written]
  rfl

/-- **All 82 sendings are the maker's own, at every opening**: the list of sendings in the public
part that the maker returns is the written one, message for message, K12's included. -/
theorem sends_of_live (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) :
    (Z.made.proof.1.sends.map fun x => x.sent.toArray) = sendsW := by
  rw [(IM.pins (pins_of_live hS hL O).1).2.2.2.2]
  exact sends_written

/-- **The codes of the sendings are the verifier's state's.** -/
theorem codes_of_live (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) :
    Z.s₀.st.codes = codesW := by
  have hco := (IM.pins (pins_of_live hS hL O).1).2.2.2.1
  have hs := Meaning.K2.pub_start O.pub
  unfold First.S.startP at hs
  split at hs
  · have e := Option.some.inj hs
    rw [← e]
    exact hco
  · cases hs

/-- **K2's 25, at the description.** -/
theorem places_tied (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) :
    ∀ x ∈ (switchPlaces Z Bs.G₀).zipIdx,
      switchSent x.1.sizes x.1.others = OnBytes.M1.sentAt (3 * (x.2 + 1)) ∧ x.1.sizes.codes = codesW ∧
      OnBytes.SendSim.Seat.treesOf F.first.blocksInOrder (F.first.blocksInOrder.takeWhile (·.place != x.1.place)) =
        treesBefore (3 * (x.2 + 1)) := by
  rw [places_of_live hS hL O]
  intro x hx
  have h1 := List.all_eq_true.1 sent_ties x hx
  have h3 := List.all_eq_true.1 tree_ties x hx
  have h2 := List.all_eq_true.1 places_codes x hx
  exact ⟨beq_iff_eq.1 h1, of_decide_eq_true h2, (trees_of_live hS hL O _).trans (beq_iff_eq.1 h3)⟩

/-- **The field `fits` of `ExactAsks` at every code switch of the description.** -/
theorem switch_fits (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) :
    ∀ x ∈ switchPlaces Z Bs.G₀,
      K1.sendFits (ProofFile.Honest.K2.sendingPar x.sizes.codes (switchSent x.sizes x.others))
        (ProofFile.Honest.K2.rideOf (switchSent x.sizes x.others)
          (ProofFile.Honest.K2.switchFresh x.sizes x.others x.foldVars)) = true := by
  intro x hx
  rw [places_of_live hS hL O] at hx
  exact fits_of_mem hx

/-- **What the description's rounds read of a code switch's trees is within the bound.** -/
theorem reads_at_switch (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) :
    ∀ x ∈ switchPlaces Z Bs.G₀,
      OnBytes.SendSim.Seat.ReadsWithin F
        (ProofFile.Honest.K2.sendingPar x.sizes.codes (switchSent x.sizes x.others))
        (OnBytes.SendSim.Seat.treesOf F.first.blocksInOrder (F.first.blocksInOrder.takeWhile (·.place != x.place))) := by
  intro x hx
  obtain ⟨l, hl⟩ := exists_zipIdx _ 0 x hx
  obtain ⟨h1, h2, h3⟩ := places_tied hS hL O (x, l) hl
  have hl' := hl
  rw [places_of_live hS hL O] at hl'
  have hi : 3 * (l + 1) < 82 := of_decide_eq_true (List.all_eq_true.1 places_lt (x, l) hl')
  have e1 : switchSent x.sizes x.others = OnBytes.M1.sentAt (3 * (l + 1)) := h1
  have e2 : x.sizes.codes = codesW := h2
  have e3 : OnBytes.SendSim.Seat.treesOf F.first.blocksInOrder
      (F.first.blocksInOrder.takeWhile (·.place != x.place)) = treesBefore (3 * (l + 1)) := h3
  rw [e1, e2, e3]
  exact OnBytes.M1.atDescription P hS hL F Z Bs base c A B O _ hi

/-- **The code switch's own count, at what the description's rounds read**, at every due list. -/
theorem switch_asks (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (x : SwitchPlace) (hx : x ∈ switchPlaces Z Bs.G₀) (ρ : Draws) (hρ : ρ.due F = true) (r : Nat) :
    ProofFile.Honest.K2.asksWithin x.sizes.codes (switchSent x.sizes x.others)
      ((List.range r).map fun i => ProofFile.Honest.treeAsks F ρ 0
        (OnBytes.SendSim.Seat.treesOf F.first.blocksInOrder (F.first.blocksInOrder.takeWhile (·.place != x.place)) + i)) := by
  intro j l hj k hk hτ
  have R := reads_at_switch hS hL O x hx ρ hρ
  have hs := sendingPar_sent x.sizes.codes (switchSent x.sizes x.others)
  have hc : (ProofFile.Honest.K2.sendingPar x.sizes.codes (switchSent x.sizes x.others)).codes =
      x.sizes.codes := rfl
  have h := R k j (by rw [hs]; exact hk) (by rw [hs, hc]; exact hτ)
  simp only [Johnson.Prover.Send.shapeAt, hs, hc] at h
  have hl : l = ProofFile.Honest.treeAsks F ρ 0
      (OnBytes.SendSim.Seat.treesOf F.first.blocksInOrder (F.first.blocksInOrder.takeWhile (·.place != x.place)) + j) := by
    simp only [List.getElem?_map, List.getElem?_range'] at hj
    by_cases hjr : j < r
    · simp [List.getElem?_range, hjr] at hj
      exact hj.symm
    · simp [List.getElem?_range, hjr] at hj
  rw [hl]
  exact ⟨fun hm => (eraseDups_length_le _).trans (h.1 hm),
    fun hm => (eraseDups_length_le _).trans (h.2 hm)⟩

end

end Johnson.M1

#print axioms Johnson.M1.reads_at_switch
#print axioms Johnson.M1.switch_asks
#print axioms Johnson.M1.switch_fits
