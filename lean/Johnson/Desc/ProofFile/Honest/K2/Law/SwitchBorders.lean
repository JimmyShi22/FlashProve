-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SwitchBorders.lean: the kind "the code switch" (K2): NUMBERS OF
A PUBLIC PLAN: THE SWITCHES' MEMBERS' NUMBERS IN THE FIRST CHAIN's FLAT LIST, UNDER THE HEAD AND THE
OPENING: the number that `borderNo` (Honest/Thread/Thr.lean, of other authors) finds for each place
of the kind's list. No two places have one number; none is a number of the shared sending's 52
members; at each stands a block, and it bears the place. The first and the third are the premises
hnd and hblk of `share_trees_fit` (Honest/K2/JoinShare.lean, not imported); the first two bear on
the field nums of `JoinFit` (Honest/Thread/JoinFit.lean, of other authors; not imported). Two
definitions: a list of numbers and a public test; a closed fact by evaluation in Lean's kernel, with
controls; lemmas.

  `switchBorders`    for each place of a list, where the written list of places first bears it
  `notShared`        A PUBLIC TEST: a number is not 2, not 356, nor that of a link's reads or digits
  `switchBordersW`   BY LEAN's KERNEL: 25 numbers; no two are one; each lies below the list's
                     length and passes `notShared`. CONTROLS: with the first place laid twice two
                     are one; the number 2 fails `notShared`
  `borders_at_head`        the numbers that `borderNo` finds are `switchBorders` of the written list
  `borders_apart_at_head`  no two places have one number
  `border_test_at_head`    what the closed fact says of one place's number
  `border_not_shared`      none is a number of the list `k1MembersW`
  `border_block_at_head`   a block stands there, and it bears the place

By, of other authors: `borderNo_written` (Honest/K1/Law/MembersByBorder.lean) · `mem_k1MembersW`
(Honest/K1/Law/LotsAtAll.lean) · `mem_k1Members` · the sealed `places_paid`
(Johnson/P5J/PlacesPaid.lean). Of ours: `places_at_head` (Honest/K2/Law/PlacesWritten.lean).

Limits. PLACES AND NUMBERS ALONE: no lot, coin, input or run occurs. The full size and the format's
second hash function alone. The head and the opening are premises; that they can be met is not said. Nothing
on any property.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.MembersByBorder
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- For each written place, where the written list of places first bears it. -/
def switchBorders (l : List SwitchPlace) : List Nat :=
  l.map fun p => P5J.At.ps.findIdx (· == p.place)

/-- A number is none of the shared sending's 52 members'. -/
def notShared (b : Nat) : Bool :=
  b != 2 && b != 356 && (List.range 25).all fun l => [false, true].all fun d =>
    b != VerifiableInference.Desc.K1.noL l d

set_option maxRecDepth 1000000 in
/-- **At the written lists**; two controls that say no. -/
theorem switchBordersW :
    (switchBorders placesW).length = 25 ∧ (switchBorders placesW).Nodup ∧
      ((switchBorders placesW).all fun b => decide (b < P5J.At.ps.length) && notShared b) = true ∧
      ¬ (switchBorders (placesW ++ placesW.take 1)).Nodup ∧ notShared 2 = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- **UNDER THE HEAD AND THE OPENING: the numbers that `borderNo` finds.** -/
theorem borders_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    (switchPlaces Zp Bs.G₀).map (fun p => borderNo cF.blocksInOrder p.place) = switchBorders placesW := by
  rw [places_at_head h.toAtMg O]
  exact List.map_congr_left fun p _ => K1.borderNo_written h p.place

/-- **No two places have one number.** -/
theorem borders_apart_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ((switchPlaces Zp Bs.G₀).map fun p => borderNo cF.blocksInOrder p.place).Nodup := by
  rw [borders_at_head h O]
  exact switchBordersW.2.1

/-- What the closed fact says of one place's number. -/
theorem border_test_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) :
    borderNo cF.blocksInOrder p.place < P5J.At.ps.length ∧ notShared (borderNo cF.blocksInOrder p.place) = true := by
  have hm : borderNo cF.blocksInOrder p.place ∈ switchBorders placesW := by
    rw [← borders_at_head h O]
    exact List.mem_map.2 ⟨p, hp, rfl⟩
  have t := List.all_eq_true.1 switchBordersW.2.2.1 _ hm
  rw [Bool.and_eq_true, decide_eq_true_eq] at t
  exact t

/-- **None is a number of the shared sending's list.** -/
theorem border_not_shared {Xi X : Type} (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀)
    (J₂ : K1.SendJob (K1.PlaceIn Xi) X) (Jl : Nat → Bool → K1.SendJob (K1.PlaceIn Xi) X)
    (Jw : K1.SendJob (K1.PlaceIn Xi) X) :
    borderNo cF.blocksInOrder p.place ∉ (K1.k1MembersW J₂ Jl Jw).map (·.1) := by
  have t := (border_test_at_head h O hp).2
  unfold notShared at t
  rw [Bool.and_eq_true, Bool.and_eq_true, bne_iff_ne, bne_iff_ne, List.all_eq_true] at t
  intro hm
  obtain ⟨x, hx, e⟩ := List.mem_map.1 hm
  rcases K1.mem_k1MembersW.1 hx with hx | rfl
  · rcases K1.mem_k1Members.1 hx with rfl | ⟨l, hl, d, rfl⟩
    · exact t.1.1 e.symm
    · have u := List.all_eq_true.1 (t.2 l (List.mem_range.2 hl)) d (by cases d <;> simp)
      exact (bne_iff_ne.1 u) e.symm
  · exact t.1.2 e.symm

/-- **A block stands at the number, and it bears the place.** -/
theorem border_block_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) :
    ∃ blk, cF.blocksInOrder[borderNo cF.blocksInOrder p.place]? = some blk ∧ blk.place = p.place := by
  have hlen : (cF.blocksInOrder.map (·.place)).length = P5J.At.ps.length :=
    congrArg List.length (P5J.At.places_paid h.scope h.reads h.laid)
  rw [List.length_map] at hlen
  have hlt : borderNo cF.blocksInOrder p.place < cF.blocksInOrder.length := by
    rw [hlen]
    exact (border_test_at_head h O hp).1
  refine ⟨cF.blocksInOrder[borderNo cF.blocksInOrder p.place]'hlt, List.getElem?_eq_getElem hlt, ?_⟩
  have hlt' : cF.blocksInOrder.findIdx (fun y : Block S ProofFile.Cl => y.place == p.place) < cF.blocksInOrder.length :=
    hlt
  have t := List.findIdx_getElem (w := hlt')
  exact beq_iff_eq.1 t

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.switchBorders
#print axioms ProofFile.Honest.K2.Law.notShared
#print axioms ProofFile.Honest.K2.Law.switchBordersW
#print axioms ProofFile.Honest.K2.Law.borders_at_head
#print axioms ProofFile.Honest.K2.Law.borders_apart_at_head
#print axioms ProofFile.Honest.K2.Law.border_test_at_head
#print axioms ProofFile.Honest.K2.Law.border_not_shared
#print axioms ProofFile.Honest.K2.Law.border_block_at_head
