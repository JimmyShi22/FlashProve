-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/NoStrayLots.lean: CONDITIONAL, UNDER THE HEAD: NO HALF OF THE
LISTS OF K2 (the code switch), K3 (the lookups) AND K1 (the commitments) STRAYS IN THE FIRST CHAIN:
three more of the lines that "the maker onlineProverFromPublicFiles returns" asks at the filling widerFillAt.

Main names:
  `k2W_in_ps`, `k3Place_in_ps`, `flatK1_in_ps`: three closed facts by Lean's kernel on written lists
    of places. The third is asked of the places of the kind K1 inside a link alone.
  `flatK1_all_fails`, `flat_all_fails`: closed facts too: without "inside a link", and without the
    kind, the third sentence is false: neither clause of its filter is idle; they say no more.
  `switchLot_no_strays`: by `FirstFill.k2_places_sub`
    (Johnson/Desc/ProofFile/Honest/Thread/FirstFillK2.lean) and the library's
    `H2K12.k2_places_written`.
  `shapeLinks_25`: under the head the request's shape has 25 links: off the entry tests' row on what
    the planner made.
  `theLotInst_no_strays`: by `site_place_head` and `site_link_lt`
    (Johnson/Desc/ProofFile/Honest/K3/Law/Thread/AtLink.lean, ThereOf.lean).
  `k1_block_in_ps`: under the head every block of the kind K1 inside a link, of the description's
    seat, stands at a place of the written list: a seat without a fault has its blocks at places
    of the shape
    (`IM.stands_in_shape`, `IM.shape_places`).
  `dataSideNo_no_strays`: the halves' places are those of the kind's own blocks
    (`K1.dataSideNo_places`).

Limits. Conditional on the head; K1's line also on hG: G is the ground that is made of the head's
public part. The head has a member at the library's written copy of the full-size public files
(`AtFullSide.Top.headMember_zFull`, AtFullSide/Top/HeadMemberAtFull.lean), which is tied to the
package's files by no theorem. General in the lists' own letters. Nothing is said of what a half
does. The five closed facts are decided by Lean's kernel by evaluation at written lists (the depth
of recursion is raised for them). `shapeLinks_25` has kin in the library's `first_links_in_scope`
(Johnson/Goal/Numbers/RequestLinks.lean), which asks the test on the first chain's parameters as a
premise. At the library's full size and the function `OnBytes.secondHashFunction` alone. Through its imports the
file stands above the files under ThirdParty/ (lean/LIMITS.md, L15).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.NoStrayThree
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillK2
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillKinds
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtLink
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ThereOf
import Johnson.Desc.ProofFile.Honest.K3.LotInst
import Johnson.Loose.H2K12.SpotsAtAll
import Johnson.Goal.Skeleton.CutIsOfLaid
import Johnson.Goal.Numbers.RequestLinks
import Johnson.LPFK9R.SubsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Place KindName Block)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

set_option maxRecDepth 1000000 in
/-- The 25 written addresses of the kind K2 stand in the written list of places. A closed fact. -/
theorem k2W_in_ps : ∀ a ∈ H2K12.k2W, a ∈ P5J.At.ps := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The 50 written places of the lookups stand in the written list of places. A closed fact. -/
theorem k3Place_in_ps : ∀ l < 25, ∀ d : Bool, IM.k3Place l d ∈ P5J.At.ps := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The places of the kind K1 inside a link in the driver's table at the written list of the
segments' sorts, at either value of its second letter, stand in the written list of places. A closed
fact. By the two theorems behind it neither clause of the filter is idle. -/
theorem flatK1_in_ps : ∀ s : Bool, ∀ a ∈ (VerifiableInference.Desc.First.flatPlacesOf
    VerifiableInference.Desc.Sound.linksFull s).filter (fun a => a.kind == .K1 && a.link.isSome),
    a ∈ P5J.At.ps := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Of all places of the kind K1 the sentence is false: "inside a link" is not idle. A closed fact.
It says no more than that. -/
theorem flatK1_all_fails : ¬ ∀ s : Bool, ∀ a ∈ (VerifiableInference.Desc.First.flatPlacesOf
    VerifiableInference.Desc.Sound.linksFull s).filter (fun a => a.kind == .K1),
    a ∈ P5J.At.ps := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Of the places of all kinds the sentence is false. A closed fact; it follows from the one above.
It says no more than that. -/
theorem flat_all_fails : ¬ ∀ s : Bool, ∀ a ∈ VerifiableInference.Desc.First.flatPlacesOf
    VerifiableInference.Desc.Sound.linksFull s, a ∈ P5J.At.ps := by decide +kernel

variable {W₀ Rc Tr X : Type}

/-- **K2's line.** Conditional: h. -/
theorem switchLot_no_strays (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) (G : Ground)
    (Dt : RowDataOf Inst) (readers : Local W₀ Rc Inst Tr → Readers) :
    strays (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
      ((K2.switchLot (X := X) Dt readers).halves Zp G) = [] := by
  refine strays_of_ps h fun z hz => ?_
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  rw [FirstFill.k2_halves] at hz
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hz
  show p.place ∈ P5J.At.ps
  obtain ⟨sp, hsp, e⟩ := List.mem_map.1
    ((FirstFill.k2_places_sub Zp G).subset (List.mem_map_of_mem hp))
  rw [← e]
  exact k2W_in_ps _ ((H2K12.k2_places_written h.scope h.reads O).2 sp hsp)

/-- Under the head the request's shape has 25 links. Conditional: h. -/
theorem shapeLinks_25 (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) :
    Zp.first.shape.link.length = 25 := by
  have hk := VerifiableInference.PlanWritten.key_in_scope_pure h.scope h.laid.pub
  have hy := (LPFD.asks_pins h.laid.asks h.laid.pub (decide_eq_true hk)).1
  unfold VerifiableInference.PlanWritten.madeRow at hy
  simp only [Bool.and_eq_true] at hy
  rw [(VerifiableInference.PlanWritten.first_of_is hy.1.1.2).2.2.1]
  exact VerifiableInference.PlanWritten.request_links_written

/-- **K3's line.** Conditional: h. -/
theorem theLotInst_no_strays (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) (G : Ground)
    (cells : Tr → Cells) (weights : W₀ → Weights) :
    strays (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
      ((K3.theLotInst (Rc := Rc) (X := X) cells weights).halves Zp G) = [] := by
  refine strays_of_ps h fun z hz => ?_
  have hz' : z ∈ (K3.lookSites Zp).map fun s =>
      K3.Law.AtThr.seatAt (Rc := Rc) (X := X) cells weights (K3.reqAt Zp) Zp s := hz
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hz'
  show s.at_.place ∈ P5J.At.ps
  rw [K3.Law.AtThr.site_place_head h s hs]
  exact k3Place_in_ps _ (by rw [← shapeLinks_25 h]; exact K3.Law.AtThr.site_link_lt Zp s hs) _

/-- **Under the head every block of the kind K1 inside a link, of every list of the description's
seat, stands at a place of the written list.** Conditional: h; O: the opening; ho; hk; hl. -/
theorem k1_block_in_ps (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) {Bs : PureBase}
    {base : List (Block VerifiableInference.Desc.First.S Cl)} {A : SharedSeat} {B : SecondSeat}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF A
      B)
    {o : Block VerifiableInference.Desc.First.S Cl} (ho : o ∈ Bs.all.flatMap fun y => y.2)
    (hk : o.place.kind = KindName.K1) (hl : o.place.link ≠ none) : o.place ∈ P5J.At.ps := by
  obtain ⟨e, he, ee⟩ := IM.stands_in_shape O.sound ho (by rw [hk]; decide)
  obtain ⟨s, hs⟩ := IM.shape_places (IM.base_made O.made).2.1
  have h1 : e.2 ∈ Bs.shape.map (·.2) := List.mem_map_of_mem he
  rw [hs, LPFK9.subs_full h.scope h.reads O, ee] at h1
  refine flatK1_in_ps s _ (List.mem_filter.2 ⟨h1, ?_⟩)
  rw [hk, Option.isSome_iff_ne_none.2 hl]
  rfl

/-- **K1's line.** Conditional: h; hG. -/
theorem dataSideNo_no_strays {V W : Type} (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) (S : OnBytes.HonestTrace.Sz)
    (wit : W → K1.PlaceIn ProofFile.Inst) (o : SecondHashFunctionArgument) :
    strays (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
      ((K1.dataSideNo (V := V) (X := X) S wit o).halves Zp G) = [] := by
  refine strays_of_ps h fun z hz => ?_
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  have hm : z.place ∈ ((K1.dataSideNo (V := V) (X := X) S wit o).halves Zp Bs.G₀).map (·.place) :=
    List.mem_map_of_mem hz
  have hm' : z.place ∈ ((k1Pure Zp).own Bs.G₀).map (·.place) := by
    unfold k1Pure
    dsimp only
    rw [← K1.dataSideNo_places (V := V) (X := X) S wit o _ Zp Bs.G₀]
    exact hm
  obtain ⟨b, hb, e⟩ := List.mem_map.1 hm'
  have hL : k1Pure Zp ∈ (pureSeat OnBytes.secondHashFunction Zp).lots := by
    show k1Pure Zp ∈ onlineFirstChainBlockTables Zp
    unfold onlineFirstChainBlockTables
    simp
  have ho : (b.retype : Block VerifiableInference.Desc.First.S Cl) ∈
      Bs.all.flatMap fun y => y.2 := by
    refine List.mem_flatMap.2 ⟨(k1Pure Zp, (k1Pure Zp).blocks Bs.G₀), ?_, ?_⟩
    · rw [(IM.base_made O.made).2.2.2]
      exact List.mem_map.2 ⟨_, hL, rfl⟩
    · exact List.mem_append_left _ (List.mem_map_of_mem hb)
  have hk : (b.retype : Block VerifiableInference.Desc.First.S Cl).place.kind = KindName.K1 := by
    show b.place.kind = KindName.K1
    rw [e, FirstFill.k1_kind S wit o Zp Bs.G₀ z hz]
  have hlk : (b.retype : Block VerifiableInference.Desc.First.S Cl).place.link ≠ none := by
    show b.place.link ≠ none
    rw [e]
    exact FirstFill.k1_linked S wit o Zp Bs.G₀ z hz
  have := k1_block_in_ps h O ho hk hlk
  rw [← e]
  exact this

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k2W_in_ps
#print axioms ProofFile.Honest.K5.k3Place_in_ps
#print axioms ProofFile.Honest.K5.flatK1_in_ps
#print axioms ProofFile.Honest.K5.flatK1_all_fails
#print axioms ProofFile.Honest.K5.flat_all_fails
#print axioms ProofFile.Honest.K5.switchLot_no_strays
#print axioms ProofFile.Honest.K5.shapeLinks_25
#print axioms ProofFile.Honest.K5.theLotInst_no_strays
#print axioms ProofFile.Honest.K5.k1_block_in_ps
#print axioms ProofFile.Honest.K5.dataSideNo_no_strays
