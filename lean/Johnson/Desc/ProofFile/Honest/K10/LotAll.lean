-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/LotAll.lean: the closing of a segment (K10), with K9's batching: the frame's two tests
on halves (`twice`, `strays`, Honest/Frame.lean), and the kinds of the places, at all that the lot `seatLotT`
(Honest/K10/SeatLotT.lean) lays: K9's own halves (`K9.batHalves`, Honest/K9/Part.lean) and the kind's; and `strays` at
the lot with the closings alone (`seatLotC`, Honest/K10/SeatLotC.lean). Fourteen theorems; no definition. The eight that
have a premise on the description have no other on it than `IM.Open` (Johnson/IMR/SeatOpen.lean): at every older hash;
no premise on scope in any of the fourteen.

  `link_in_flat`, `a9_in_link`, `a10_in_link`   the driver's table of places (`flatPlacesOf`,
                   Johnson/Desc/First/Driver/Chain.lean) holds, at each of its links, the batching's place and the
                   closing's
  `twice_nil`, `strays_nil`   `twice` finds nothing where the halves' places have no double; `strays` nothing where
                   each half's place is a block's
  `seatLotT_kinds`   each half that the lot lays stands at a place of the kind K9 or of the kind K10: no premise; Z too
                   is a letter. Called by nobody: kept for a caller that wants the kinds of the lot's places; none is at
                   hand
  `where_is`         the four numbers of place that the lot reads at a link (chain, link, piece, pieceEq) are the
                   driver's (the library's `IM.k9_alone`, called); of rows, work, sent nothing
  `bat_place`        a half of K9's own stands at the driver's place of the batching of a link
  `close_place`      a place of the kind that the lot reads is the driver's place of the closing of a link
  `bat_places_once`  K9's own halves: no two at one place
  `lot_places_once`  of all that the lot lays no two stand at one place (a place of the kind K9 is none of the kind K10)
  **`lot_no_twice`**    `twice ((seatLotT …).halves Z G) = []`
  **`lot_no_strays`**   `strays F.first.blocksInOrder ((seatLotT …).halves Z G) = []`: at the description's own list
  **`seatLotC_clean`**   `strays F.first.blocksInOrder ((seatLotC …).halves Z G) = []`: the same of the closings alone

Called: `links_once`, `where_in_links` (Johnson/Desc/K10/Honest/LinksOnce.lean); `filterMap_key`, `filter_le_one`,
`halves_once` (Honest/K10/LotPlaces.lean); `seatLotT_halves`, `closingsT_are` (SeatLotT.lean); `seatLotC_halves`
(SeatLotC.lean); the library's `IM.k9_alone`, `IM.k9Where_fields`, `IM.k10Par_fields` (Johnson/IMR/LinkSeat.lean),
`IM.places_any` (Johnson/IMR/PlacesScope.lean). Where other names of the statements are defined: `closePars`
(Honest/K10/AtLot.lean), `closePlace` (Half.lean), `IM.a9Of` (Johnson/IMR/LinkSeat.lean), `ProofFile.subsOf`
(Johnson/Desc/ProofFile/Frames1.lean), `ProofFile.k9Where`, `ProofFile.k9Stretches` (Johnson/Desc/ProofFile/Lot/K9.lean).

Limits. Of these two lots' halves, and of their places alone (of a half's parts nothing). The three head theorems, and
`seatLotT_kinds`, hold also where the lot lays nothing: that a half stands at each place that has a round is not said
here. The frame's `readyTests` runs `twice` and `strays`
over the prover's list `H.first`: that no half of another lot stands at one of these places, and that another lot's are
no strays, is not said; nor that the prover's list of halves holds this lot's at all; nor `FileDescription.placesOk`, the two
tests on the range, the tests on the book, the two other chains. They say: where the maker has returned, the lot's
halves are clean: `links_once` is read off the maker's own test. At the Z of `IM.Open` (but `seatLotT_kinds`: at every
Z); G is a letter. Three of the eight have a second premise, on a list read off Z. Whether `IM.Open` can be had is no
theorem. F is a description at `ProofFile.Inst`, the halves stand at a letter Xi: the frame's calls want the same one for
both. `no_strays` (LotPlaces.lean), of the kind's halves in scope, follows from `lot_no_strays`' road without scope; it
is left as it is. No line that can fail. Nothing here is on coins. No property of the protocol is claimed: nothing is
said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.LotPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching flatPlacesOf linkPlaces closeAddresses closeKinds)
open VerifiableInference.Desc.First.Close (Par)

variable {W₀ Rc Xi Tr V W X : Type}

/-! ## The driver's table holds the two places of a link -/

theorem link_in_flat {links : List ModelPart} {several : Bool} {l : Nat} {sub : ModelPart}
    (h : links[l]? = some sub) {a : Place} (ha : a ∈ linkPlaces l sub) :
    a ∈ flatPlacesOf links several := by
  unfold flatPlacesOf
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ ?_))
  exact List.mem_flatMap.2 ⟨(sub, l), List.mk_mem_zipIdx_iff_getElem?.2 (by simpa using h), ha⟩

theorem a9_in_link (l : Nat) (sub : ModelPart) : IM.a9Of l sub ∈ linkPlaces l sub := by
  unfold linkPlaces
  simp

theorem a10_in_link (l : Nat) (sub : ModelPart) :
    (⟨1, some l, (kindsBeforeBatching sub (l == 0)).length + 4, .K10⟩ : Place) ∈ linkPlaces l sub := by
  unfold linkPlaces closeAddresses closeKinds
  simp

/-! ## Two small ones on the frame's two tests -/

theorem twice_nil {hs : List (Placed V W X)} (h : (hs.map (·.place)).Nodup) : twice hs = [] := by
  unfold twice
  rw [List.filter_eq_nil_iff.2 fun a _ hb => ?_]
  · rfl
  · have h1 := filter_le_one (fun x : Placed V W X => x.place) hs h a
    have h2 : 1 < (hs.filter fun x => x.place == a).length := by simpa using hb
    omega

theorem strays_nil {σ C : Type} {bs : List (Block σ C)} {hs : List (Placed V W X)}
    (h : ∀ x ∈ hs, x.place ∈ bs.map (·.place)) : strays bs hs = [] := by
  unfold strays
  rw [List.filter_eq_nil_iff.2 fun x hx hb => ?_]
  · rfl
  · obtain ⟨b, hb1, hb2⟩ := List.mem_map.1 (h x hx)
    have h1 : (bs.any fun b => b.place == x.place) = true :=
      List.any_eq_true.2 ⟨b, hb1, by rw [hb2]; exact beq_self_eq_true _⟩
    have h2 : (!(bs.any fun b => b.place == x.place)) = true := hb
    rw [h1] at h2
    cases h2

/-! ## The kinds of all that the lot lays -/

/-- **Each half that the lot lays stands at a place of the kind K9 or of the kind K10.** No premise. -/
theorem seatLotT_kinds (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi)
    (stAt : StAtOf Xi) (Z : ProofFile.Pub) (G : Ground) :
    ∀ x ∈ (seatLotT (X := X) readers rows stAt).halves Z G,
      x.place.kind = KindName.K9 ∨ x.place.kind = KindName.K10 := by
  intro x hx
  rw [seatLotT_halves] at hx
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨l, _, hf⟩ := List.mem_filterMap.1 hx
    obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 hf
    exact Or.inl rfl
  · rw [closingsT_are] at hx
    obtain ⟨Q, _, rfl⟩ := List.mem_map.1 hx
    exact Or.inr rfl

/-! ## The places of all that the lot lays -/

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- The four numbers of place that the lot reads at a link of its list (chain, link, piece, pieceEq) are the driver's;
of rows, work, sent nothing. -/
theorem where_is (O : IM.Open o pol lay KL F Z Bs base c A B) {l : Nat}
    {p : VerifiableInference.Desc.K9.Where} (hp : ProofFile.k9Where (ProofFile.k9Stretches Z) l = some p) :
    ∃ sub, (ProofFile.subsOf Z)[l]? = some sub ∧ p.chain = 1 ∧ p.link = l ∧
      p.piece = (kindsBeforeBatching sub (l == 0)).length + 1 ∧ p.pieceEq = p.piece + 2 := by
  have hl := ((YesFree.links_once O).2 l).1 (YesFree.where_in_links hp)
  obtain ⟨_, p', _, hp', h1, h2, h3, h4, _⟩ := IM.k9_alone O l _ (List.getElem?_eq_getElem hl)
  obtain rfl : p' = p := Option.some.inj (hp'.symm.trans hp)
  exact ⟨_, List.getElem?_eq_getElem hl, h2, h3, h1, h4⟩

/-- **A half of K9's own stands at the driver's place of the batching of a link.** -/
theorem bat_place (O : IM.Open o pol lay KL F Z Bs base c A B) {x : Placed V W X}
    (hx : x ∈ K9.batHalves Z) :
    ∃ l sub, (ProofFile.subsOf Z)[l]? = some sub ∧ x.place = IM.a9Of l sub := by
  obtain ⟨l, _, hf⟩ := List.mem_filterMap.1 hx
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 hf
  obtain ⟨sub, hs, h1, h2, h3, _⟩ := where_is O hp
  refine ⟨l, sub, hs, ?_⟩
  show (⟨p.chain, some p.link, p.piece, .K9⟩ : Place) = _
  rw [h1, h2, h3]

/-- **A place of the kind that the lot reads is the driver's place of the closing of a link.** -/
theorem close_place (O : IM.Open o pol lay KL F Z Bs base c A B) {Q : Par} (hQ : Q ∈ closePars Z) :
    ∃ l sub, (ProofFile.subsOf Z)[l]? = some sub ∧
      closePlace Q = ⟨1, some l, (kindsBeforeBatching sub (l == 0)).length + 4, .K10⟩ := by
  obtain ⟨l, _, hf⟩ := List.mem_filterMap.1 hQ
  obtain ⟨p, hp, hq⟩ := Option.bind_eq_some_iff.1 hf
  obtain ⟨sub, hs, _, h2, h3, h4⟩ := where_is O hp
  obtain ⟨q1, q2⟩ := IM.k10Par_fields hq
  refine ⟨l, sub, hs, ?_⟩
  show (⟨1, some Q.link, Q.piece, .K10⟩ : Place) = _
  rw [q1, q2, h2, h4, h3]

/-- K9's own halves: no two at one place. -/
theorem bat_places_once (O : IM.Open o pol lay KL F Z Bs base c A B) :
    ((K9.batHalves (V := V) (W := W) (X := X) Z).map (·.place)).Nodup := by
  have h1 : ((K9.batHalves (V := V) (W := W) (X := X) Z).map fun x => x.place.link.getD 0).Nodup := by
    refine (filterMap_key (fun l => (ProofFile.k9Where (ProofFile.k9Stretches Z) l).map K9.batHalf)
      (fun x : Placed V W X => x.place.link.getD 0) (fun l a h => ?_) _).nodup
      (YesFree.links_once O).1
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 h
    exact (IM.k9Where_fields hp).2.1
  refine List.Nodup.of_map (fun a : Place => a.link.getD 0) ?_
  rw [List.map_map]
  exact h1

/-- **Of all that the lot lays no two stand at one place.** -/
theorem lot_places_once (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi)
    (stAt : StAtOf Xi) (G : Ground)
    (O : IM.Open o pol lay KL F Z Bs base c A B) :
    (((seatLotT (X := X) readers rows stAt).halves Z G).map (·.place)).Nodup := by
  rw [seatLotT_halves, List.map_append]
  refine List.nodup_append.2 ⟨bat_places_once O, halves_once readers rows stAt G O, ?_⟩
  intro a ha b hb e
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
  obtain ⟨_, _, _, e1⟩ := bat_place O hx
  rw [closingsT_are] at hy
  obtain ⟨Q, _, rfl⟩ := List.mem_map.1 hy
  have e2 : x.place.kind = KindName.K10 := by rw [e]; rfl
  rw [e1] at e2
  cases e2

/-- **The frame's `twice` finds nothing among all that the lot lays.** -/
theorem lot_no_twice (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi)
    (stAt : StAtOf Xi) (G : Ground)
    (O : IM.Open o pol lay KL F Z Bs base c A B) :
    twice ((seatLotT (X := X) readers rows stAt).halves Z G) = [] :=
  twice_nil (lot_places_once readers rows stAt G O)

/-- **The frame's `strays` finds nothing among all that the lot lays, at the description's own list `F.first.blocksInOrder`.** At
every older hash; no premise on scope. -/
theorem lot_no_strays (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi)
    (stAt : StAtOf Xi) (G : Ground)
    (O : IM.Open o pol lay KL F Z Bs base c A B) :
    strays F.first.blocksInOrder ((seatLotT (X := X) readers rows stAt).halves Z G) = [] := by
  have key : ∀ x ∈ (seatLotT (X := X) readers rows stAt).halves Z G,
      x.place ∈ c.blocksInOrder.map (·.place) := by
    intro x hx
    rw [IM.places_any O]
    rw [seatLotT_halves] at hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨l, sub, hs, e⟩ := bat_place O hx
      rw [e]
      exact link_in_flat hs (a9_in_link l sub)
    · rw [closingsT_are] at hx
      obtain ⟨Q, hQ, rfl⟩ := List.mem_map.1 hx
      obtain ⟨l, sub, hs, e⟩ := close_place O hQ
      show closePlace Q ∈ _
      rw [e]
      exact link_in_flat hs (a10_in_link l sub)
  obtain rfl := O.desc
  exact strays_nil key

/-- **The same of the lot with the closings alone** (`seatLotC`, Honest/K10/SeatLotC.lean). At every older hash; no
premise on scope. -/
theorem seatLotC_clean (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi)
    (stAt : StAtOf Xi) (G : Ground)
    (O : IM.Open o pol lay KL F Z Bs base c A B) :
    strays F.first.blocksInOrder ((seatLotC (X := X) readers rows stAt).halves Z G) = [] := by
  have key : ∀ x ∈ (seatLotC (X := X) readers rows stAt).halves Z G,
      x.place ∈ c.blocksInOrder.map (·.place) := by
    intro x hx
    rw [IM.places_any O]
    rw [seatLotC_halves] at hx
    obtain ⟨Q, hQ, rfl⟩ := List.mem_map.1 hx
    obtain ⟨l, sub, hs, e⟩ := close_place O hQ
    show closePlace Q ∈ _
    rw [e]
    exact link_in_flat hs (a10_in_link l sub)
  obtain rfl := O.desc
  exact strays_nil key

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.link_in_flat
#print axioms ProofFile.Honest.K10.a9_in_link
#print axioms ProofFile.Honest.K10.a10_in_link
#print axioms ProofFile.Honest.K10.twice_nil
#print axioms ProofFile.Honest.K10.strays_nil
#print axioms ProofFile.Honest.K10.seatLotT_kinds
#print axioms ProofFile.Honest.K10.where_is
#print axioms ProofFile.Honest.K10.bat_place
#print axioms ProofFile.Honest.K10.close_place
#print axioms ProofFile.Honest.K10.bat_places_once
#print axioms ProofFile.Honest.K10.lot_places_once
#print axioms ProofFile.Honest.K10.lot_no_twice
#print axioms ProofFile.Honest.K10.lot_no_strays
#print axioms ProofFile.Honest.K10.seatLotC_clean
