-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/LotNoStrayOpen.lean: CONDITIONAL.

What is here. NO HALF OF K4's LOT STRAYS, FROM THE THREE FACTS THAT THE FRAME's MAKER `onlineProverFromPublicFiles`
(Honest/AtPure.lean) HAS IN HAND BEHIND ITS FIRST THREE BINDS (`k4HLot_noStray_desc`): the public
part, the ground and the description are what `ProofFile.pubPlain`, `ProofFile.blankBy ProofFile.pureRoad.links` and
`ProofFile.onlineDescription` return. WITHOUT THE LIBRARY's HYPOTHESIS ON THE PUBLIC FILES: at every hash function
in the earlier hash's stead, at every size at which the makers return. The lot (`k4HLot`,
Honest/K4/Part.lean) is the entry of the feed-forward layers' own rounds (the sub-protocol K4) in a
filling of the honest prover; a half is the prover's side for one member of the chain. `strays`
(Honest/Frame.lean) is the frame's test: the places of halves at which no member of the chain
stands. (1) at an opening of the description (`IM.Open`, Johnson/IMR/SeatOpen.lean): a member of the
chain's flat list stands at the place of each member of the lot's own list (`k4From`): that member
stems from a segment of the kind 0 at its number (`IM.k4List_mem`), the driver's row has "layers"
there (`IM.subs_of_kind`), and the chain has a lot's sub-protocol alone at piece 3 of such a segment
(`IM.chain_hear_alone`). (2) so `strays` of the lot's halves at the opening's chain is empty. (3)
THE SAME FROM THE THREE RETURNS: `strays` at the description's own first chain is empty: by
`IM.seat_open`. General in cells, weights and look. ITS IMPORT LINES
NAME Honest/K4/Part.lean AND TWO OF THE LIBRARY's (Johnson/IMR/K4Seat.lean,
Johnson/IMR/FlatIx.lean).

  `k4From_member_open`   a member of the chain at the place of each member of the lot's own list.
  `k4HLot_member_open`   a member of the chain at each half's place.
  `strays_nil_of_member`   the frame's test is empty where each half's place has a member.
  `k4HLot_noStray_open`   **`strays` of the lot's halves is empty**, at an opening.
  `k4HLot_noStray_desc`   **the same from the three returns.**

Not shown here. THAT ANY OF THE THREE MAKERS RETURNS. THAT THE LOT LAYS A HALF: ALL OF IT HOLDS ALSO
WHERE THE LOT LAYS NOTHING, and says nothing there; under the library's hypothesis on the public
files the lot lays twelve halves, one at each of K4's twelve places: `k4HLot_twelve`,
`k4HLot_places_perm` (Law/LotTwelve.lean (no part of the library)). It is K4's share of a test
that the maker asks, and that the frame's `readyTests` (Honest/Frame.lean) asks again: both ask
`strays` of all lots' halves in one list; the step from the lots' shares to that list is not made
here. THE GROUND IS THE ONE THAT IS MADE OF THE PUBLIC PART (hG): at a free ground nothing is said.
On a place at which two halves stand: Law/LotOnce.lean. `strays_nil_of_member` is a small law on the
frame's own test, AND IT IS A TWIN: other kinds' writers have typed the like under other names:
`ProofFile.Honest.K14.strays_nil` (Honest/K14/NoStray.lean) is the same statement but for its letters,
with the two lists as explicit arguments; `ProofFile.Honest.K5.strays_of_mem`
(Honest/K5/Law/LotClean.lean) says it by membership in the list of places; it is typed here so that
no file of another kind's writers is imported. A LAW, NOT A PART: no file that defines a part of the
proof file's description may import this one: its imports reach modules under Johnson/Goal/:
Johnson/IMR/K4Seat.lean imports one. A program's walk of import lines, which stops unopened at every
module under Johnson/Goal/ or Johnson/Bridge/, stopped at two of each; what lies behind these four
has not been counted.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Part
import Johnson.IMR.K4Seat
import Johnson.IMR.FlatIx

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open VerifiableInference.Desc (Place Chain Block FileDescription KindName)
open VerifiableInference.Desc.First (S kindsBeforeBatching)

variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat} {W₀ Rc Tr X' : Type}

/-- CONDITIONAL: on O and hx. A member of the chain stands at the place of each member of the lot's
own list. -/
theorem k4From_member_open (O : IM.Open o pol lay KL F Z Bs base c A B) {x : Bool × Par}
    (hx : x ∈ ProofFile.k4From Z Bs.G₀ Bs.G₀.built.toList 0 none) :
    ∃ b ∈ c.blocksInOrder, b.place = (⟨1, some x.2.link, x.2.piece, .K4⟩ : Place) := by
  obtain ⟨j, X, a, K⟩ := IM.k4List_mem hx
  have hl : (ProofFile.subsOf Z)[j]? = some .layers := by
    rw [IM.subs_of_kind O.blank a, K.kind]
    rfl
  have hk : (kindsBeforeBatching .layers (j == 0))[2]? = some KindName.K4 := by
    unfold kindsBeforeBatching
    rfl
  obtain ⟨Lk, b, e1, e2, _, -, _, -, _, -, -, -, hla⟩ :=
    IM.chain_hear_alone O.made O.places O.chain j .layers hl 2 .K4 hk (by decide) (by decide)
      (by decide)
  refine ⟨b, List.mem_of_getElem? (IM.hear_at_flat e1 e2), ?_⟩
  rw [IM.alone_place hla, K.link, K.piece]

/-- CONDITIONAL: on O. A member of the chain stands at each half's place. -/
theorem k4HLot_member_open (O : IM.Open o pol lay KL F Z Bs base c A B) (cells : Tr → Cells)
    (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard) :
    ∀ z ∈ (k4HLot (Rc := Rc) (X := X') cells weights look).halves Z Bs.G₀,
      ∃ b ∈ c.blocksInOrder, b.place = z.place := by
  intro z hz
  obtain ⟨x, hx, e⟩ := List.mem_filterMap.1 hz
  obtain ⟨Q, hQ', rfl⟩ := Option.map_eq_some_iff.1 e
  obtain ⟨hQ, -⟩ := Option.filter_eq_some_iff.1 hQ'
  unfold k4PubOf at hQ
  obtain ⟨r0, -, rfl⟩ := Option.map_eq_some_iff.1 hQ
  exact k4From_member_open O hx

/-- A law on the frame's test: it is empty where each half's place has a member of the list. -/
theorem strays_nil_of_member {σ C V W X : Type} {bs : List (Block σ C)} {hs : List (Placed V W X)}
    (h : ∀ z ∈ hs, ∃ b ∈ bs, b.place = z.place) : strays bs hs = [] := by
  unfold strays
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro z hz hn
  obtain ⟨b, hb, e⟩ := h z hz
  have ha : (bs.any fun b => b.place == z.place) = true :=
    List.any_eq_true.2 ⟨b, hb, beq_iff_eq.2 e⟩
  have hn' : (!(bs.any fun b => b.place == z.place)) = true := hn
  rw [ha] at hn'
  exact Bool.false_ne_true hn'

/-- CONDITIONAL: on O. **NO HALF OF THE LOT STRAYS**, at an opening's chain. -/
theorem k4HLot_noStray_open (O : IM.Open o pol lay KL F Z Bs base c A B) (cells : Tr → Cells)
    (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard) :
    strays c.blocksInOrder ((k4HLot (Rc := Rc) (X := X') cells weights look).halves Z Bs.G₀) = [] :=
  strays_nil_of_member (k4HLot_member_open O cells weights look)

/-- CONDITIONAL: on the three returns. **NO HALF OF THE LOT STRAYS, AT THE DESCRIPTION's OWN FIRST
CHAIN.** -/
theorem k4HLot_noStray_desc {G : ProofFile.Ground} (hZ : ProofFile.pubPlain o pol lay KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) (hF : ProofFile.onlineDescription o pol lay KL = .ok F)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard) :
    strays F.first.blocksInOrder ((k4HLot (Rc := Rc) (X := X') cells weights look).halves Z G) = [] := by
  obtain ⟨Z', Bs', base', c', A', B', O⟩ := IM.seat_open hF
  obtain rfl : Z' = Z := Except.ok.inj (O.pub.symm.trans hZ)
  obtain rfl : Bs'.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  have e := k4HLot_noStray_open (Rc := Rc) (X' := X') O cells weights look
  rw [O.desc]
  exact e

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4From_member_open
#print axioms ProofFile.Honest.K4.k4HLot_member_open
#print axioms ProofFile.Honest.K4.strays_nil_of_member
#print axioms ProofFile.Honest.K4.k4HLot_noStray_open
#print axioms ProofFile.Honest.K4.k4HLot_noStray_desc
