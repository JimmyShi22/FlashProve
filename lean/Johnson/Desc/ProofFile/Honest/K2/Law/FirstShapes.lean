-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/FirstShapes.lean: the kind "the code switch" (K2): THREE PUBLIC
TIES BETWEEN A SWITCH's PLACE (`SwitchPlace`, Honest/K2/Half.lean) AND THE VERIFIER's SIDE, UNDER
THE HEAD: the shapes of its sending's messages are those of the first members of its link's written
list; the last message's shape is the chain's shape at the plan's number of the link's fresh mask;
its codes are those of a later switch's front's statement. Two definitions (tests on public data,
with code); statements with their proofs.

  `firstShapesTie` the test: the sending's shapes, but for the last message, are the shapes of the
                    first members of `loAt p₀.link`, in order
  `firstShapesTie_gives` what its yes gives, message by message
  `firstShapesTieW` BY THE KERNEL: it accepts at every written place that leads into a written
                    segment
  `firstShapesTieW_can_fail` at the next link's list it rejects, at some written place at which that
                    list is a written one and long enough
  `maskShapeTie` the test: the written list of the chain's shapes has, at the written plan's number
                    of the link's fresh mask, the shape of the sending's last message
  `maskShapeTieW` BY THE KERNEL: it accepts at every such place, and the sending is not empty there
  `maskShapeTieW_can_fail` at the number in front it rejects at every such place; the list holds a
                    shape there
  `first_shapes_at_head` `AtMg` · the opening · p₀ ∈ `switchPlaces Zp Bs.G₀` · p₀.link < 25 · n <
                    size - 1 ⊢ ∃ i, `(membersOf (loAt p₀.link))[n]? = some i` and `((loAt
                    p₀.link).get i).1` is the shape of message n
  `mask_shape_at_head` the like ⊢ `(msgsOfChain Zp.made.proof.1)[maskNo (At.seats Zp) (At.pseats Zp)
                    p₀.link]?` is the shape of message size - 1
  `place_codes_at_front` p₀, p places, p₀.link < p.link, `FrontTies Zp fx` ⊢ `p₀.sizes.codes =
                    fx.st.codes`

By: `places_at_head` (Honest/K2/Law/PlacesWritten.lean), `fencesW`, `switchTies_at_head`
(Honest/K2/Law/TiesWritten.lean), `segmentsOf_at_front` (Honest/K2/Law/SegmentsAtFront.lean) · the
library's `AtMg.maskNo_is` (Johnson/P5J/MaskLettersAtMg.lean), `sends_in_scope`
(Johnson/Goal/Numbers/MadeInScope.lean), `pins_of_laid` (Johnson/Goal/Skeleton/PinsOfLaid.lean),
`MW_eq` (Johnson/Top/H0/K2Hands/FrontsFull.lean). THE SEALED NAMES `membersOf`, `maskNo`,
`seatsPlanW`, `MList` ARE WRITTEN WHOLE: `membersOf` has a namesake in `ProofFile.Honest`, which encloses
this namespace and wins over an `open`. NEAR, NOT CALLED: `segMembers_written`
(Honest/K2/Law/MembersWritten.lean): a written segment's members against the written list, shapes
and flags · `shapes_written`, `shape_fact_laid` (Johnson/LPFE1R/ShapeAtNoFull.lean): the chain's
shapes at the listed messages' numbers · `seat_at_head` (Honest/K2/Law/SeatIsK10.lean, which this
library may not hold): at the same n and member: the seat, not the shape.

Limits. Closed facts by Lean's kernel, replayed by no independent checker. The tests are on written
data: the full size and the format's second hash function alone, under the head. Nothing on a message's seat
or number in a witness. Nothing on the later sendings of a segment, nor on the first segment. No
coin, no input, no witness, no text of a side. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.TiesWritten
import Johnson.Desc.ProofFile.Honest.K2.Law.SegmentsAtFront
import Johnson.LPFE1R.RowPubAt
import Johnson.Desc.First.Close.Law.Drawn.Def
import Johnson.LPFE1R.ShapeAtNoFull
import Johnson.P5J.MaskLettersAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.LinkJoin (loAt)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- **The test**, on public data: the shapes of a switch's sending, but for its last message (the
fold's fresh mask), are the shapes of the first members of its link's written list, in order. -/
def firstShapesTie (p₀ : SwitchPlace) : Bool :=
  ((switchSent p₀.sizes p₀.others).toList.take ((switchSent p₀.sizes p₀.others).size - 1)).map
      (·.shape) ==
    ((VerifiableInference.Desc.First.Close.membersOf (loAt p₀.link)).take
      ((switchSent p₀.sizes p₀.others).size - 1)).map fun i =>
      ((loAt p₀.link).get i).1

/-- What its yes gives, message by message. -/
theorem firstShapesTie_gives {p₀ : SwitchPlace} (h : firstShapesTie p₀ = true) {n : Nat}
    (hn : n < (switchSent p₀.sizes p₀.others).size - 1) :
    ∃ i, (VerifiableInference.Desc.First.Close.membersOf (loAt p₀.link))[n]? = some i ∧
      ((loAt p₀.link).get i).1 = ((switchSent p₀.sizes p₀.others).getD n default).shape := by
  have e := congrArg (fun l => l[n]?) (eq_of_beq h)
  simp only [List.getElem?_map, List.getElem?_take_of_lt hn, Array.getElem?_toList] at e
  have hs : (switchSent p₀.sizes p₀.others)[n]? =
      some ((switchSent p₀.sizes p₀.others).getD n default) := by
    have hlt : n < (switchSent p₀.sizes p₀.others).size := by omega
    rw [Array.getElem?_eq_getElem hlt, Array.getD, dif_pos hlt]
    rfl
  rw [hs, Option.map_some] at e
  obtain ⟨i, hi, ei⟩ := Option.map_eq_some_iff.1 e.symm
  exact ⟨i, hi, ei⟩

set_option maxRecDepth 1000000 in
/-- **It accepts at every written place that leads into a written segment.** By Lean's kernel. -/
theorem firstShapesTieW :
    (placesW.all fun p₀ => decide (segsW.length ≤ p₀.link) || firstShapesTie p₀) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **It can fail**: at the next link's list it rejects, at some written place at which that list
is a written one and has as many members as the test compares: so shapes are held against shapes. -/
theorem firstShapesTieW_can_fail :
    (placesW.any fun p₀ => decide (p₀.link + 1 < segsW.length) &&
      decide ((switchSent p₀.sizes p₀.others).size - 1 ≤
        (VerifiableInference.Desc.First.Close.membersOf (loAt (p₀.link + 1))).length) &&
      !firstShapesTie { p₀ with link := p₀.link + 1 }) = true := by
  decide +kernel

/-- **The test on the fresh mask**, on public data: the written list of the chain's messages' shapes
has, at the written plan's number of the link's fresh mask, the shape of the sending's last
message. -/
def maskShapeTie (p₀ : SwitchPlace) : Bool :=
  VerifiableInference.Desc.First.K2Hands.MList[VerifiableInference.Desc.First.Close.maskNo
      VerifiableInference.Desc.First.Close.seatsPlanW P5T.psFull p₀.link]? ==
    (switchSent p₀.sizes p₀.others).back?.map (·.shape)

set_option maxRecDepth 1000000 in
/-- **It accepts at every written place that leads into a written segment**, and the sending has a
last message there. By Lean's kernel. -/
theorem maskShapeTieW :
    (placesW.all fun p₀ => decide (segsW.length ≤ p₀.link) ||
      (maskShapeTie p₀ && !(switchSent p₀.sizes p₀.others).isEmpty)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **It can fail**: at the number in front it rejects, at every such place: there the list holds a
shape (the number is below the list's length), and it is another. -/
theorem maskShapeTieW_can_fail :
    (placesW.all fun p₀ => decide (segsW.length ≤ p₀.link) ||
      ((VerifiableInference.Desc.First.K2Hands.MList[VerifiableInference.Desc.First.Close.maskNo
          VerifiableInference.Desc.First.Close.seatsPlanW P5T.psFull p₀.link - 1]?).isSome &&
        !(VerifiableInference.Desc.First.K2Hands.MList[VerifiableInference.Desc.First.Close.maskNo
            VerifiableInference.Desc.First.Close.seatsPlanW P5T.psFull p₀.link - 1]? ==
          (switchSent p₀.sizes p₀.others).back?.map (·.shape)))) = true := by
  decide +kernel

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- **UNDER THE HEAD**: message n of a switch's sending, in front of the fresh mask, has the shape
of the n-th member of its link's written list. -/
theorem first_shapes_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {p₀ : SwitchPlace} (hp₀ : p₀ ∈ switchPlaces Zp Bs.G₀) (hl : p₀.link < 25) {n : Nat}
    (hn : n < (switchSent p₀.sizes p₀.others).size - 1) :
    ∃ i, (VerifiableInference.Desc.First.Close.membersOf (loAt p₀.link))[n]? = some i ∧
      ((loAt p₀.link).get i).1 = ((switchSent p₀.sizes p₀.others).getD n default).shape := by
  rw [places_at_head h O] at hp₀
  have k := List.all_eq_true.1 firstShapesTieW p₀ hp₀
  rw [Bool.or_eq_true, decide_eq_true_eq, fencesW.2.1] at k
  exact firstShapesTie_gives (k.resolve_left (by omega)) hn

/-- **UNDER THE HEAD**: the chain's list of messages' shapes has, at the plan's own number of the
link's fresh mask, the shape of the last message of the switch's sending. -/
theorem mask_shape_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {p₀ : SwitchPlace} (hp₀ : p₀ ∈ switchPlaces Zp Bs.G₀) (hl : p₀.link < 25) :
    (VerifiableInference.Desc.K12.Door.msgsOfChain Zp.made.proof.1)[
        VerifiableInference.Desc.First.Close.maskNo
        (P5J.At.seats Zp) (P5J.At.pseats Zp) p₀.link]? =
      some ((switchSent p₀.sizes p₀.others).getD ((switchSent p₀.sizes p₀.others).size - 1)
        default).shape := by
  rw [places_at_head h O] at hp₀
  have k := List.all_eq_true.1 maskShapeTieW p₀ hp₀
  rw [Bool.or_eq_true, decide_eq_true_eq, fencesW.2.1, Bool.and_eq_true] at k
  obtain ⟨k1, k2⟩ := k.resolve_left (by omega)
  have e3 : VerifiableInference.Desc.K12.Door.msgsOfChain Zp.made.proof.1 =
      VerifiableInference.Desc.First.K2Hands.MList := by
    rw [VerifiableInference.PlanWritten.Joined.sends_in_scope h.scope h.laid.pub
      (P5J.pins_of_laid h.scope h.laid).1]
    exact VerifiableInference.Desc.First.K2Hands.MW_eq
  have hne : 0 < (switchSent p₀.sizes p₀.others).size := by
    rcases Nat.eq_zero_or_pos (switchSent p₀.sizes p₀.others).size with e | e
    · rw [Array.isEmpty_iff_size_eq_zero.2 e] at k2
      cases k2
    · exact e
  rw [e3, h.maskNo_is p₀.link, eq_of_beq k1, Array.back?, Array.getElem?_eq_getElem (by omega),
    Option.map_some, Array.getD, dif_pos (by omega)]
  rfl

/-- **UNDER THE HEAD**: a sender's codes are those of a later switch's front's statement. -/
theorem place_codes_at_front (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {p₀ p : SwitchPlace} (hp₀ : p₀ ∈ switchPlaces Zp Bs.G₀) (hp : p ∈ switchPlaces Zp Bs.G₀)
    (hl : p₀.link < p.link) {fx : _root_.Tw.K2.Front}
    (T : VerifiableInference.Desc.K2.Honest.Returns.FrontTies Zp fx) :
    p₀.sizes.codes = fx.st.codes := by
  obtain ⟨⟨Sg, rest, hSg, -, e, -, -⟩, -, -⟩ := switchTies_at_head h O hp₀ hp hl
  rw [← e]
  exact (segmentsOf_at_front O T (List.mem_of_getElem? hSg)).1

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.firstShapesTie
#print axioms ProofFile.Honest.K2.Law.firstShapesTie_gives
#print axioms ProofFile.Honest.K2.Law.firstShapesTieW
#print axioms ProofFile.Honest.K2.Law.firstShapesTieW_can_fail
#print axioms ProofFile.Honest.K2.Law.first_shapes_at_head
#print axioms ProofFile.Honest.K2.Law.maskShapeTie
#print axioms ProofFile.Honest.K2.Law.maskShapeTieW
#print axioms ProofFile.Honest.K2.Law.maskShapeTieW_can_fail
#print axioms ProofFile.Honest.K2.Law.mask_shape_at_head
#print axioms ProofFile.Honest.K2.Law.place_codes_at_front
