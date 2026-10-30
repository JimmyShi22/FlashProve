-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/HalfNoStray.lean: NO HALF THAT THE HONEST SIDE OF THE LOT "the
output head's own rounds (K6)" LAYS STRAYS. The lot is `headLot` (Honest/K6/Part.lean). A half is a
`Placed` (Honest/Frame.lean): the prover's side of a sub-protocol, at its place. Five theorems.
THREE ARE CONDITIONAL ON hlast: THE LAST BUILT SEGMENT IS A HEAD's. `hearKinds_head_own` has no
premise; `strays_nil_of_places` has its own premise h and no other.

What is here. `strays` (Honest/Frame.lean) is a test of the frame's: the places of halves at which
a chain has no sub-protocol. `onlineProverFromPublicFiles` (Honest/AtPure.lean) asks it of all lots' halves. This is
K6's share. Its last theorem has FOUR premises. Three are facts that `onlineProverFromPublicFiles` has in hand behind
its first three binds: the public part, the ground and the description are what `ProofFile.pubPlain`,
`ProofFile.blankBy ProofFile.pureRoad.links` and `ProofFile.onlineDescription` return. THE FOURTH IS hlast, WHICH `onlineProverFromPublicFiles`
DOES NOT TEST. None of the hypotheses by which other files fix the public files is taken
(`VerifierAndGoals.InScope` with `VerifierAndGoals.readFiles`, as in Johnson/IMR/Subs.lean; `P5J.AtMgA`,
Johnson/P5J/MgAtAll.lean): the theorems stand at every function in the earlier hash's stead and at
every size at which their premises hold. General in the lot's public test `fits` and in its reader
`wit`.

  `hearKinds_head_own`    the fourth kind in front of a head's segment's batching is K6, first
                          segment or not
  `headLot_member_open`   under hlast, at an opening of the description (`IM.Open`,
                          Johnson/IMR/SeatOpen.lean): a sub-protocol of the chain stands at each
                          half's place
  `strays_nil_of_places`  a law on the frame's test: it is empty where each half's place has a
                          sub-protocol
  `headLot_noStray_open`  **`strays` of the lot's halves is empty**, under hlast, at an opening's
                          chain
  `headLot_noStray_desc`  **the same from the three returns and hlast**, at the description's own
                          first chain

THE PREMISE hlast : (ProofFile.subsOf Z)[G.built.size - 1]? = some .head. The row of sorts is the public
part's; the number is the ground's. The lot lays its half at the last built segment, whatever that
segment's sort is (`P4.k6Hear`, Johnson/Desc/ProofFile/Lot/K6K7.lean); neither that text nor
`headFitsB` asks the sort. hlast is a test with code on the public part and the ground: it can be
evaluated at given files. Under `P5J.AtMgA` at `OnBytes.secondHashFunction` (the full size and the format's
second hash function alone), with hG beside it, hlast follows from two theorems together: `IM.ground_gets`
(Johnson/IMR/PureJoin.lean: 25 segments) and `IM.subs_head` (Johnson/IMR/Subs.lean: the head at
24). That step is typed in Honest/K6/Law/HalfNoStrayHead.lean, which is not in the library. No
theorem here says whether the three conditional statements hold without hlast.

The road. Every half stands at `headPlace (G.built.size - 1) 4` (`headLot_place`,
Honest/K6/LotKind.lean). Where the driver's row has a head's segment at a number, the chain's entry
at that segment's fourth piece is a lot's sub-protocol with nothing joined behind it, laid at the
place of the kind K6 there (`IM.chain_hear_alone`, Johnson/IMR/LaidFirst.lean). That entry is in the
chain's flat list `c.blocksInOrder` (`IM.hear_at_flat`, Johnson/IMR/FlatIx.lean) and has that place
(`IM.alone_place`, Johnson/IMR/SeatForm.lean). That it is the only entry with that place is not
said. Where `onlineDescription` returns, the description can be opened (`IM.seat_open`,
Johnson/IMR/SeatOpen.lean).

Limits.
  * THAT ANY OF `pubPlain`, `blankBy`, `onlineDescription` RETURNS is not proved here.
  * THAT THE LOT LAYS A HALF is not proved here: all of it holds also where the lot lays nothing.
  * It is one lot's share: the step from the lots' shares to the one list of all lots' halves that
    `onlineProverFromPublicFiles` tests is not made here.
  * The ground is the one that is made of the public part (hG): at a free ground nothing is said.
  * `strays_nil_of_places` is a small law on the frame's own test. IT IS A SECOND TEXT OF A THEOREM
    THAT WAS WRITTEN FOR ANOTHER SUB-PROTOCOL: statement and proof are those of
    `strays_nil_of_member` in Honest/K4/Law/LotNoStrayOpen.lean (the feed-forward layers'
    sub-protocol, K4), under another name; the docstring is worded anew. It is a theorem, no
    definition: the two have one statement, so no law is wanted to tie them. Why that file is not
    imported: it stands over the other sub-protocol's own part. The road of this whole file
    follows that file's.
  * A law, no part: its imports reach modules under Johnson/Goal/ (Johnson/IMR/K6Seat.lean imports
    two).
  * Nothing on what the half sends. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.LotKind
import Johnson.IMR.K6Seat
import Johnson.IMR.FlatIx

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Place Chain Block FileDescription KindName)
open VerifiableInference.Desc.First (S kindsBeforeBatching)

variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat} {W₀ Rc Tr X' : Type}

/-- The fourth kind in front of a head's segment's batching is K6. f: whether the segment is the
chain's first. -/
theorem hearKinds_head_own (f : Bool) : (kindsBeforeBatching .head f)[3]? = some KindName.K6 := by
  cases f <;> rfl

/-- CONDITIONAL: on O and hlast. A sub-protocol of the chain stands at each half's place. -/
theorem headLot_member_open (O : IM.Open o pol lay KL F Z Bs base c A B)
    (hlast : (ProofFile.subsOf Z)[Bs.G₀.built.size - 1]? = some .head) (fits : Pub → Ground → Bool)
    (wit : Pub → Ground → Local W₀ Rc Inst Tr → HeadAsk) :
    ∀ z ∈ (headLot (X := X') fits wit).halves Z Bs.G₀, ∃ b ∈ c.blocksInOrder, b.place = z.place := by
  intro z hz
  obtain ⟨Lk, b, e1, e2, _, -, _, -, _, -, -, -, hla⟩ :=
    IM.chain_hear_alone O.made O.places O.chain (Bs.G₀.built.size - 1) .head hlast 3 .K6
      (hearKinds_head_own _) (by decide) (by decide) (by decide)
  exact ⟨b, List.mem_of_getElem? (IM.hear_at_flat e1 e2),
    (IM.alone_place hla).trans (headLot_place fits wit Z Bs.G₀ z hz).symm⟩

/-- A law on the frame's test: it is empty where each half's place has a sub-protocol among bs. -/
theorem strays_nil_of_places {σ C V W X : Type} {bs : List (Block σ C)} {hs : List (Placed V W X)}
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

/-- CONDITIONAL: on O and hlast. **NO HALF OF THE LOT STRAYS**, at an opening's chain. -/
theorem headLot_noStray_open (O : IM.Open o pol lay KL F Z Bs base c A B)
    (hlast : (ProofFile.subsOf Z)[Bs.G₀.built.size - 1]? = some .head) (fits : Pub → Ground → Bool)
    (wit : Pub → Ground → Local W₀ Rc Inst Tr → HeadAsk) :
    strays c.blocksInOrder ((headLot (X := X') fits wit).halves Z Bs.G₀) = [] :=
  strays_nil_of_places (headLot_member_open O hlast fits wit)

/-- CONDITIONAL: on the three returns and hlast. **NO HALF OF THE LOT STRAYS, AT THE DESCRIPTION's
OWN FIRST CHAIN.** -/
theorem headLot_noStray_desc {G : Ground} (hZ : ProofFile.pubPlain o pol lay KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) (hF : ProofFile.onlineDescription o pol lay KL = .ok F)
    (hlast : (ProofFile.subsOf Z)[G.built.size - 1]? = some .head) (fits : Pub → Ground → Bool)
    (wit : Pub → Ground → Local W₀ Rc Inst Tr → HeadAsk) :
    strays F.first.blocksInOrder ((headLot (X := X') fits wit).halves Z G) = [] := by
  obtain ⟨Z', Bs', base', c', A', B', O⟩ := IM.seat_open hF
  obtain rfl : Z' = Z := Except.ok.inj (O.pub.symm.trans hZ)
  obtain rfl : Bs'.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  have e := headLot_noStray_open (X' := X') O hlast fits wit
  rw [O.desc]
  exact e

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.hearKinds_head_own
#print axioms ProofFile.Honest.K6.headLot_member_open
#print axioms ProofFile.Honest.K6.strays_nil_of_places
#print axioms ProofFile.Honest.K6.headLot_noStray_open
#print axioms ProofFile.Honest.K6.headLot_noStray_desc
