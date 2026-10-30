-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Returns/WordAtFront.lean: UNDER THE HEAD's PREMISE, AT THE FRONT THAT A CODE
SWITCH's BLOCK TAKES OFF A REACHED STATE, AT ALL THREE SORTS OF THE KIND's PLACES: A WITNESS's WORDS
AT A MEMBER OF THE CLOSED GROUP, READ AT THE FRONT's STATEMENT AND THE BOOK THERE (`wordsFirst`,
Johnson/Desc/Sound/WordsAt.lean), ARE THE WITNESS's TABLE AT THE PLAN's SEAT (`Wit.tab`,
Johnson/Desc/Sound/MsgSig.lean). Statements with their proofs; no definition. For every witness v
and every numbering arr of the seats.

  `link_word_front` `AtMgA` · m < 23 · a reached at 14 (m + 1) + 2 · fx the front that the switch's
                    block takes off a's state · i a member of link m's written list · b below the
                    rows of its part ⊢ `wordsFirst arr fx.st a.1.2.book v (noK10 … m i) part (b + j
                    * 2 ^ ceilLog2 rows) = v.tab fx.st.codes ((loAt m).get i).1 (arr seat.1 seat.2)
                    seat.1 seat.2 (part == .mask) b j`, seat := `seatK10 (loAt m) (P5J.At.pseats Zp)
                    m i`
  `head_word_front` the same at the output head's front (339), of link 23's list
  `fin_word_front` the same at the front behind the last segment (353), of link 24's list: fx is
                    taken off t, the state behind the quiet step in front (`finishFrontQ`), and the
                    book is t's

Why. The item "carry" reads a witness's words at a switch's front, at the carried rows' members'
numbers; these are `noK10 … i` (Returns/MembersNumbered.lean).

THE SPLIT IS NOT ENTERED. `Wit.tab` reads, where `padB cs s mask row place`
(Johnson/Desc/SeatAt.lean) says yes, the seat's own component of the witness (`w.pad j t`), and
elsewhere the message's (`w.msg n`), which all copies share. THESE LAWS STOP IN FRONT OF THAT SPLIT:
NONE SAYS WHETHER AN ENTRY IS A DATUM, A COIN OR A PAD. Whoever goes on from here goes by cases on
`padB`.

By: `listed_reached`, `link_member_stated`, `head_member_stated`, `fin_member_stated`
(Returns/SeatReached.lean) · `wordFirst_at_row` (Johnson/Desc/K2/Honest/Carry/WordAt.lean), at the
front's statement · the library's `front_pin_link`, `front_pin_head` (Johnson/IMR/FrontPin.lean),
`front_nums_fin` (Johnson/IMR/FinCount.lean): the front's statement has the state's oracle messages
· `finishFrontQ_book` (Johnson/Top/H0/Tw/K2C/BookKept.lean): the quiet step keeps the book. NEAR,
NOT CALLED: `listed_word` (Returns/SeatReached.lean): the like at the state's own statement ·
`wordsFirst_older` (Johnson/Desc/First/Close/Law/FillRowRides.lean), `words_same`
(Johnson/Top/H0/Walk/FrameFieldsBack.lean): one message's words at two statements and books.

Limits. No run is given at which the head's premise and "reached" hold together: the three laws
could hold of nothing. The front is the one that `First.K2.frontAt` takes at numbers p with the
place's sort; nothing ties p to the plan's own numbers of the place, nor the state to the item's way
in. Nothing on the fresh mask's message. j is not held below a code's length. The full size and the
format's second hash function alone. Nothing on any property.
-/
import Johnson.Desc.K2.Honest.Returns.SeatReached
import Johnson.Top.H0.Tw.K2C.BookKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (noK10 seatK10)
open VerifiableInference.Desc.LinkJoin (loAt)
open VerifiableInference.Desc.Sound (allOf EAll MsgT wordsFirst)
open Johnson.Desc.First.Walk.Tied (reach_raw)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **AT A SEGMENT's FIRST PLACE** (14 (m + 1) + 2, m < 23), AT THE FRONT THAT THE SWITCH's BLOCK
TAKES OFF THE REACHED STATE: a witness's words at a member of the closed group, read at the front's
statement and the state's book, are the witness's table at the plan's seat. -/
theorem link_word_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : Nat} (h23 : m < 23)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (m + 1) + 2) a) {p : First.K2.P2} (hq : p.stands = .link)
    {fx : _root_.Tw.K2.Front} (hfx : First.K2.frontAt p a.1.2 = some fx)
    (i : Fin (loAt m).length)
    (hi : i ∈ VerifiableInference.Desc.First.Close.membersOf (loAt m))
    {Cells Tok : Type} (arr : Nat → Nat → Nat) (v : Wit Cells Tok MsgT) (part : OnBytes.Part)
    {b : Nat} (hb : b < ((loAt m).get i).1.rows part) (j : Nat) :
    wordsFirst arr fx.st a.1.2.book v (noK10 (P5J.At.seats Zp) (loAt m) (P5J.At.pseats Zp) m i)
        part (b + j * 2 ^ ceilLog2 (((loAt m).get i).1.rows part)) =
      v.tab fx.st.codes ((loAt m).get i).1
        (arr (seatK10 (loAt m) (P5J.At.pseats Zp) m i).1
          (seatK10 (loAt m) (P5J.At.pseats Zp) m i).2)
        (seatK10 (loAt m) (P5J.At.pseats Zp) m i).1 (seatK10 (loAt m) (P5J.At.pseats Zp) m i).2
        (part == .mask) b j := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨hu, hst⟩ := link_member_stated h h23 a hr
  obtain ⟨h1, h2⟩ := listed_reached h (by omega) a hr hu (l := m) (by omega) i (hst i hi)
  obtain ⟨-, R', C', f⟩ := (reach_raw (h.toAtMg.rch_is_reach _ a hr)).fold
  obtain ⟨-, a2, -⟩ :=
    Meaning.K2.front_pin_link h.scope h.reads O (l := m + 1) (by omega) (by omega) f hq hfx
  exact wordFirst_at_row arr _ _ v (by rw [a2]; exact h2) h1 part hb j

/-- **At the output head's front** (339): segment 23's members. -/
theorem head_word_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 339 a) {p : First.K2.P2} (hq : p.stands = .head)
    {fx : _root_.Tw.K2.Front} (hfx : First.K2.frontAt p a.1.2 = some fx)
    (i : Fin (loAt 23).length)
    (hi : i ∈ VerifiableInference.Desc.First.Close.membersOf (loAt 23))
    {Cells Tok : Type} (arr : Nat → Nat → Nat) (v : Wit Cells Tok MsgT) (part : OnBytes.Part)
    {b : Nat} (hb : b < ((loAt 23).get i).1.rows part) (j : Nat) :
    wordsFirst arr fx.st a.1.2.book v (noK10 (P5J.At.seats Zp) (loAt 23) (P5J.At.pseats Zp) 23 i)
        part (b + j * 2 ^ ceilLog2 (((loAt 23).get i).1.rows part)) =
      v.tab fx.st.codes ((loAt 23).get i).1
        (arr (seatK10 (loAt 23) (P5J.At.pseats Zp) 23 i).1
          (seatK10 (loAt 23) (P5J.At.pseats Zp) 23 i).2)
        (seatK10 (loAt 23) (P5J.At.pseats Zp) 23 i).1 (seatK10 (loAt 23) (P5J.At.pseats Zp) 23 i).2
        (part == .mask) b j := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨hu, hst⟩ := head_member_stated h a hr
  obtain ⟨h1, h2⟩ := listed_reached h (by omega) a hr hu (l := 23) (by omega) i (hst i hi)
  obtain ⟨-, R', C', f⟩ := (reach_raw (h.toAtMg.rch_is_reach _ a hr)).fold
  obtain ⟨-, a2, -⟩ := Meaning.K2.front_pin_head h.scope h.reads O f hq hfx
  exact wordFirst_at_row arr _ _ v (by rw [a2]; exact h2) h1 part hb j

/-- **At the front behind the last segment** (353, behind its quiet step in front, t): segment 24's
members; the book is t's. -/
theorem fin_word_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 353 a) {t : S} (he : First.K2.finishFrontQ a.1.2 = .ok t)
    {p : First.K2.P2} (hq : p.stands = .finish) {fx : _root_.Tw.K2.Front}
    (hfx : First.K2.frontAt p t = some fx)
    (i : Fin (loAt 24).length)
    (hi : i ∈ VerifiableInference.Desc.First.Close.membersOf (loAt 24))
    {Cells Tok : Type} (arr : Nat → Nat → Nat) (v : Wit Cells Tok MsgT) (part : OnBytes.Part)
    {b : Nat} (hb : b < ((loAt 24).get i).1.rows part) (j : Nat) :
    wordsFirst arr fx.st t.book v (noK10 (P5J.At.seats Zp) (loAt 24) (P5J.At.pseats Zp) 24 i)
        part (b + j * 2 ^ ceilLog2 (((loAt 24).get i).1.rows part)) =
      v.tab fx.st.codes ((loAt 24).get i).1
        (arr (seatK10 (loAt 24) (P5J.At.pseats Zp) 24 i).1
          (seatK10 (loAt 24) (P5J.At.pseats Zp) 24 i).2)
        (seatK10 (loAt 24) (P5J.At.pseats Zp) 24 i).1 (seatK10 (loAt 24) (P5J.At.pseats Zp) 24 i).2
        (part == .mask) b j := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨hu, hst⟩ := fin_member_stated h a hr
  obtain ⟨h1, h2⟩ := listed_reached h (by omega) a hr hu (l := 24) (by omega) i (hst i hi)
  obtain ⟨-, R', C', f⟩ := (reach_raw (h.toAtMg.rch_is_reach _ a hr)).fold
  obtain ⟨-, -, -, a4, -⟩ := Meaning.K2.front_nums_fin h.scope h.reads O f he hq hfx
  exact wordFirst_at_row arr _ _ v (by rw [a4]; exact h2)
    (by rw [(First.K2.finishFrontQ_book he).1]; exact h1) part hb j

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_word_front
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_word_front
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_word_front
