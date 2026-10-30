-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/MatAtFold.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: A
PAYMENT BENEATH THE KIND'S FROZEN CONDITION: THE FOUR PLAIN FACTS A MATRIX ON THE STATE (`MatAt`,
SmallAtDraw.lean) OUT OF THE FACTS ALONG "REACHED" (`FoldFacts`), THE PROMISE'S TEST ON THE
BOOK, AND ONE CLOSED SENTENCE ON THE PLAN. NO SOUNDNESS.

  `MatPlan`: THE CLOSED SENTENCE, on public data alone, at one array A born at a link: the plan's
    term for "where is the message" answers o; o is below the number n of messages that are sent by
    then; the shape has the message, and the plan's list of shapes has its shape at o; the plan's
    list of seats has a seat q at o; q is a tenant of the segment's group; q has the plan's number
    of the message.
  `bookAt_of_onQ`: the promise's test on the book, out of the promise.
  `matrixOk_at`: the programs' own test `laidMatrixOk` at the STATEMENT's bits of message o, where
    the statement's shape at o is the shape's message's: `matrixOk_of_layoutOk` (K05LayoutOk.lean).
  `matAt_of_fold`: **`FoldFacts`, the test on the book, "the layout is lawful" and `MatPlan` give
    `MatAt`**: by `whereIs_reached` (PartFitsReached.lean), and `msgShape_at` and
    `seatsCarriedB` (Johnson/Desc/K12/Door/: MsgShapes.lean, DoorBools.lean).
Limits. `MatPlan` and "the layout is lawful" are shown nowhere here; they read no state. Nothing on
soundness.

-/
import Johnson.P1K8R.SmallAtDraw
import Johnson.Desc.First.Link.Law.PartFitsReached
import Johnson.Desc.First.Att.K05LayoutOk

set_option autoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open OnBytes.Params (ReqArray)
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning FoldData FoldFacts momentAt shiftAt
  bookAt flatPlacesOf)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.LinkJoin (whereD whereIs_reached)
open VerifiableInference.Desc.K9 (seatAt)
open ProofFile (Cl)

/-- **THE CLOSED SENTENCE ON THE PLAN**, at one array A born at link born, in segment l with t
moments sent and n messages sent. -/
def MatPlan (d : FoldData) (own : List (ℕ × ℕ)) (arr num : ℕ → ℕ → ℕ) (l t n born : ℕ)
    (A : ReqArray) : Prop :=
  ∃ (o : ℕ) (q : ℕ × ℕ) (msg : OnBytes.Params.ReqMessage), whereD d l t born A.message = some o ∧
    o < n ∧ _root_.Meaning.messageAt d.sent.shape born A.message = some msg ∧
    d.M[o]? = some msg.shape ∧ d.L.places[o]? = some q ∧ q ∈ own ∧
    arr q.1 q.2 = num born A.message

/-- The promise's test on the book, out of the promise. -/
theorem bookAt_of_onQ {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (ps : List Place) (get : A → P × S) (k : ℕ) (a : A × Fr.E.Str)
    (h : onQ N Mg links ps get k a) (hm : (get a.1).2.failed = none) :
    bookAt N ps[k]? (get a.1).2 = true := by
  rcases h.2 with h' | h'
  · exact absurd hm h'
  · exact (Bool.and_eq_true_iff.1 h'.1).2

/-- **`laidMatrixOk` at the statement's own bits.** -/
theorem matrixOk_at {st : Statement} {shape : OnBytes.Params.ReqShape}
    {layout : OnBytes.Params.ReqLayout} (hlo : reqLayoutOk st.codes shape layout = true) {born : ℕ}
    {name : String} {A : ReqArray} (hA : OnBytes.reqArray layout born name = some A) {o : ℕ}
    {x : Oracle} (hx : st.oracles[o]? = some x) {msg : OnBytes.Params.ReqMessage}
    (hmsg : _root_.Meaning.messageAt shape born A.message = some msg) (hs : x.shape = msg.shape) :
    laidMatrixOk A (st.rowBits o .main) (st.placeBits o .main) = true := by
  obtain ⟨Lk, msg', c, h1, h2, h3, h4, h5, -⟩ :=
    VerifiableInference.Desc.First.Att.P.matrixOk_of_layoutOk _ _ _ hlo born name A hA
  obtain rfl : msg' = msg := by
    unfold _root_.Meaning.messageAt at hmsg
    rw [h1] at hmsg
    exact Option.some.inj (h2.symm.trans hmsg)
  have eR : st.rowBits o .main = ceilLog2 msg'.shape.mainRows := by
    unfold Statement.rowBits
    rw [hx]
    show ceilLog2 (x.shape.rows .main) = _
    rw [hs]
    rfl
  have eP : st.placeBits o .main = c.logEll := by
    unfold Statement.placeBits
    rw [hx]
    show (if (x.shape.rows .main == 0) = true then 0
      else (st.codes.base.getD x.shape.code default).logEll) = _
    rw [hs]
    show (if (msg'.shape.mainRows == 0) = true then 0
      else (st.codes.base.getD msg'.shape.code default).logEll) = _
    rw [if_neg (by simpa using h4), Array.getD_eq_getD_getElem?, h3]
    rfl
  rw [eR, eP]
  exact h5

/-- **THE FOUR PLAIN FACTS, OUT OF THE FACTS ALONG "REACHED".** -/
theorem matAt_of_fold {Zp : ProofFile.Pub} {cF : Chain S Cl} {X P : Type} {Rch : ℕ → X → Prop}
    {at_ : X → P × S} {d : FoldData} {reqW : P → Array UInt32} {links : List ModelPart} {ps : List Place}
    (FF : FoldFacts Rch at_ d reqW links ps) {k : ℕ} {a : X} {p : Place} {l : ℕ} {L : LinkCtx}
    (hR : Rch k a) (hu : (at_ a).2.failed = none) (hp : ps[k]? = some p) (hlk : p.link = some l)
    (hpc : p.piece ≤ 11 + 2 * shiftAt links l) (hL : (at_ a).2.link? = some L)
    (hB : bookAt (P5J.At.N Zp cF) ps[k]? (at_ a).2 = true)
    (hlo : reqLayoutOk d.sent.codes d.sent.shape d.sent.layout = true) {born : ℕ} {name : String}
    {A : ReqArray} (hA : OnBytes.reqArray d.sent.layout born name = some A)
    (T : MatPlan d ((P5J.At.N Zp cF).group l) (P5J.At.arr Zp) (P5J.At.num Zp) l
      (momentAt (shiftAt links l) p.piece) ((P5J.At.N Zp cF).msgsAt ps[k]?) born A) :
    MatAt Zp cF l (at_ a).2 L born A := by
  obtain ⟨o, q, msg, hw, hon, hmsg, hM, hpl, hqo, hn⟩ := T
  unfold bookAt at hB
  simp only [Bool.and_eq_true, beq_iff_eq] at hB
  obtain ⟨⟨-, hb2⟩, hb3⟩ := hB
  have hoS : o < (at_ a).2.st.oracles.size := by rw [hb3]; exact hon
  have e := VerifiableInference.Desc.K12.Door.msgShape_at (FF.msgShapes k a hR hu) o hoS
  rw [hM] at e
  obtain ⟨x, hx, hxs⟩ := Option.map_eq_some_iff.1 e
  refine ⟨o, q, (whereIs_reached FF hR hu hp hlk hpc hL born A.message).trans hw, ?_, ?_, hn⟩
  · exact matrixOk_at (by rw [FF.codes k a hR hu]; exact hlo) hA hx hmsg hxs
  · have hS := FF.seatsCarried k a hR hu
    unfold VerifiableInference.Desc.K12.Door.atFirstSeats
      VerifiableInference.Desc.K12.Door.seatsCarriedB at hS
    simp only [Bool.and_eq_true, beq_iff_eq] at hS
    have e0 : (at_ a).2.book.place.toList = d.L.places.take (at_ a).2.book.place.size := hS.1.1.1
    have h3 : (at_ a).2.book.place[o]? = some q := by
      rw [← Array.getElem?_toList, e0, List.getElem?_take_of_lt (by rw [hb2]; exact hoS)]
      exact hpl
    unfold seatAt
    rw [h3]
    show (if ((P5J.At.N Zp cF).group l).contains q = true then some q else none) = some q
    rw [if_pos (List.contains_iff_mem.2 hqo)]

end P1K8T

#print axioms P1K8T.bookAt_of_onQ
#print axioms P1K8T.matrixOk_at
#print axioms P1K8T.matAt_of_fold
