-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/SeatedM4.lean: kind K13 at the place "M:4" (W's sending): ALL THAT
THE KIND's STATEMENTS THERE ASK OF THE FIRST CHAIN's THREAD, GATHERED IN ONE STRUCTURE
(`K13SeatedM4`), and what follows from it: the share of `Exchange` (Honest/Thread/Pays.lean) at
three of the four items that the member's forward row owes: "wrow", "pileOne", "pinW"; and
`Exchange` itself, from the share at the fourth, "pinV". The words thread, border, item and forward
row are explained in the head of Honest/Thread/Thr.lean; member in that of Honest/Thread/Pays.lean.

In which parameters it is general. The thread is `L.thread`, with L : `FirstThread.Letters`
(Honest/Thread/First.lean) A VARIABLE: every field of L is free, `L.valid` among them, but that the
messages' type is the library's `MsgT`, through which the library's reader of words goes, and the
type of claims the proof file's own (`ProofFile.Cl`), as `IM.Open` has it. The statements name items
(`Item.wrow`, `Item.pileOne`, `Item.pinW`, `Item.pinV`), and the type of a thread's items is itself
a field of a thread: so L, not the thread, is the variable. Every fact on L's fields that a proof
uses is a field of `K13SeatedM4`. Further parameters: Z, the proof file's public data; c, the first
chain of its IOP; arr, the reader's numbers of the messages; mat, the matrix off the witness's
cells; asked, what an instance asks about.

The fields, and what each needs.
  iop: on no field of L: the IOP of three public files is opened as `IM.Open` has it, with the first
    chain c and the public data Z.
  flat, member: on L.bs: it is c's flat list; its number b stands at "M:4". (By these and iop the
    member's accepted step is an accepted step of the lot's sub-protocol: W's commitment with the
    kind's `rowsB` behind it.)
  place, opened: on the written lists (L.ps, L.links): the place "M:4" has the number b; "pileOne"
    is open in front of it. Evaluations at written lists.
  wrow, pileOne: on L.Mg: the two items are the library's sentences `WRow` and `RowsTrue`, at the
    words and the reader through the book of commitment trees, at arr and mat.
  pinW: on L.mg, L.N and L.Q.wit: the item "pinW" holds of the thread's witness at every state: so
    it is where the decoder of the committed table is the constant "the cells that the thread's
    witness has".
  ridesReply: AN IMPLICATION FROM L.rides AT b: it gives that the reply that the state holds is the
    one that the input's instance asks about (`ReplyIs`, FromThread.lean). IT SPEAKS OF ONE VALUE
    THAT IS SENT IN THE CLEAR. It is met by unfolding where that sentence is laid among the clauses
    of L.rides.
  pub: on the thread's sentence at the border b: it gives seven sentences on the verifier's public
    state (`PublicAtM4`, ExchangeM4.lean). No coin and no sent value is in them. They need: the
    decision of the members' batching in front (the claim; the room); facts on reached states (the
    rows' masks, and that these lie within their table); the public form (the message of index masks
    is there; the book of trees is in step).
  witness: on L.Q.msg, L.Q.cells, arr and mat: `WitnessHasW` (ExchangeM4.lean): where the reply
    heard is the one asked, the Script's message for W holds, in the main table, at the places of
    the vector's entries below 2^kCol, the claim's row weights times the matrix. THE HEAVY ONE. It
    needs: that the claim's row weights, which are read off the verifier's state in front, are a
    function of the instance, the challenges heard and the reply, over every member in front that
    lays a row; W's place in the book of trees behind, and arr at it; that these places lie on real
    rows, off the pad. Nothing is asked of a pad's place, a row's tail, a free entry or a mask row.
WHICH ITEM USES WHICH FIELDS. "pileOne": iop, flat, member, place, opened, wrow, pileOne (through
  `TiedAtM4`) and pub. "pinW": pinW alone. "wrow": those of "pileOne", ridesReply and witness.
Main names:
  `K13SeatedM4`: **the structure.** `K13SeatedM4.tied`, `K13SeatedM4.reply`: it gives `TiedAtM4` and
    `ReplyRides`.
  `exchangeOf_pinW`: the share at "pinW", from the field `pinW`'s sentence, at every border.
  `k13_seated_m4`: **the share at the three items, from the structure.**
  `k13_seated_m4_exchange`: `Exchange` at the member, from the structure and the share at "pinV".
  `seatedM4_at_letters`: at the library's own parameters (`FirstThread.lettersAt`), b = 356, under
    the hypothesis h under which these are laid: THE FIRST EIGHT OF THE ELEVEN FIELDS HOLD;
    `ridesReply`, `pub` and `witness` stay premises.

What is not claimed. That `K13SeatedM4` holds at any L: at the library's own parameters three fields
are premises, and the hypothesis h is met by nothing here. THE DEBT AT "wrow" IS NOT MET: it is
carried back to the fields `witness`, `ridesReply` and `pub`. The item "pinV". `Plays`, `Behind`,
`Accepted` and `RidesPast` at this member: it is W's sending, whose prover's half is another kind's.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K13.ExchangeM4At

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Slice
open VerifiableInference.Desc (Block Chain FileDescription Strs)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.Sound (MsgT wordsFirst)
open VerifiableInference.Desc.K13 (whereOf)
open VerifiableInference.Desc.K13.Law (WRow RowsTrue rwBook)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X P Cells Tok : Type} {nR : ℕ}

/-- **All that the kind's statements at "M:4" ask of the first chain's thread.** Z: the proof file's
public data. c: the first chain of its IOP. arr: the reader's numbers of the messages. mat: the
matrix off the witness's cells. asked: what an instance asks about. -/
structure K13SeatedM4 (L : FirstThread.Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT) (b : Nat)
    (Z : Pub) (c : Chain S Cl) (arr : ℕ → ℕ → ℕ)
    (mat : Cells → Fin nR → (Fin (whereOf Z).lin.kCol → Bool) → GE) (asked : Xi → E) : Prop where
  iop : ∃ (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription Inst) (Bs : PureBase)
    (base : List (Block S Cl)) (A : SharedSeat) (B : SecondSeat),
    IM.Open o pol lay KL F Z Bs base c A B
  flat : L.bs = c.blocksInOrder
  member : ∀ blk, L.bs[b]? = some blk → blk.place = ⟨1, none, 4, .K1⟩
  place : L.ps[b]? = some ⟨1, none, 4, .K1⟩
  opened : Item.pileOne ∈ L.thread.opened b
  wrow : ∀ w, (L.Mg w).wrow =
    fun a _ v => WRow (whereOf Z) a.2 (wordsFirst arr a.2.st a.2.book v)
  pileOne : ∀ w, (L.Mg w).pileOne = fun a _ v => RowsTrue (rwBook arr mat a) a.2 v
  pinW : ∀ k w a y hd, Item.holds L.N (L.mg w) Item.pinW a y (L.Q.wit k w hd)
  ridesReply : ∀ w s, L.rides b w s → ReplyIs asked w.x s
  pub : ∀ k s m En, Thr L.thread b k s m En → PublicAtM4 (whereOf Z) s
  witness : WitnessHasW L b Z arr mat asked

variable {L : FirstThread.Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT} {b : Nat} {Z : Pub}
  {c : Chain S Cl} {arr : ℕ → ℕ → ℕ}
  {mat : Cells → Fin nR → (Fin (whereOf Z).lin.kCol → Bool) → GE} {asked : Xi → E}

/-- The structure gives `TiedAtM4`. -/
theorem K13SeatedM4.tied (h : K13SeatedM4 L b Z c arr mat asked) : TiedAtM4 L b Z c arr mat :=
  ⟨h.flat, h.member, h.place, h.wrow, h.pileOne, h.opened⟩

/-- The structure gives `ReplyRides`: by the implication from `L.rides` at b. -/
theorem K13SeatedM4.reply (h : K13SeatedM4 L b Z c arr mat asked) : ReplyRides L b asked :=
  replyRides_of_rides L h.ridesReply

/-- The share at the item "pinW", at every border: where that item holds of the thread's witness at
every state. Neither the thread in front nor the member's step is used. -/
theorem exchangeOf_pinW
    (h : ∀ k w a y hd, Item.holds L.N (L.mg w) Item.pinW a y (L.Q.wit k w hd)) (b : Nat) :
    ExchangeOf L.thread b [Item.pinW] := by
  intro blk hb k s m En ds y cols s' _ _ _ ds' i hi
  obtain rfl : i = Item.pinW := List.mem_singleton.1 hi
  exact h k _ _ _ _

/-- **From the structure: behind the member's accepted step the items "wrow", "pileOne" and "pinW"
hold**, at every run's coins and every continuation of the challenges. -/
theorem k13_seated_m4 (h : K13SeatedM4 L b Z c arr mat asked) :
    ExchangeOf L.thread b [Item.wrow, Item.pileOne, Item.pinW] := by
  obtain ⟨o, pol, lay, KL, F, Bs, base, A, B, O⟩ := h.iop
  exact (exchangeOf_append L.thread b [Item.wrow, Item.pileOne] [Item.pinW]).2
    ⟨exchange_at_m4 L b o pol lay KL F Z Bs base c A B arr mat asked O h.tied h.pub h.reply
      h.witness, exchangeOf_pinW h.pinW b⟩

/-- **`Exchange` at the member**, from the structure and the share at "pinV". -/
theorem k13_seated_m4_exchange (h : K13SeatedM4 L b Z c arr mat asked)
    (hV : ExchangeOf L.thread b [Item.pinV]) : Exchange L.thread b := by
  obtain ⟨h1, h2⟩ :=
    (exchangeOf_append L.thread b [Item.wrow, Item.pileOne] [Item.pinW]).1 (k13_seated_m4 h)
  exact exchange_of_m4 h.tied h1 h2 hV

section
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersAt Script WtF)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **At the library's own parameters**, b = 356, under h: the first eight fields hold;
`ridesReply`, `pub` and `witness` stay premises. -/
theorem seatedM4_at_letters (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Tr X : Type}
    (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
    (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (keeps : Nat → TS → TS → Prop)
    (hR : ∀ w s, rides 356 w s → ReplyIs ProofFile.Inst.asked w.x s)
    (hpub : ∀ k s m En,
      Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 356 k s m
        En → PublicAtM4 (whereOf Zp) s)
    (hW : WitnessHasW (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 356 Zp
      h.𝔇.arr h.𝔇.mat13 ProofFile.Inst.asked) :
    K13SeatedM4 (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 356 Zp cF
      h.𝔇.arr h.𝔇.mat13 ProofFile.Inst.asked := by
  have T := tied_at_letters h hs Q stored ans test carryX item n₁ n₂ valid rides keeps
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact ⟨⟨_, _, _, _, _, Bs, base, _, _, O⟩, T.flat, T.place, T.row, T.opened, T.wrow, T.pileOne,
    fun k w a y hd => m3_pinW_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps k w a y
      hd, hR, hpub, hW⟩

end

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.K13SeatedM4.tied
#print axioms ProofFile.Honest.K13.K13SeatedM4.reply
#print axioms ProofFile.Honest.K13.exchangeOf_pinW
#print axioms ProofFile.Honest.K13.k13_seated_m4
#print axioms ProofFile.Honest.K13.k13_seated_m4_exchange
#print axioms ProofFile.Honest.K13.seatedM4_at_letters
