-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AtPureWiderK10.lean: a choice of fields for `onlineProverFromPublicFiles`
(Honest/AtPure.lean) beside `widerFillOwn` (Honest/AtPureWiderAt.lean): its ten lists of prover's
sides and, behind them, an eleventh: the closings of the segments (the kind K10). The eleventh is
their authors' list `K10.seatLotC` (Honest/K10/SeatLotC.lean: the closings alone, no side at a place
of the kind K9) with their authors' filler `K10.stAtZero` (Honest/K10/StAtZero.lean). Three
definitions with code; eleven short lemmas.

  `closeLotAt`      the eleventh list. THE FILLER's TWO LETTERS, BY NAME: bs := cF.blocksInOrder, where the
     library's `ProofFile.onlineFirstChainAt Z` (Johnson/Desc/ProofFile/LinkAt.lean: the proof file's first
     chain, from the public part) returns cF; start := fun ξ => ProofFile.startS Z ξ.pub
  `widerFillOwnC`   `widerFillOwn` with `closeLotAt` behind its ten lists; all other fields its own
  `widerFillAtC`    that at `LongLots.plain` and the own state `Unit`: `widerFillAt`'s sister
  `closeLotAt_name`, `closeLotAt_ok`, `closeLotAt_error`, `closeLotAt_kinds`   the list's name; its
     sides where the chain is made; where it is not; every side is at a place of the kind K10
  `widerFillOwnC_lots`, `widerFillOwnC_old`, `widerFillOwnC_close`, `widerFillOwnC_trace`
     the field `lots` written out; the ten are members; the eleventh is; the field `trace` is
     `widerFillOwn`'s
  `atPure_open`, `closeLotAt_of_open`, `atPure_closings`   WHERE `onlineProverFromPublicFiles` RETURNS, AT ANY CHOICE OF
     FIELDS, THE CHAIN IS MADE, and it is the c of which the returned description is made
     (`IM.Open`, Johnson/IMR/SeatOpen.lean; the library's `ToldDesc.pureChainAt_of_open`,
     Johnson/ToldDescR/PureChainOfOpen.lean): so the silent default below is not met there, and the
     list is its authors' with the filler at c.blocksInOrder

What may be said here on hiding, and no more (a rule of use for whoever builds on this file; no
theorem), on the filler and on this laying: «(Z1) bs := c.blocksInOrder AND start := ProofFile.startS Zp ·.pub BY
NAME IN THE LAYING's TEXT» · «(Z2) closeAtHand … = true BY NAME WHEREVER A LAW SPEAKS OF A CLOSING»
· (Z3), in its later form: «NO COUNT AT ANY OF THE 25 UNTIL, AT THE STANDS OF WHICH THE COUNTED
SENTENCE SPEAKS: (α) the filler returns · (β) closeAtHand … = true at every move · (γ) the data are
made (askZero … = some A): EACH A THEOREM THERE, OR A CONJUNCT OF THE COUNTED SENTENCE; (γ)'s
premises on the record in front and on the prover's rows BY NAME.» · «(Z4) … nobody reads more of it
than (wipeSt ·.st, the live group's number)» · «NEVER "AT EVERY CLOSING" WITHOUT onlineFirstChainAt Z = .ok
cF BY NAME». On hiding this file says nothing of its own.

Limits.
  * NEITHER CHOICE OF FIELDS HERE IS `widerFillAt`. No law that is stated at `widerFillAt` speaks of
    them: each such law's premises are to be paid anew.
  * A SILENT DEFAULT: where `ProofFile.onlineFirstChainAt Z` returns an error `closeLotAt` lays NO side
    (`closeLotAt_error`). Whoever speaks of the closings' sides names `ProofFile.onlineFirstChainAt Z = .ok cF`
    (`closeLotAt_ok`), or `onlineProverFromPublicFiles`'s return (`atPure_closings`).
  * The chain does not read the stand-in for the format's second hash function (the library's
    `ProofFile.Law.chainOfSeat_older`, by `rfl`): so the o of a choice of fields and the o at which
    `onlineProverFromPublicFiles` is called need not be tied for the chain's sake.
  * The list's name says at which sealed lot's places its sides stand; `lotsLacking`
    (Honest/Frame.lean) reads it: that test no longer names the sealed lot of K9 and K10, though
    K9's places have no side. The test by senders (`lacking`) is the one that tells.
  * That no side of the ten stands at a place of the kind K10 is stated in no file that this one
    imports (Honest/AtPureWiderK10Kinds.lean, which imports this one, has it: `ten_not_K10`, under a
    premise on the five lists L, in which `widerFillOwnC` is general; `ten_not_K10_plain`, at the
    lists of `widerFillAtC`, without one). Where a caller's list does lay such a side `ready`
    refuses, aloud (two sides at one place). The eleventh stands last: it can shadow none of the
    ten.
  * TWO MORE DEFAULTS, `widerFillOwn`'s own, unturned: `shared` is the empty list where its maker
    returns an error; `second` is the empty list always, though by its authors' reading the second
    chain has a sub-protocol that sends (Honest/AtPureSharedOk.lean says both by name).
  * AND ONE OF THE CLOSING's PART, which this laying brings in. The part that `K10.seatLotC` lays is
    the total one (`foldShellT true`, Honest/K10/Sim.lean): it never refuses. Where the filler
    returns an error, and where `closeAskAt` or `closeAsk` (Honest/K10/Job.lean) refuses for any
    other cause (seven refusals, by their authors' count), `askOr true` makes nothing of the
    refusal, and the part sends the words at empty tables (`bareAsk`), IN SILENCE.
  * COST: the match stands under `fun Z G`: the chain is made anew wherever the list's sides are
    asked; and the filler folds over the members in front at every call of a closing's part.
  * The readers and the rows' data are what `widerFillOwn` gives the kind K2. That these rows are
    the tables which K2's parts committed at each segment is not said by this laying: a law on what
    a closing sends will have to spend it by name.
  * STILL WITHOUT A SIDE in the first chain: the proximity test (the kind K12) and K1's message "W".
    At the places of the kind K9 no side is laid on purpose: their rounds want none.
  * That `onlineProverFromPublicFiles` returns at these choices of fields, that `ready` does, that a closing's part
    plays or is accepted: none is stated here.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtPureWiderAt
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.Desc.ProofFile.Honest.K10.SeatLotC
import Johnson.Desc.ProofFile.Honest.K10.StAtZero
import Johnson.ToldDescR.PureChainOfOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Chain FileDescription KindName)

variable {W₀ X : Type}

/-! ## 1 The definitions -/

/-- **The closings' list of prover's sides**: `K10.seatLotC` at the readers and the rows' data that
`widerFillOwn` gives the kind K2, with the filler `K10.stAtZero` AT bs := cF.blocksInOrder AND
start := fun ξ => ProofFile.startS Z ξ.pub, cF the library's first chain at Z (`ProofFile.onlineFirstChainAt`).
A SILENT DEFAULT: no side where that chain is not made. The name is `K10.seatLotC`'s own: that of
the sealed lot which lays both K9's batchings and K10's closings (`k9Ninth`). -/
def closeLotAt (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) :
    HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X :=
  { name := (K9.batLot (V := Local W₀ IndexCommitterCoins Inst Cells) (W := Local W₀ IndexCommitterCoins Inst Cells) (X := X)
      fun _ _ => []).name
    halves := fun Z G =>
      match ProofFile.onlineFirstChainAt Z with
      | .ok cF =>
        (K10.seatLotC (fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights Z w.w₀, w.rc⟩)
          (widerRows S Z G) (K10.stAtZero cF.blocksInOrder fun ξ : Inst => ProofFile.startS Z ξ.pub)).halves Z G
      | .error _ => [] }

/-- **`widerFillOwn` with the closings' list behind its ten.** The arguments are
`widerFillOwn`'s. -/
def widerFillOwnC (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) : OnlineProverParts W₀ IndexCommitterCoins Cells Unit X :=
  { widerFillOwn own₀ L I o S O with
    lots := (widerFillOwn own₀ L I o S O).lots ++ [closeLotAt I S] }

/-- **`widerFillAt`'s sister with the closings.** -/
def widerFillAtC (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    OnlineProverParts W₀ IndexCommitterCoins Cells Unit Unit :=
  widerFillOwnC () (LongLots.plain o S O) I o S O

/-! ## 2 The list -/

/-- The list's name is the sealed lot's own. -/
theorem closeLotAt_name (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (Z : Pub) :
    (closeLotAt (X := X) I S).name = (k9Ninth Z).name := rfl

/-- **Where the first chain is made**: the authors' list, the filler's two letters by name. -/
theorem closeLotAt_ok (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) {Z : Pub} (G : Ground)
    {cF : Chain VerifiableInference.Desc.First.S ProofFile.Cl} (h : ProofFile.onlineFirstChainAt Z = .ok cF) :
    (closeLotAt (X := X) I S).halves Z G =
      (K10.seatLotC (fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights Z w.w₀, w.rc⟩)
        (widerRows S Z G)
        (K10.stAtZero cF.blocksInOrder fun ξ : Inst => ProofFile.startS Z ξ.pub)).halves Z G := by
  show (match ProofFile.onlineFirstChainAt Z with
    | .ok cF =>
      (K10.seatLotC (fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights Z w.w₀, w.rc⟩)
        (widerRows S Z G) (K10.stAtZero cF.blocksInOrder fun ξ : Inst => ProofFile.startS Z ξ.pub)).halves Z G
    | .error _ => []) = _
  rw [h]

/-- **Where it is not made**: no side. -/
theorem closeLotAt_error (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) {Z : Pub} (G : Ground)
    {e : String} (h : ProofFile.onlineFirstChainAt Z = .error e) :
    (closeLotAt (X := X) I S).halves Z G = [] := by
  show (match ProofFile.onlineFirstChainAt Z with
    | .ok cF =>
      (K10.seatLotC (fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights Z w.w₀, w.rc⟩)
        (widerRows S Z G) (K10.stAtZero cF.blocksInOrder fun ξ : Inst => ProofFile.startS Z ξ.pub)).halves Z G
    | .error _ => []) = _
  rw [h]

/-- Every side of the list stands at a place of the kind K10. -/
theorem closeLotAt_kinds (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground) :
    ∀ x ∈ (closeLotAt (X := X) I S).halves Z G, x.place.kind = KindName.K10 := by
  intro x hx
  cases h : ProofFile.onlineFirstChainAt Z with
  | ok cF =>
    rw [closeLotAt_ok I S G h] at hx
    exact K10.seatLotC_kinds _ _ _ Z G x hx
  | error e =>
    rw [closeLotAt_error I S G h] at hx
    cases hx

/-! ## 3 The choice of fields -/

/-- The field `lots`, written out. -/
theorem widerFillOwnC_lots (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    (widerFillOwnC own₀ L I o S O).lots =
      (widerFillOwn own₀ L I o S O).lots ++ [closeLotAt I S] := rfl

/-- The ten are members. -/
theorem widerFillOwnC_old (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {M : HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X}
    (h : M ∈ (widerFillOwn own₀ L I o S O).lots) : M ∈ (widerFillOwnC own₀ L I o S O).lots :=
  List.mem_append_left _ h

/-- The eleventh is a member. -/
theorem widerFillOwnC_close (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    closeLotAt I S ∈ (widerFillOwnC own₀ L I o S O).lots :=
  List.mem_append_right _ (.head _)

/-- The field `trace` is `widerFillOwn`'s. -/
theorem widerFillOwnC_trace (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    (widerFillOwnC own₀ L I o S O).trace = (widerFillOwn own₀ L I o S O).trace := rfl

/-! ## 4 Where `onlineProverFromPublicFiles` returns the chain is made -/

/-- **Where `onlineProverFromPublicFiles` returns, the returned description can be opened at the returned public
part.** -/
theorem atPure_open {Rc Tr X₀ : Type} {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : onlineProverFromPublicFiles o pol lay KL P = .ok A) :
    ∃ Bs base c Sh Se, IM.Open o pol lay KL A.F A.Z Bs base c Sh Se := by
  obtain ⟨hZ, -, hF, -⟩ := atPure_ok h
  obtain ⟨Z, Bs, base, c, Sh, Se, O⟩ := IM.seat_open hF
  obtain rfl : Z = A.Z := Except.ok.inj (O.pub.symm.trans hZ)
  exact ⟨Bs, base, c, Sh, Se, O⟩

/-- **The closings' list at the opened description's letters.** -/
theorem closeLotAt_of_open (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (G : Ground)
    {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst} {Z : Pub}
    {Bs : ProofFile.PureBase} {base : List (Block VerifiableInference.Desc.First.S ProofFile.Cl)}
    {c : Chain VerifiableInference.Desc.First.S ProofFile.Cl} {Sh : ProofFile.SharedSeat}
    {Se : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c Sh Se) :
    (closeLotAt (X := X) I S).halves Z G =
      (K10.seatLotC (fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights Z w.w₀, w.rc⟩)
        (widerRows S Z G)
        (K10.stAtZero c.blocksInOrder fun ξ : Inst => ProofFile.startS Z ξ.pub)).halves Z G :=
  closeLotAt_ok I S G (ToldDesc.pureChainAt_of_open O)

/-- **WHERE `onlineProverFromPublicFiles` RETURNS A, AT ANY CHOICE OF FIELDS AND ANY o, THE SILENT ARM IS DEAD**: the
description opens at some c, and at A.Z and A.G the closings' list is its authors', the filler at
c.blocksInOrder. -/
theorem atPure_closings {Rc Tr X₀ Y : Type} (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz)
    {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {P : OnlineProverParts W₀ Rc Tr X₀ Y}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ Y} (h : onlineProverFromPublicFiles o pol lay KL P = .ok A) :
    ∃ Bs base c Sh Se, IM.Open o pol lay KL A.F A.Z Bs base c Sh Se ∧
      (closeLotAt (X := X) I S).halves A.Z A.G =
        (K10.seatLotC
          (fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights A.Z w.w₀, w.rc⟩)
          (widerRows S A.Z A.G)
          (K10.stAtZero c.blocksInOrder fun ξ : Inst => ProofFile.startS A.Z ξ.pub)).halves A.Z A.G := by
  obtain ⟨Bs, base, c, Sh, Se, O⟩ := atPure_open h
  exact ⟨Bs, base, c, Sh, Se, O, closeLotAt_of_open I S A.G O⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.closeLotAt_name
#print axioms ProofFile.Honest.closeLotAt_ok
#print axioms ProofFile.Honest.closeLotAt_error
#print axioms ProofFile.Honest.closeLotAt_kinds
#print axioms ProofFile.Honest.widerFillOwnC_lots
#print axioms ProofFile.Honest.widerFillOwnC_old
#print axioms ProofFile.Honest.widerFillOwnC_close
#print axioms ProofFile.Honest.widerFillOwnC_trace
#print axioms ProofFile.Honest.atPure_open
#print axioms ProofFile.Honest.closeLotAt_of_open
#print axioms ProofFile.Honest.atPure_closings
