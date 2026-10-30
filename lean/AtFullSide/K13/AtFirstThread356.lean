-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K13/AtFirstThread356.lean: kind K13 (the members' batching): at the first chain's thread
as it is written (`firstLetters`, `firstThread`, Honest/Thread/TheFirstThread.lean): the kind's tie
`MatTie` (Honest/K13/ExchangeAtM3.lean), which its statements at numbers 355 and 356 take as the
premise hM; and the kind's two shares of the exchange at number 356, the member at which the prover
sends the vector W. Statements with their proofs: calls; no definition. The full size and the
format's second hash function alone.

The parameters. A: a value of `OnlineProverWithDescription`; from `k13_items_at_356_at_firstThread` on, what the maker
`onlineProverFromPublicFiles` returns at the wide filling `onlineProverPartsInUse I o S O` (Honest/K1/Law/WSideAtFill.lean),
with I, which says what depends on the type of the index, a variable. hd: the head at A
(`HeadAtReturn`: the library's hypothesis at the full size, at A's public part). parts: what the
first thread takes from outside: the Script and the falls' stated numbers. w: the run's input. Said:
a variable.

Main names.
  `k13_matTie_at_firstLetters`: **`MatTie` at the first thread's parameters**, at every reader
    `weights` of the index, from hc.
  `k13_cells_of_record`: where the Script is the join of a senders' record, its cells are the
    record's.
  `k13_items_at_356_at_firstThread`: the shares at "pileOne" and "wrow" at 356, from R and hc, at
    every Said.
  `k13_exchangeS_at_356_at_firstThread`: the whole debt `ExchangeS` at 356, from R, hc and the share
    at "pinV".
  `k13_items_at_356_of_script`: the two shares with R replaced by hO, msgs and pads.

The premises. hc: the Script's cells at the run's input are the library's matrix of cells
(`Bind.ForProver.cellsOfF`, Johnson/Bind/ForProver/CellsInField.lean) of the entries that the reader
reads off the input's index. IT IS NOT SHOWN HERE: `parts.script` is a variable. Where the Script is
defined as a join whose cells are that matrix, hc holds by unfolding; where the Script is the join
of a senders' record, hc is a sentence on the record's field `cells` (`k13_cells_of_record`). R:
kind K1's record `K1Seated` (Honest/K1/Seated.lean) at number 356, at the filling's own reader of
the input and at W's job with the data `wDataAt pileAnyK3 A.Z A.G`. IT IS NOT SHOWN HERE. hO: the
filling's filler of the pile is `pileAnyK3`. msgs, pads: R's two fields on the Script: its messages
and pads at W's seat are the texts of W's job. msgs AND pads ARE NOT SHOWN HERE. R's other eighteen
fields follow at this filling (`K1.k1Seated_w_at_book`, Honest/K1/Law/RecordAtBookFill.lean, at
`hex_wM` and `ho_wM`).

What hc does and does not give. Under hc `MatTie` is true by construction: it compares the Script's
cells with the reader's entries, and hc defines the one from the other (`k13_matTie_of_cellsOfF`,
Honest/K13/MatTieOfReaderCells.lean). So no premise here asks anything of the run's input or its
index; the statements on shares still speak only of inputs that the thread admits (`ReadyInput`,
Honest/Thread/ReadyInput.lean). Two things are not shown by this. First, that this matrix of cells
is in range (`Flat.InRange`: it holds a well-formed index). Other kinds' statements at the same
parameters take that as a premise (hH, Honest/K5/Law/AllJoined.lean). It does not follow from
`ReadyInput` while I is a variable: I's test of the range and I's reader are two fields that nothing
ties. Second,
that these cells are what the stored table decodes to. In the first chain's thread no item says so:
the decoder there is the constant "the Script's cells". At an input whose matrix of cells is
out of range `MatTie` still holds, and nothing shows that the thread's invariant holds at any run
there.

Limits. Where the thread's invariant holds at no run, or the member's step is never accepted, the
statements on shares hold vacuously. That a head stands at any return, and that the maker returns,
is not shown here. Of the five debts at number 356 only `ExchangeS` is spoken of. The limits of
WitnessHasWAt356.lean of this folder hold here too: in particular these statements are not to stand
in front of a law over coins.

What is not claimed. None of these is one of the library's goals. Nothing on soundness, completeness
or hiding.
-/
import AtFullSide.K13.WitnessHasWAt356
import Johnson.Desc.ProofFile.Honest.K13.MatTieOfReaderCells
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K13
open OnBytes
open ProofFile.Honest ProofFile.Honest.K13
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open VerifiableInference.Desc.Sound (MsgT Mem)
open VerifiableInference.OnPublicFiles (numsRef)
open OnBytes.Slice (frS frZ)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead OwnMsgs OwnPads HeadAtReturn FirstThreadParts
  SendersRecord firstLetters firstThread)
open ProofFile.Honest.K1 (K1Seated PlaceIn SendJob lotNo wJobAt wGp seatAtMember msgTxt padTxt)

section
variable {W₀ Rc Tr X₀ X' : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
  (hd : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- hc is a premise that is not shown here. **`MatTie` at the first thread's parameters**, at every
reader of the index. hc: the Script's cells at the run's input are the library's matrix of cells of
the entries that the reader reads off the input's index. pl: a pile's filler, which neither matrix
reads. -/
theorem k13_matTie_at_firstLetters {weights : W₀ → Weights} {pl : PileOf ProofFile.Inst}
    (hc : parts.script.cells w =
      Bind.ForProver.cellsOfF frS frZ 402653181 numsRef (weights w.w₀).entry) :
    MatTie (firstLetters hd parts w) weights pl hd.head.𝔇.P13 (k13ReaderAt hd.head) :=
  k13_matTie_of_cellsOfF hd.head A.H parts.script _ _ _ _ _ _ _ _ _ w hc

/-- Where the Script is the join of a senders' record, its cells are the record's. -/
theorem k13_cells_of_record {Xj : Type} (r : SendersRecord A Xj)
    (hs : parts.script = SendersRecord.script hd r) : parts.script.cells w = r.cells w := by
  rw [hs]
  rfl

end

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument)
  (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL (onlineProverPartsInUse I o S O) = .ok A)
  (hd : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
  {first : ℕ} {blk₆ : Block TS ProofFile.Cl} {own₀ : Unit} {seats₀ : List (ℕ × ℕ)} {ms : List Mem}
  {rad : ℕ → ℕ}
include hA

/-- R and hc are premises that are not shown here. **The kind's two shares of the exchange at number
356, at the first thread as it is written, at the wide filling, at every Said.** R: kind K1's record
at number 356, at the filling's own reader of the input and W's job. hc: the Script's cells at the
run's input are the matrix of cells of the filling's reader of the index. -/
theorem k13_items_at_356_at_firstThread
    (R : K1Seated (firstLetters hd parts w) 356 blk₆
      (fun v : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => ⟨v.x, ⟨v.trace, I.weights A.Z v.w₀, v.rc⟩⟩)
      (K1.wJobAt A.Z.first (K1.wGp A.Z) 4 wMsgFull first (wDataAt pileAnyK3 A.Z A.G)) own₀ .w
      (P5J.At.arr A.Z) seats₀ ms rad)
    (hc : parts.script.cells w =
      Bind.ForProver.cellsOfF frS frZ 402653181 numsRef (I.weights A.Z w.w₀).entry)
    (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) :
    ExchangeAtS (firstThread hd parts w) Said 356 Item.pileOne ∧
      ExchangeAtS (firstThread hd parts w) Said 356 Item.wrow :=
  k13_items_at_356_of_maker hd.head hA parts.script _ _ _ _ _ 339 _ _ _ w
    (weights := I.weights A.Z) (pl := pileAnyK3 A.Z A.G) (by omega) R rfl rfl
    (k13_matTie_at_firstLetters hd parts w hc) Said

/-- R, hc and hV are premises that are not shown here. **The whole debt `ExchangeS` at number 356,
at the first thread as it is written**, from the same premises and hV: the share at "pinV". -/
theorem k13_exchangeS_at_356_at_firstThread
    (R : K1Seated (firstLetters hd parts w) 356 blk₆
      (fun v : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => ⟨v.x, ⟨v.trace, I.weights A.Z v.w₀, v.rc⟩⟩)
      (K1.wJobAt A.Z.first (K1.wGp A.Z) 4 wMsgFull first (wDataAt pileAnyK3 A.Z A.G)) own₀ .w
      (P5J.At.arr A.Z) seats₀ ms rad)
    (hc : parts.script.cells w =
      Bind.ForProver.cellsOfF frS frZ 402653181 numsRef (I.weights A.Z w.w₀).entry)
    (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hV : ExchangeAtS (firstThread hd parts w) Said 356 Item.pinV) :
    ExchangeS (firstThread hd parts w) Said 356 := by
  obtain ⟨Bs, base₀, Op⟩ := hd.head.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground hd.head.laid Op.blank hA
  exact k13_exchangeS_at_356 hd.head A.H parts.script _ _ _ _ _ 339 _ _ _ w
    (weights := I.weights A.Z) (pl := pileAnyK3 A.Z A.G) (by omega) R (eG ▸ Op.blank) rfl rfl
    (k13_matTie_at_firstLetters hd parts w hc) Said hV

/-- msgs, pads and hc are premises that are not shown here. **The same two shares with kind K1's
record replaced by its two fields on the Script.** hO: the filling's filler of the pile is
`pileAnyK3`. msgs, pads: the Script's messages and pads at W's seat are the texts of W's job. -/
theorem k13_items_at_356_of_script (hO : O.pile = pileAnyK3)
    {J : SendJob (PlaceIn ProofFile.Inst) Unit}
    (hJ : J = wJobAt A.Z.first (wGp A.Z) 4 wMsgFull (lotNo OnBytes.secondHashFunction A.Z ⟨1, none, 4, .K1⟩)
      (wDataAt pileAnyK3 A.Z A.G))
    (msgs : ∀ n, n < J.P.sent.size →
      OwnMsgs (firstLetters hd parts w).Q (firstLetters hd parts w).valid
        ((firstThread hd parts w).front + roundsTo (firstLetters hd parts w).bs 356)
        ((P5J.At.arr A.Z) (seatAtMember (firstLetters hd parts w).bs 356 J.P n).1
          (seatAtMember (firstLetters hd parts w).bs 356 J.P n).2)
        ((firstThread hd parts w).front + roundsTo (firstLetters hd parts w).bs 356)
        (msgTxt 0
          (fun v : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => ⟨v.x, ⟨v.trace, I.weights A.Z v.w₀, v.rc⟩⟩)
          J () n))
    (pads : ∀ n, n < J.P.sent.size →
      OwnPads (firstLetters hd parts w).Q (firstLetters hd parts w).valid
        (seatAtMember (firstLetters hd parts w).bs 356 J.P n).1
        (seatAtMember (firstLetters hd parts w).bs 356 J.P n).2 (fun k _ => padTxt 0 J n k))
    (hc : parts.script.cells w =
      Bind.ForProver.cellsOfF frS frZ 402653181 numsRef (I.weights A.Z w.w₀).entry)
    (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) :
    ExchangeAtS (firstThread hd parts w) Said 356 Item.pileOne ∧
      ExchangeAtS (firstThread hd parts w) Said 356 Item.wrow :=
  k13_items_at_356_of_lots hd.head hA _ (lotNo o A.Z) (hO ▸ hex_wM I o S O A.Z A.G)
    (hO ▸ ho_wM I o S O A.Z A.G) parts.script _ _ _ _ _ 339 _ _ _ w ()
    (L := firstLetters hd parts w) rfl hJ msgs pads (weights := I.weights A.Z)
    (pl := pileAnyK3 A.Z A.G) (by omega) rfl rfl (k13_matTie_at_firstLetters hd parts w hc) Said

end AtFullSide.K13

#print axioms AtFullSide.K13.k13_matTie_at_firstLetters
#print axioms AtFullSide.K13.k13_cells_of_record
#print axioms AtFullSide.K13.k13_items_at_356_at_firstThread
#print axioms AtFullSide.K13.k13_exchangeS_at_356_at_firstThread
#print axioms AtFullSide.K13.k13_items_at_356_of_script
