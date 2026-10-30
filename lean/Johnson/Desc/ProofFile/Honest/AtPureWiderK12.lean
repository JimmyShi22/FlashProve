-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AtPureWiderK12.lean: `widerFillOwnC` (Honest/AtPureWiderK10.lean) with
one list more: the prover's side of the proximity test that closes the proof file's first chain (the
sub-protocol "F:2", of the kind K12). The list is its authors' `K12.AtProof.lotAtDoor`
(Honest/K12/AtProof/LotAtDoor.lean), laid behind three public tests. Four definitions; eight short
lemmas.

  `proxLotOf`        the authors' list at this filling's letters, each by name: the rows' data
                     `widerRows S`; the readers that `widerFillOwn` gives the kind K2 and
                     `closeLotAt` the kind K10; the closing
                     `K2.lotClosingAt G.first.layout (K2.segmentsOf Z G)` (Honest/K2/Exact.lean)
  `proxLotAt`        that list behind three public tests: no side where one of them says no
  `widerFillOwnCP`   `widerFillOwnC` with `proxLotAt` behind its eleven lists
  `widerFillAtCP`    `widerFillAtC`'s sister
  `proxLotAt_name`   the list's name is the sealed lot's own string
  `proxLotAt_ok`, `proxLotAt_error`, `proxLotAt_else`   the three arms
  `proxLotOf_is`     the readers and the rows' data laid in `proxLotOf` are `widerFillOwn`'s
  `widerFillOwnCP_lots`, `widerFillOwnCP_old`, `widerFillOwnCP_prox`   the field `lots`

Limits.
  * THREE SILENT DEFAULTS OF THIS LAYING: no side where `ProofFile.onlineFirstChainAt Z` refuses, where no block
    of that chain stands at `K12.AtProof.placeL`, and where the planner's record
    `H2U.p12OfMade Z.made` bears another place. All three read the public part alone. THE SECOND AND
    THE THIRD ARE NEVER TAKEN: wherever the chain is made a block of it stands at that place
    (`proxPlace_stands`), and the record bears that place at every public part (`proxPlace`; both in
    Honest/AtPureWiderK12Places.lean); the two tests stand in the text all the same. So the premises
    of `proxLotAt_else` are met together at no public part: it serves a case split. Where there is
    no side, `lacking` (Honest/Frame.lean), which goes by place, names the sender; `lotsLacking`
    goes by the list's name and is quiet on this list once it is laid, side or none.
  * TWO MORE OF THE AUTHORS' LIST: no side where `K12.AtProof.finishAt Z G` is none or
    `K12.AtProof.fitsL` says no (Honest/K12/AtProof/LotL.lean).
  * THE TWO PARTS CANNOT REFUSE: every move returns a message, and neither part has a stop
    (Honest/K12/Parts.lean). A side here is no ground that they play. What fails beneath them fails
    in silence: the state on entry falls back on a state that holds nothing where its fold or the
    way in refuses (`K12.AtProof.atHandAtL` is the test that tells); the rows fall back on zeros and
    the tree's message on the zero message where `K12.AtProof.carryRows` refuses; five steps of the
    verifier's, above the state on entry, keep the state before them where they refuse
    (`TestJob.recB`, Honest/K12/Test.lean; Johnson/Desc/K12/Honest/Stages.lean); whether the rows'
    data is ready at the challenges heard is asked by no move (`K2.ownHeard`,
    Honest/K2/AtPlan.lean).
  * No word «plays», «accepted» or «tested» of the two parts, and no count, without, at each part's
    stand, each at its own front `fr`, by name: (i) `K12.AtProof.atHandAtL … = true` · (ii)
    `K12.AtProof.carryRows (widerRows S Z G) …` returns at the part's input, at `K12.AtProof.heardL
    fr` and at the part's stretches (Honest/K12/AtProof/JobL.lean): at this list's own closing
    alone; `widerRows S` closes over no witness, by its arguments; shown here at no plan; under
    `K2.closingOk`, `K2.publicOk` at the instance and `K2.ShapeFits` it is `carryRows_returns`
    (Honest/K12/AtFile/ClosingReturns.lean; not imported here) ·
    (iii) `K2.ownHeard … (K12.AtProof.heardL fr) = true` · (iv) the five steps return · (v) the
    front shows just the rounds in front: `fr.seen.rounds.length` is the number of declared rounds
    of the chain's blocks in front of the test's place · (vi)
    `fr.heard.length = fr.seen.rounds.length` · the block right in front of the test's place
    declares two rounds. As a theorem, never as a conjunct: (vii): the list's authors' `length_test`
    (Honest/K12/TermLen.lean): the number of rounds that `testAll` lists is `termLen` at the stages'
    numbers, at every input, under no premise; `test_covers` and `listed_at`
    (Honest/K12/TermCount.lean): at two stages or more a round is listed at every move of the two
    parts; `test_count`: just as many, where h ≤ k at every stage but the last. None is imported
    here. Open: that the list of trees that `testAll` returns (its field `tr`), which a move reads
    by `getD`, is as long as the two parts have moves.
  * `K12.AtProof.asK2` claims a count over a stretch that yields 0 beyond it. That the count is the
    lent entry's, at the parts' own stretches, is the list's authors' `carryRows_by_carried`
    (Honest/K12/AtProof/SeamL.lean; not imported here).
  * FOUR MORE KINDS OF SILENT DEFAULTS STAND IN THE PROVER's SEALED TEXT ABOVE THE STATE ON ENTRY,
    general in the job (found by the list's authors): `lastOut` takes the claim
    `⟨#[], #[], (0, 0, 0)⟩` where the stage or its claim is not found
    (Johnson/Prover/Link/BodyAll.lean; Johnson/Desc/K12/Honest/Stages.lean) · `rowOf t` is `{}`
    where the record passes no claim (BodyAll.lean) · `aAns` reads a stage and an element by
    defaults (Stages.lean) · challenges are read by `.elems.headD (0, 0, 0)` (`aPoint`, Stages.lean;
    `lastOut`). The first two hang on the record. The test on the state on entry covers none.
  * The state on entry is not shown to be the verifier's.
  * The first stage's mask table and its tails are zeros: the carrying message has no mask row
    (Honest/K12/AtProof/JobL.lean).
  * Wanted by name wherever `proxLotOf` is laid, and shown by nothing here: the closing's refusals
    hang on public fields alone. The list's authors' `carryRows_returns`
    (Honest/K12/AtFile/ClosingReturns.lean) says at this closing that the sender's text returns
    where `K2.publicOk` says yes at the instance, under `K2.ShapeFits` at the carrying message's
    shape and under `K2.closingOk`, which is shown true at no plan here; under the head, by the head
    of Honest/K2/Exact.lean: `closing_at_head` (Honest/K2/Law/ClosingAtHead.lean; not read for this
    file). That this closing is the one of the kind K2's own list (`K2.switchLot`) is
    `K2.switchSLot_toHLot` (Honest/K2/Rows.lean), an equation of two lists, the one laid at
    `K2.lotClosing`, which is this closing by definition; not imported here.
  * The readers hand on the whole family `w.rc`. What the two parts read of it is not stated here.
    No law over coins (a statement on a distribution) at this list is stated here.
  * That `onlineProverFromPublicFiles` returns at these choices of fields, that `ready` does, that a part plays or is
    accepted: none is stated here.
  * All limits of Honest/K12/AtProof/LotAtDoor.lean hold here, and those of
    Honest/AtPureWiderK10.lean, three of them in another form. STILL WITHOUT A SIDE in the first
    chain: K1's message "W". NEITHER CHOICE OF FIELDS HERE IS `widerFillOwnC` OR `widerFillAtC`: a
    law that is stated at one of these is to be paid anew here. That no side of the eleven stands
    at a place of the kind K12 is stated in no file that this one imports: `eleven_not_K12`
    (Honest/AtPureWiderK12Kinds.lean), under `FirstFill.LongKinds`.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtPureWiderK10
import Johnson.Desc.ProofFile.Honest.K12.AtProof.LotAtDoor
import Johnson.Desc.ProofFile.Honest.K2.Exact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Chain)

variable {W₀ X : Type}

/-! ## 1 The definitions -/

/-- **The authors' list at this filling's letters.** D := `widerRows S`. readers := what
`widerFillOwn` gives the kind K2 and `closeLotAt` the kind K10. closing := the term by which the
law of the kind K2's authors on the code switch's list names the sender's closing. -/
def proxLotOf (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) :
    HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X :=
  K12.AtProof.lotAtDoor (widerRows S)
    (fun Z _ (w : Local W₀ IndexCommitterCoins Inst Cells) => ⟨w.trace, I.weights Z w.w₀, w.rc⟩)
    (fun Z G => K2.lotClosingAt G.first.layout (K2.segmentsOf Z G))

/-- **The proximity test's list of prover's sides.** A SILENT DEFAULT: no side where the first chain
is not made, where no block of it stands at the test's place, or where the planner's record bears
another place (the last two are never taken: `proxPlace_stands`, `proxPlace`,
Honest/AtPureWiderK12Places.lean). THE TWO
PARTS CANNOT REFUSE: a side here is no ground that they play. The first stage's mask table and its
tails are zeros: the carrying message has no mask row. The state on entry is not shown to be the
verifier's. `lotsLacking` goes by the name and is quiet on this list once it is laid, side or none;
`lacking` goes by place. -/
def proxLotAt (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) :
    HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X :=
  { name := (proxLotOf (X := X) I S).name
    halves := fun Z G =>
      match ProofFile.onlineFirstChainAt Z with
      | .ok cF =>
        if cF.blocksInOrder.any (·.place == K12.AtProof.placeL) &&
            (H2U.p12OfMade Z.made).place == K12.AtProof.placeL
        then (proxLotOf I S).halves Z G else []
      | .error _ => [] }

/-- **`widerFillOwnC` with the proximity test's list behind its eleven.** The arguments are
`widerFillOwn`'s. -/
def widerFillOwnCP (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) : OnlineProverParts W₀ IndexCommitterCoins Cells Unit X :=
  { widerFillOwnC own₀ L I o S O with
    lots := (widerFillOwnC own₀ L I o S O).lots ++ [proxLotAt I S] }

/-- **`widerFillAtC`'s sister with the proximity test.** -/
def widerFillAtCP (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    OnlineProverParts W₀ IndexCommitterCoins Cells Unit Unit :=
  widerFillOwnCP () (LongLots.plain o S O) I o S O

/-! ## 2 The list -/

/-- The list's name is the string of the sealed lot (Johnson/Desc/ProofFile/Lot/K12.lean), typed
here a second time: no term ties the two. -/
theorem proxLotAt_name (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) :
    (proxLotAt (X := X) I S).name = "the proximity test at F:2 (K12)" := rfl

/-- **Where all three tests say yes**: the authors' list. hb and hq follow from h
(`proxLotAt_made`, Honest/AtPureWiderK12Places.lean). -/
theorem proxLotAt_ok (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) {Z : Pub} (G : Ground)
    {cF : Chain VerifiableInference.Desc.First.S ProofFile.Cl} (h : ProofFile.onlineFirstChainAt Z = .ok cF)
    (hb : cF.blocksInOrder.any (·.place == K12.AtProof.placeL) = true)
    (hq : ((H2U.p12OfMade Z.made).place == K12.AtProof.placeL) = true) :
    (proxLotAt (X := X) I S).halves Z G = (proxLotOf I S).halves Z G := by
  show (match ProofFile.onlineFirstChainAt Z with
    | .ok cF =>
      if cF.blocksInOrder.any (·.place == K12.AtProof.placeL) &&
          (H2U.p12OfMade Z.made).place == K12.AtProof.placeL
      then (proxLotOf (X := X) I S).halves Z G else []
    | .error _ => []) = _
  rw [h]
  simp [hb, hq]

/-- **Where the first chain is not made**: no side. -/
theorem proxLotAt_error (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) {Z : Pub} (G : Ground)
    {e : String} (h : ProofFile.onlineFirstChainAt Z = .error e) :
    (proxLotAt (X := X) I S).halves Z G = [] := by
  show (match ProofFile.onlineFirstChainAt Z with
    | .ok cF =>
      if cF.blocksInOrder.any (·.place == K12.AtProof.placeL) &&
          (H2U.p12OfMade Z.made).place == K12.AtProof.placeL
      then (proxLotOf (X := X) I S).halves Z G else []
    | .error _ => []) = _
  rw [h]

/-- **Where it is made and one of the two other tests says no**: no side. h AND hn ARE MET TOGETHER
AT NO PUBLIC PART (`proxPlace_stands`, `proxPlace`, Honest/AtPureWiderK12Places.lean): the lemma
says nothing of any Z; it closes the case split in `proxLotAt_sub` and `proxLotAt_once` there. -/
theorem proxLotAt_else (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) {Z : Pub} (G : Ground)
    {cF : Chain VerifiableInference.Desc.First.S ProofFile.Cl} (h : ProofFile.onlineFirstChainAt Z = .ok cF)
    (hn : (cF.blocksInOrder.any (·.place == K12.AtProof.placeL) &&
      (H2U.p12OfMade Z.made).place == K12.AtProof.placeL) = false) :
    (proxLotAt (X := X) I S).halves Z G = [] := by
  show (match ProofFile.onlineFirstChainAt Z with
    | .ok cF =>
      if cF.blocksInOrder.any (·.place == K12.AtProof.placeL) &&
          (H2U.p12OfMade Z.made).place == K12.AtProof.placeL
      then (proxLotOf (X := X) I S).halves Z G else []
    | .error _ => []) = _
  rw [h]
  simp [hn]

/-- **The rows' data and the readers laid in `proxLotOf` are `widerFillOwn`'s own fields.** -/
theorem proxLotOf_is (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    proxLotOf (X := X) I S =
      K12.AtProof.lotAtDoor (widerFillOwn own₀ L I o S O).rows
        (fun Z _ w => (widerFillOwn own₀ L I o S O).readers Z w.w₀ w.rc w.trace)
        (fun Z G => K2.lotClosingAt G.first.layout (K2.segmentsOf Z G)) := rfl

/-! ## 3 The choice of fields -/

/-- The field `lots`, written out. -/
theorem widerFillOwnCP_lots (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    (widerFillOwnCP own₀ L I o S O).lots =
      (widerFillOwnC own₀ L I o S O).lots ++ [proxLotAt I S] := rfl

/-- The eleven are members. -/
theorem widerFillOwnCP_old (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {M : HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X}
    (h : M ∈ (widerFillOwnC own₀ L I o S O).lots) : M ∈ (widerFillOwnCP own₀ L I o S O).lots :=
  List.mem_append_left _ h

/-- The twelfth is a member. -/
theorem widerFillOwnCP_prox (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    proxLotAt I S ∈ (widerFillOwnCP own₀ L I o S O).lots :=
  List.mem_append_right _ (.head _)

end ProofFile.Honest

#print axioms ProofFile.Honest.proxLotOf
#print axioms ProofFile.Honest.proxLotAt
#print axioms ProofFile.Honest.widerFillOwnCP
#print axioms ProofFile.Honest.widerFillAtCP
#print axioms ProofFile.Honest.proxLotAt_name
#print axioms ProofFile.Honest.proxLotAt_ok
#print axioms ProofFile.Honest.proxLotAt_error
#print axioms ProofFile.Honest.proxLotAt_else
#print axioms ProofFile.Honest.proxLotOf_is
#print axioms ProofFile.Honest.widerFillOwnCP_lots
#print axioms ProofFile.Honest.widerFillOwnCP_old
#print axioms ProofFile.Honest.widerFillOwnCP_prox
