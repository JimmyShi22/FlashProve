-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AtPureWider.lean: a second choice of the fields of `OnlineProverParts`
(Honest/AtPure.lean) for the honest prover of the proof file's description. It has every prover's
side that `nowFill` (Honest/AtPureSixKinds.lean) has and those of four kinds more, it supplies two of the
six functions that `nowFill` leaves open, and it supplies the data of K1's and K2's oracle messages.
Executable definitions, and one lemma by unfolding.

How it relates to `nowFill`. That definition and its structure of open functions, `OnlineProverArguments`, are
unchanged, because lemmas in other files name them. `widerFill` takes the same `OnlineProverArguments` and reads
neither its field `req` nor its field `enc`. Every field that is not named below is `nowFill`'s.

  1  `HLot.byRows`   a kind's list of prover's sides whose data of the main rows depends on the
                    public part and the ground; `HLot.byRows_halves`: its sides, by unfolding
  2  `widerRows`     the data of the oracle messages' main rows
  3  `widerFill`     the choice of fields

What is added to the list of the first chain's kinds.
  * K1, the kind of the oracle messages' sendings: the prover's sides at the first place of the
    first segment and at each link's two later places, "reads" and "digits" (`K1.dataSideNo`,
    Honest/K1/LotNoPure.lean).
  * K2, the code switch: `K2.switchLot` (Honest/K2/AtPlan.lean), at the data `widerRows`.
  * K4: the prover's sides at the layers' segments (`K4.k4HLot`, Honest/K4/Part.lean). Its argument
    `look`, what the lookup before it has sampled, is `K4.k4LookAt` (Honest/K4/Look.lean).
  * K8, the smallness test: `K8.smallLot` (Honest/K8/Part.lean). Its argument `mats`, each link's
    list of matrices, is `K3.matsOwn` (Honest/K3/WitOwner.lean) at the ground's public data.

What is supplied.
  * The covered positions and the checked tokens of a request: `K3.theLotInst`
    (Honest/K3/LotInst.lean) computes them from the instance by `K3.reqAt` (Honest/K3/WitReq.lean).
    It takes the place of `K3.theLot` at `OnlineProverArguments.req`.
  * The columns of the committed table: `Bind.ForProver.encW` (Johnson/Bind/ForProver/Enc.lean).
  * The data of the main rows: of K1's oracle messages `K1.lotData` (Honest/K1/LotData.lean), and
    of the messages that a switch itself sends `K2.switchData`, joined to it by
    `K2.withSwitchData` (Honest/K2/OwnData.lean).

Limits.
  * Four functions are still open: `claims`, `pile`, `keyOf` and `cells` (`OnlineProverArguments`). K5 has a
    prover's side at a segment only where its test `keysFit` accepts what `keyOf` returns at blank
    challenges (`K5.seatAtK`, Honest/K5/KeysFit.lean).
  * K3's side is laid also where the tests at its seat reject (`K3.theLotInstFit`,
    Honest/K3/LotInst.lean, is the form that asks them). K4 and K6 lay theirs only where
    `K4.k4TableFits` (Honest/K4/Part.lean) and `K6.headFitsB` accept.
  * The second chain has no prover's side, as in `nowFill`.
  * There is no prover's side for K1 at the place of the message "W", nor for K9, K10 and K12.
  * Whether `widerRows` has data at every address that K2's sides read is not compared here: they
    return an error where an array of a message has no data. Their authors' public test for it
    (`K2.publicOk`, Honest/K2/Sim.lean) has not been evaluated at this data.
  * `HLot.byRows` takes the list's name at the empty data. K2's name is a written string that
    depends on no data; no lemma here says so.
  * `S`, the model's sizes that K1's first place reads, is an argument. Nothing compares it with the
    public files.
  * `encW` returns columns at the statement's item 0 alone. The shared chain's own parameters name
    that item (`Desc.K14.p14Of`, Johnson/Desc/K14/Blocks.lean), and `nowShared` reads the
    committer's coins of the item that they name. `encW` computes all rows again at each call; by
    its own head it has been run at toy shapes alone, gives columns also at shapes that the
    verifier's test on the shape rejects, and is the format's code only where a is at most 32.
  * `K4.k4LookAt` rests on two hypotheses, which its docstring states: where the lookup's rounds
    are, and at which shape the lookup is heard.
  * Nothing compares `K3.matsOwn` with the list that K8's sub-protocol has at a place. K8's part
    returns an error where the two lists differ in length.
  * `K3.reqAt` returns empty arrays where the library's tests reject a request. The test on the
    instance (`K3.reqMadeB` and `K3.sizesOneB`) is asked by whoever supplies the instance.
  * K1's public tests and lemmas are stated at `K1.lotData`, not at `widerRows`. That `widerRows`
    returns `K1.lotData`'s data at every sender that is not of the kind K2 is `K2.with_other_kind`
    (Honest/K2/Law/OwnDataApart.lean), which this file does not import. By its authors' letter that
    file does not say what `K1.lotData` returns at a switch's address; no lemma that says it is
    known to this file's author.
  * `K1.dataSideNo` computes the description again from the public part and `o`, for the number
    that a place's first new message gets. By its own head that number enters nothing that is sent.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtPureSixKinds
import Johnson.Desc.ProofFile.Honest.K1.LotNoPure
import Johnson.Desc.ProofFile.Honest.K2.OwnData
import Johnson.Desc.ProofFile.Honest.K3.LotInst
import Johnson.Desc.ProofFile.Honest.K4.Part
import Johnson.Desc.ProofFile.Honest.K4.Look
import Johnson.Desc.ProofFile.Honest.K8.Part
import Johnson.Bind.ForProver.Enc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

/-- **A kind's list of prover's sides whose data of the main rows depends on the public part and the
ground.** `L`: the list, from the data. The name is taken at the empty data. -/
def HLot.byRows {V W X Xi : Type} (D : Pub → Ground → RowDataOf Xi)
    (L : RowDataOf Xi → HLot V W X) : HLot V W X :=
  { name := (L fun _ => RowData.empty).name
    halves := fun Z G => (L (D Z G)).halves Z G }

/-- Its sides at a public part and a ground are the list's at the data there. -/
theorem HLot.byRows_halves {V W X Xi : Type} (D : Pub → Ground → RowDataOf Xi)
    (L : RowDataOf Xi → HLot V W X) (Z : Pub) (G : Ground) :
    (HLot.byRows D L).halves Z G = (L (D Z G)).halves Z G := rfl

/-- **The data of the oracle messages' main rows**: K1's, and that of the messages that a switch
itself sends. `S`: the model's sizes. -/
def widerRows (S : OnBytes.HonestTrace.Sz) : Pub → Ground → RowDataOf Inst :=
  K2.withSwitchData S (K1.lotData S)

/-- **The wider choice of fields.** `o`: the function that stands for the format's second hash function:
the one that `onlineProverFromPublicFiles` is handed; nothing here ties the two. `S`: the model's sizes, for K1's first
place. `O`: the open functions, of which `req` and `enc` are not read. `shared` and `second` are
`nowFill`'s, WITH THEIR TWO SILENT DEFAULTS (its comment; `widerFill_shared_ok`,
`widerFill_shared_error`, Honest/AtPureSharedOk.lean). `inRange` and `dummy` are `nowFill`'s too:
every index is in range. -/
def widerFill (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    OnlineProverParts Weights IndexCommitterCoins Cells Unit Unit :=
  { nowFill O with
    rows := widerRows S
    enc := Bind.ForProver.encW
    lots := [
      K1.dataSideNo S (fun w : Local Weights IndexCommitterCoins Inst Cells => ⟨w.x, ⟨w.trace, w.w₀, w.rc⟩⟩) o,
      HLot.byRows (widerRows S) fun D =>
        K2.switchLot D fun w : Local Weights IndexCommitterCoins Inst Cells => ⟨w.trace, w.w₀, w.rc⟩,
      replyLot, K11.headMergeLot O.claims id, K13.k13Lot id O.pile, K3.theLotInst id id,
      K4.k4HLot id id (fun _ _ => K4.k4LookAt), K5.k5LotK id O.keyOf,
      K6.headLot K6.headFitsB (K6.headWit' id id),
      K8.smallLot id (fun _ G _ l => K3.matsOwn G.W l)] }

end ProofFile.Honest

#print axioms ProofFile.Honest.HLot.byRows_halves
