-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AtPureWiderAt.lean: the choice of the fields of `OnlineProverParts` that
`widerFill` makes (Honest/AtPureWider.lean), general in the type of the index. The index may be any
type `W₀` with a reader of the matrix of digits that may depend on the public part; the trace stays
`Cells`. It is also general in the type of the sides' own state. Executable definitions. No theorem
is stated.

Why. A forward pass that can be evaluated takes the integer model's arrays as its index, not the
reader of the matrix of digits, and it computes that reader from the arrays and the public files.
`nowFill` and `widerFill` fix the index as `Weights` and give every kind the identity as its reader.

  1  `WiderIn`       what depends on the type of the index: the reader of the digits, the trace, the
                    range and its named member
  2  `HLot.byPub`    a kind's list of prover's sides whose reader of the index depends on the public
                    part
  3  `nowSharedBy`   the shared chain's prover's sides at a reader of the index, or an error message
  4  `LongLots`      the lists of K1 and of the four kinds that run long sumchecks, as arguments
  5  `widerFillOwn`  the choice of fields, general in the sides' own state
  6  `widerFillAt`   the same where no side keeps anything: the own state is `Unit`

How it relates to `widerFill`. At `LongLots.plain` the kinds, their order and their other arguments
are the same. At W₀ := `Weights`, the identity reader and `nowFill`'s range, two things differ. The
shared chain's sides are made by `K14.sixOf` (Honest/K14/Six.lean), which asks
three public tests first and returns an error message where one rejects; `nowShared`
(Honest/SharedChainProverSides.lean) asks none of them. And the trace is `WiderIn.trace`, so `OnlineProverArguments.cells` is
not read.

Why the own state is a type parameter. A side of K3, K6, K11 or K13 computes its tables again in
each move. That can be too slow to be evaluated at the stored examples' sizes: K3's is, by an
estimate; the others are not measured here. A side can pass its tables on from
move to move in its own state (`keepPart`, Honest/SumKeep.lean). All sides of a chain share one type
of own state, so that type and the four kinds' lists are arguments here; every other kind's list is
general in it. K1's list is an argument as well.
Honest/AtPureKeep.lean [not in this library] chooses them.

Which filling the lemmas are about. `widerFillAt` has each kind's first list (`LongLots.plain`). The
kinds' lemmas are stated of these lists, so `widerFillAt` is the filling of record. (`widerFillAtC`,
Honest/AtPureWiderK10.lean, adds K10's closings; no law at `widerFillAt` speaks of them.)

Limits.
  * Of `OnlineProverArguments` three functions are read and open here: `claims`, `pile` and `keyOf` (`openHonest`,
    Honest/OpenHonest.lean, gives them a value). Its fields `req`, `enc` and `cells` are not read.
  * `OnlineProverParts.shared` cannot return an error. Where `nowSharedBy` returns one, `widerFillAt` has no side
    in the shared chain. A caller asks `nowSharedBy` first.
  * `HLot.byPub` takes the list's name at the reader that is 0 everywhere. Each kind's name is a
    written string that depends on no reader; no lemma here says so.
  * A kind calls its reader of the index in each of its moves. What `WiderIn.weights` prepares
    inside its own body is prepared again at each call, and by one measurement in compiled code at
    each read of an entry. A caller that needs a prepared value puts it into the index.
  * Nothing compares `WiderIn.trace` with `WiderIn.weights`: that the trace is the one of the index
    whose digits the reader returns has to be shown by whoever supplies the two.
  * All limits of Honest/AtPureWider.lean hold here as well.
  * A lemma of a kind that asks that its own list is a member of `OnlineProverParts.lots` cannot be applied at
    `widerFillOwn`: a list that reads the index stands there inside `HLot.byPub`. What can be had is
    a member with the same sides: `HLot.byPub_halves` and `widerFillOwn_k4`
    (Honest/AtPureWiderLots.lean).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtPureWider
import Johnson.Desc.ProofFile.Honest.K14.Six

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

/-- **What depends on the type of the index.** -/
structure WiderIn (W₀ : Type) where
  /-- the matrix of digits, from the public part and the index -/
  weights : Pub → W₀ → Weights
  /-- a request's trace, as its reader; `none` where the request has no trace -/
  trace : Pub → W₀ → Inst → Option Cells
  /-- in range: a test on the index -/
  inRange : W₀ → Bool
  /-- a named member of the range -/
  dummy : W₀

variable {W₀ : Type}

/-- **A kind's list of prover's sides whose reader of the index depends on the public part.** `L`:
the list, from a reader. The name is taken at the reader that is 0 everywhere. -/
def HLot.byPub {V W X : Type} (weights : Pub → W₀ → Weights)
    (L : (W₀ → Weights) → HLot V W X) : HLot V W X :=
  { name := (L fun _ => ⟨fun _ _ => OnBytes.Slice.toF 0⟩).name
    halves := fun Z G => (L (weights Z)).halves Z G }

/-- **The shared chain's prover's sides at a reader of the index**, or an error message: where the
chain's own parameters or its place in the description cannot be computed, where one of the three
public tests of `K14.sixOf` rejects, and at `sixOf`'s arm for a list without "LIN point" or
"LIN zeta". -/
def nowSharedBy (weights : W₀ → Weights) (Z : Pub) :
    Except String (List (Placed Empty (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit)) :=
  (due? "the shared chain's own parameters" (p14At Z)).bind fun P =>
  (due? "the shared chain's place in the description" (onlineSharedChain Z)).bind fun s =>
    K14.sixOf P s.chain.blocksInOrder weights fun rc : IndexCommitterCoins => ⟨(rc P.item).pad, (rc P.item).tail⟩

/-- **The lists of K1 and of the four kinds that run long sumchecks**, each from a reader of the
index. `X`: the sides' own state. NOTHING TIES A FIELD TO ITS KIND, TO THE READER THAT IT IS HANDED,
OR TO THE S, o AND O OF `widerFillOwn`: a statement at `widerFillOwn` that needs one of these takes
it as a premise on L; at `LongLots.plain` they hold by its text. -/
structure LongLots (W₀ X : Type) where
  k1 : (W₀ → Weights) → HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X
  k3 : (W₀ → Weights) → HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X
  k6 : (W₀ → Weights) → HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X
  k11 : (W₀ → Weights) → HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X
  k13 : (W₀ → Weights) → HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X

/-- The five lists as `widerFill` has them: no side reads or writes the own state. -/
def LongLots.plain {X : Type} (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    LongLots W₀ X :=
  { k1 := fun wt =>
      K1.dataSideNo S (fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.x, ⟨w.trace, wt w.w₀, w.rc⟩⟩) o
    k3 := fun wt => K3.theLotInst id wt
    k6 := fun wt => K6.headLot K6.headFitsB (K6.headWit' id wt)
    k11 := fun wt => K11.headMergeLot O.claims wt
    k13 := fun wt => K13.k13Lot wt O.pile }

/-- **The choice of fields, general in the index and in the sides' own state.** `own₀`: the own
state before the first round. `L`: the five kinds' lists. `I`: what depends on the type of the
index. `_o` is not read since K1's list is an argument; no value of it has an effect here.
`S`: the model's sizes, for the data of the main rows. Of `O` the field `keyOf` alone is read
here. TWO SILENT DEFAULTS. `shared` is the empty list where `nowSharedBy (I.weights Z) Z` returns an
error: whoever speaks of the shared chain's sides names its return.
`second` is the empty list always, though by reading the second chain has a
sub-protocol that sends (its proximity test): so a sender is then without a side here, and no
sentence on an honest prover reaches that chain. -/
def widerFillOwn {X : Type} (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (_o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) : OnlineProverParts W₀ IndexCommitterCoins Cells Unit X :=
  { trace := I.trace
    readers := fun Z w rc T => ⟨T, I.weights Z w, rc⟩
    rows := widerRows S
    inRange := I.inRange, dummy := I.dummy
    enc := fun Z w => Bind.ForProver.encW Z (I.weights Z w)
    own₀ := own₀, ownShared₀ := (), meet := fun x _ => x
    lots := [
      HLot.byPub I.weights L.k1,
      HLot.byPub I.weights fun wt => HLot.byRows (widerRows S) fun D =>
        K2.switchLot D fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, wt w.w₀, w.rc⟩,
      replyLot,
      HLot.byPub I.weights L.k11,
      HLot.byPub I.weights L.k13,
      HLot.byPub I.weights L.k3,
      HLot.byPub I.weights fun wt => K4.k4HLot id wt fun _ _ => K4.k4LookAt,
      K5.k5LotK id O.keyOf,
      HLot.byPub I.weights L.k6,
      K8.smallLot id fun _ G _ l => K3.matsOwn G.W l]
    shared := fun Z _ => (nowSharedBy (I.weights Z) Z).toOption.getD []
    second := fun _ _ => [] }

/-- **The choice of fields, general in the index**, where no side keeps anything. Of `O` the fields
`req`, `enc` and `cells` are not read. -/
def widerFillAt (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    OnlineProverParts W₀ IndexCommitterCoins Cells Unit Unit :=
  widerFillOwn () (LongLots.plain o S O) I o S O

end ProofFile.Honest
