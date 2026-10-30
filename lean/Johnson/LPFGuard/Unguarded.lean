-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFGuard/Unguarded.lean: THE PROOF FILE's DESCRIPTION WITHOUT THE GUARD ON THE REPLY, and
THE STRIKE's STATEMENT. Definitions, and statements as `def … : Prop`. The only theorems here are
checks by unfolding (`rfl`) on the repeated texts.

Why. After every step of the proof file's first chain, except the one decision that hears the reply
(the block of the kind K7), the verifier rejects if that step has changed its stored copy of the
reply. That test, "the guard", is laid at three places of the description's text:
 (a) the driver lays the whole first chain behind it: `firstChain`,
     Johnson/Desc/First/Driver/Chain.lean: `(firstChainWithoutReplyGuard …).map (Chain.guarded H.same hearsReply)`;
 (b) what is joined behind a block is laid behind it: `chainBy`,
     Johnson/Desc/ProofFile/Frames1.lean: `x.2.guarded road.same fun _ => false`;
 (c) the first half of the block at "H:1" is laid behind it: `h1Own`,
     Johnson/Desc/ProofFile/Lots/H1.lean: `front.guarded sameReply fun _ => false`.
A yes behind the guard is the block's own yes, with the same state after it, by the guard's own
text: its test returns the state that it is handed, or refuses (Driver/Chain.lean).
The soundness theorem's proof takes from this test the fact that
only one step changes the reply. Here a second text of the description, without the test, is written
down, so that it can be said, and then proved, that what is laid for the two is the same.

HOW THE UNGUARDED DESCRIPTION IS MADE.
 (a), (b): THE CALL STANDS IN `descBare`'s TERM, WITH A TEST THAT ALWAYS SAYS YES. The test is a
     field of the seat, `PureSeat.same` (Johnson/Desc/ProofFile/OnlineDescriptionFromBlockTables.lean: "so that a test harness
     can run the same blocks with a guard that does nothing"; default `sameReply`). Here it is
     `fun _ _ => true`. That the guard is then the identity is stated: `Spec.idle_block`,
     `Spec.idle_chain` (of the structures, not only of what is run) and `Spec.idle_first`: the
     driver's `firstChain` is then its `firstChainWithoutReplyGuard`, the chain "without the guard".
 (c): THE CALL IS LEFT OUT OF THE TEXT. `sameReply` is written into `h1Own`, so its text is repeated
     without `.guarded sameReply fun _ => false`.
WHAT IS REPEATED: four short texts of the description (`h1Bare` for `h1Own`; `p4Bare` for `p4Pure`,
with `h1Bare` for `h1Own`; `thePureBare` for `onlineFirstChainBlockTables`, with `p4Bare` for `p4Pure`; `bareSeat` for
`pureSeat`, with `thePureBare` for `onlineFirstChainBlockTables` and the field `same` written) and one of the laying
(`laidPBare` for `proofDataAndDecisionOfPublicFiles`, with `descBare` for `ProofFile.onlineDescription`). `bareSeat`'s fields are written
out, and not taken from `ProofFile.pureSeat`, so that `descBare`'s term names neither `sameReply` nor
`h1Own`. HOW THEY ARE HELD:
 (1) BY LEAN, text by text: for each of the five a check by `rfl`, in this file's own namespace and
     opens, that the library's constant is the text written here with the guard's tokens, or the
     library's names, put back (`h1Own_text`, `p4Pure_text`, `thePure_text`, `pureSeat_text`,
     `laidPOf_text`); and `descPure_unfolds`: `ProofFile.onlineDescription` is `descBare`'s text with
     `ProofFile.pureSeat` for `bareSeat`. (`ProofFile.onlineDescription`'s own term does not name `pureSeat`: it writes
     that structure out; this check is what ties the two.)
 (2) BY LEAN, function by function: `laidAll wrap same` is the five repeated texts and `descBare`'s,
     six in all, as ONE FUNCTION of the two parts that turn. `proofDataAndDecisionOfPublicFiles` is its value at the guard's
     call and `sameReply`, `laidPBare` its value at the identity and the test that always says yes
     (`laidPOf_all`, `laidPBare_all`, by `rfl`). What is left to the eye is these two pairs of
     arguments.
 (3) BY A PROGRAM, token for token: each repeated text against the library's file and against its
     check's right side (the program is not in this library).
Not to be mixed up with `Frames.unguarded` (Johnson/Desc/ProofFile/FillCore.lean), which also does
nothing where a segment starts and ends and supplies no batching: it is for reading names and
places.

WHAT STANDS, in `descBare` as in `ProofFile.onlineDescription`: THE GUARD ON THE REPLY IS THE ONLY THING THAT PARTS
THE TWO. Every test of the verifier's own that reads the reply stands: K7's refusal "heard once"
(Johnson/Desc/Kinds/ReplyKind.lean) and its seat's test that the head's segment is entered
(Johnson/Stored/ReplySeatAt.lean); K13's need "K13.reply-heard" (Johnson/Desc/K13/Text.lean); what
K2's opening of the head's segment, K6 and `S.covered` read of it; the last test's `S.finAsked`: the
reply that was heard is the reply that is asked about (Johnson/Desc/First/State.lean; `fileDescBy`,
Frames1.lean). The one writer stands: K7's `setReply`. Two other things that a reader of the word
"guard" might think of stand too: `guardMark` (Frames1.lean: a refusal where a decision leaves a
mark of failure in the state) and the last test's clause that the request's words in the state are
still the instance's.

Main names.
* `h1Bare`, `p4Bare`, `thePureBare`, `bareSeat`, `descBare`, `laidPBare`; the checks.
* `Spec.idle_block`, `Spec.idle_chain`, `Spec.idle_first`: at a test that always says yes the guard
  is the identity on blocks and on chains, and `firstChain` is `firstChainWithoutReplyGuard`.
* `Alike F F'`, `Spec.strike_desc`: the two descriptions are made or refused together, with the same
  words. Where they are made they part in the first chain's structure alone, and the two first
  chains have one flat list and one last block's rounds. These two are all that is read of a first
  chain by the tests on the plan, the data, the decision and the two entry tests that read the
  description (AlikeLaid.lean).
* `Spec.strike`: THE STRIKE: `laidPBare o pol lay KL = proofDataAndDecisionOfPublicFiles o pol lay KL`: what is laid for the
  proof file (its data and its decision as a function of the instance and the three views, or a
  refusal with its words) is the same with the guard and without it. No premise: all bytes for the
  three public files, every function o in the place of the second hash function.
* `Spec.strike_the`: `Spec.strike` and an unfolding, no more: `proofDataAndDecisionOrRefusalAt`, the goals'
  description's own name for what is laid for the proof file, is `laidPBare`.

Limits.
1. Statements: nothing is proved here but the checks by `rfl`. The six statements are proved in
   Strike.lean.
2. THIS FILE's TOP STATEMENT STOPS AT `proofDataAndDecisionOrRefusalAt`. That the goals' description takes the proof
   file's description through that one door alone is NO THEOREM. What is a theorem: the goals'
   description is equal to one written function, `Text.theDescription`, at `LPFD.Full.proofDataAndDecisionOfPublicFiles`,
   which `proofDataAndDecisionOrRefusalAt` only calls (`Text.theDescription_at`, DoorText.lean). That equation alone
   would also hold of a function that throws its argument away. That there is no other way is read
   off the written function's text, which shows its twenty declarations and not what lies beneath
   the names that they name, and it is the print of a walk over Lean's constants, which is no proof
   (the walk's program is not in this library).
3. THE FULL SIZE ALONE at `Spec.strike`: `LPFD.Full.proofDataAndDecisionOfPublicFiles` (Johnson/Desc/Laid/ProofFull.lean),
   which is what the goals' description takes. The small example's `laidPOf` (Laid/ProofSmall.lean)
   is made of the same `ProofFile.onlineDescription`; its like is not stated; `Spec.strike_desc` serves both.
4. NOTHING OF THE LIBRARY's TEXT IS STRUCK OR TURNED: the verifier's description bears the guard at
   all three places. "The strike" does not say that the verdict is unchanged without the guard.
   It says less: that what is laid is unchanged (Limits 2, 7 and 9).
   Whether the call can be struck on it is not said here. `descBare` is a second description of the
   same verifier, written for these theorems alone; no definition outside this folder names it. No
   goal of the release is named or stated.
5. Nothing is said on the programs' verifier. That it has no such test is not checked here; that
   it is the verifier which `descBare` describes is no theorem.
6. The strike carries a theorem on the guarded description over to the unguarded one. It does not
   free that theorem's proof of the guard: the proof takes its fact from the test.
7. What is laid holds the decision as a yes or no. A run's words of refusal are not in it.
8. NO THEOREM OF THIS FOLDER SAYS THAT ANYTHING IS LAID AT ANY PUBLIC FILES: as far as its theorems
   go the equation could be of two refusals. Another theorem says that `proofDataAndDecisionOfPublicFiles` returns a value at
   the library's written terms meant to be the full-size files (`VerifierAndGoals.storedPublicFiles`), at the format's
   second hash, and speaks of no other files and of no other function in that hash's place:
   `AtFullSide.Top.theProofLaid_zFull_returns` (AtFullSide/Top/LiveAtFull.lean, in a side library,
   outside the main library). `FlashProve.theLive_made` (Johnson/Goal/Description/Live.lean) says it
   wherever the test `protocolDataWellFormed` says yes, and the side library says that also at `storedPublicFiles`'s files
   under other policies (`theLive_zGap`; `theLive_zAt`, within four bounds;
   AtFullSide/Top/LiveAtPolicies.lean); `seats_zGap` and `seats_zAt` (AtFullSide/Top/GatesOpen.lean)
   join the two: `proofDataAndDecisionOfPublicFiles` returns a value there too. That a value is returned does not say that any
   proof is accepted. That the written terms are the release's public files is no theorem. There are
   compiled #guard checks at two places, evaluations, which compare digests with stored values:
   Ladder/Guards.lean, of the three together; Johnson/Top/Own/OwnStoredFullRun.lean, of the same
   layout and scale terms, against sums taken of the example's files outside Lean. Not tested in
   this library: that the example's files have the sums that Ladder/Stored.lean lists. That
   `proofDataAndDecisionOfPublicFiles` returns a value at the release's public files no theorem says, and this folder does not
   run it there. It can be known by running it there, or, at the second hash function, from the
   theorem at the written terms by whoever holds these files against the terms outside Lean.
9. "Without the guard" rests on `Spec.strike` AND the three `Spec.idle_…` together, and on one step
   more: that the calls at places (a) and (b) are handed the seat's field `same` (`partsAt`,
   Pure.lean; `chainBy`, Frames1.lean; `fill`, FillCore.lean; `firstChain`, Driver/Chain.lean). Here
   that is read off these texts. Of the values the library proves two links of it: the road's test
   is the seat's (`ProofFile.Law.partsAt_road_same`); the chain that `chainBy` returns is `firstChain` at
   a structure with the road's test, and what is joined behind a block is guarded with that test
   (`ProofFile.Law.chainBy_first_same`; of the chain's last block too: `ProofFile.Law.chainBy_first_fill`; all
   three: Johnson/Desc/ProofFile/Law/FirstSame.lean). This folder does not call them at `bareSeat`.
10. The strike stands at the entry tests of this library (`LPFD.lawsAsk`, fourteen rows, of which
    two read the description).
11. Nothing on soundness, completeness or hiding.

What it leans on. Definitions of the library alone, each named above with its file. No proof is
carried from another file.


-/
import Johnson.Desc.Laid.ProofFull
import Johnson.Goal.Description.ProofFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFGuard

open VerifiableInference.Desc (Block roundlessBlock FileDescription Chain Place)
open VerifiableInference.Desc.First
open ProofFile (Lot Ground Pub PureSeat SecondHashFunctionArgument)

/-- The block at "H:1", without the guard on its first half: `ProofFile.h1Own`'s text without
`.guarded sameReply fun _ => false`. -/
def h1Bare (G : Ground) : List (Block S Unit) :=
  let l := G.built.size - 1
  let own : Block S Unit := P4.k7Core G
  let front : Block S Unit :=
    { (roundlessBlock "H:1" 1 (some l) 1 (K2.headFrontQ G.W.H.tl) : Block S Unit) with
      place := own.place }
  [front.andThen "H:1" own]

/-- A check: `ProofFile.h1Own` is `h1Bare`'s text with the guard's tokens put back. By unfolding alone. -/
theorem h1Own_text (G : Ground) : ProofFile.h1Own G =
  (let l := G.built.size - 1
  let own : Block S Unit := P4.k7Core G
  let front : Block S Unit :=
    { (roundlessBlock "H:1" 1 (some l) 1 (K2.headFrontQ G.W.H.tl) : Block S Unit) with
      place := own.place }
  [(front.guarded ProofFile.sameReply fun _ => false).andThen "H:1" own]) := rfl

/-- `ProofFile.p4Pure`'s text with `h1Bare` for `h1Own`. -/
def p4Bare (Z : Pub) : List Lot :=
  [P4.k6Lot Z,
   { name := "the next token (K7), with the step that enters the head's link"
     letters := false
     own := h1Bare }]

/-- A check: `ProofFile.p4Pure` is `p4Bare`'s text with `ProofFile.h1Own` for `h1Bare`. By unfolding alone. -/
theorem p4Pure_text (Z : Pub) : ProofFile.p4Pure Z =
  [P4.k6Lot Z,
   { name := "the next token (K7), with the step that enters the head's link"
     letters := false
     own := ProofFile.h1Own }] := rfl

/-- `ProofFile.onlineFirstChainBlockTables`'s text with `p4Bare` for `p4Pure`. -/
def thePureBare (Z : Pub) : List Lot :=
  [ProofFile.framesLot Z, ProofFile.k1Pure Z, ProofFile.k2Pure Z, K3Lot.lot Z, ProofFile.k4Lot Z, H2K5.lotN Z,
   ProofFile.P1K8.lot Z, ProofFile.k9Ninth Z, K11.lot Z, VerifiableInference.Desc.K12.lot Z,
   VerifiableInference.Desc.K13.lot Z, VerifiableInference.Desc.K13.lot4 Z,
   VerifiableInference.Desc.K13.lotEnd Z] ++ p4Bare Z

/-- A check: `ProofFile.onlineFirstChainBlockTables` is `thePureBare`'s text with `ProofFile.p4Pure` for `p4Bare`. By unfolding
alone. -/
theorem thePure_text (Z : Pub) : ProofFile.onlineFirstChainBlockTables Z =
  [ProofFile.framesLot Z, ProofFile.k1Pure Z, ProofFile.k2Pure Z, K3Lot.lot Z, ProofFile.k4Lot Z, H2K5.lotN Z,
   ProofFile.P1K8.lot Z, ProofFile.k9Ninth Z, K11.lot Z, VerifiableInference.Desc.K12.lot Z,
   VerifiableInference.Desc.K13.lot Z, VerifiableInference.Desc.K13.lot4 Z,
   VerifiableInference.Desc.K13.lotEnd Z] ++ ProofFile.p4Pure Z := rfl

/-- The seat without the guard: `ProofFile.pureSeat`'s text with `thePureBare` for `onlineFirstChainBlockTables`, and with the
field `same`, which that text leaves at its default `sameReply`, at a test that always says yes. -/
def bareSeat (o : SecondHashFunctionArgument) (Z : Pub) : PureSeat :=
  { links := ProofFile.pureRoad.links, lots := thePureBare Z, shared := ProofFile.onlineSharedChain Z
    second := ProofFile.onlineLastChain Z, older := o, same := fun _ _ => true }

/-- A check: `ProofFile.pureSeat` is `bareSeat`'s text with `ProofFile.onlineFirstChainBlockTables` for `thePureBare` and
`ProofFile.sameReply` for the test that always says yes. By unfolding alone. -/
theorem pureSeat_text (o : SecondHashFunctionArgument) (Z : Pub) : ProofFile.pureSeat o Z =
  { links := ProofFile.pureRoad.links, lots := ProofFile.onlineFirstChainBlockTables Z, shared := ProofFile.onlineSharedChain Z
    second := ProofFile.onlineLastChain Z, older := o, same := ProofFile.sameReply } := rfl

/-- A check: `bareSeat` is `ProofFile.pureSeat` with these two fields turned. By unfolding alone. -/
theorem bareSeat_turns (o : SecondHashFunctionArgument) (Z : Pub) :
    bareSeat o Z = { ProofFile.pureSeat o Z with lots := thePureBare Z, same := fun _ _ => true } := rfl

/-- **The proof file's description without the guard on the reply**: at the driver's place and at
`chainBy`'s the guard is still called, with a test that always says yes; at the block "H:1" the call
is gone. That the first two calls then do nothing is `Spec.idle_block`, `idle_chain`, `idle_first`.
-/
def descBare (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) : Except String (FileDescription ProofFile.Inst) :=
  (ProofFile.pureRoad.pub o pol lay KL).bind fun Z => ProofFile.onlineDescriptionFromPublicPart Z (bareSeat o Z)

/-- A check on `descBare`'s text: `ProofFile.onlineDescription` is that text with `ProofFile.pureSeat` for `bareSeat`. By
unfolding alone. -/
theorem descPure_unfolds (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) :
    ProofFile.onlineDescription o pol lay KL =
      (ProofFile.pureRoad.pub o pol lay KL).bind fun Z => ProofFile.onlineDescriptionFromPublicPart Z (ProofFile.pureSeat o Z) := rfl

/-- **What is laid for the proof file, without the guard** (in `descBare`'s sense):
`LPFD.Full.proofDataAndDecisionOfPublicFiles`'s text with `descBare` for `ProofFile.onlineDescription`. -/
def laidPBare (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) :
    Except String (OnBytes.Maker.WholeD × LPFD.Full.RunPF) :=
  match descBare o pol lay KL with
  | .error e => .error ("the proof file's description is not made: " ++ e)
  | .ok F => LPFD.Full.proofDataAndDecisionOfDescription o pol lay KL F

/-- A check: `LPFD.Full.proofDataAndDecisionOfPublicFiles` is `laidPBare`'s text with `ProofFile.onlineDescription` for `descBare`. By
unfolding alone. -/
theorem laidPOf_text (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) : LPFD.Full.proofDataAndDecisionOfPublicFiles o pol lay KL =
  (match ProofFile.onlineDescription o pol lay KL with
  | .error e => .error ("the proof file's description is not made: " ++ e)
  | .ok F => LPFD.Full.proofDataAndDecisionOfDescription o pol lay KL F) := rfl

/-! ### The same check, in Lean alone: each text as one function of the part that turns -/

/-- `h1Own`'s and `h1Bare`'s text, as a function of what is laid around the first half. -/
def h1With (wrap : Block S Unit → Block S Unit) (G : Ground) : List (Block S Unit) :=
  let l := G.built.size - 1
  let own : Block S Unit := P4.k7Core G
  let front : Block S Unit :=
    { (roundlessBlock "H:1" 1 (some l) 1 (K2.headFrontQ G.W.H.tl) : Block S Unit) with
      place := own.place }
  [(wrap front).andThen "H:1" own]

theorem h1Own_with : ProofFile.h1Own = h1With fun b => b.guarded ProofFile.sameReply fun _ => false := rfl

theorem h1Bare_with : h1Bare = h1With fun b => b := rfl

/-- `p4Pure`'s and `p4Bare`'s text, as a function of the block at "H:1". -/
def p4With (h1 : Ground → List (Block S Unit)) (Z : Pub) : List Lot :=
  [P4.k6Lot Z,
   { name := "the next token (K7), with the step that enters the head's link"
     letters := false
     own := h1 }]

theorem p4Pure_with : ProofFile.p4Pure = p4With ProofFile.h1Own := rfl

theorem p4Bare_with : p4Bare = p4With h1Bare := rfl

/-- `onlineFirstChainBlockTables`'s and `thePureBare`'s text, as a function of the last two lots. -/
def pureWith (p4 : Pub → List Lot) (Z : Pub) : List Lot :=
  [ProofFile.framesLot Z, ProofFile.k1Pure Z, ProofFile.k2Pure Z, K3Lot.lot Z, ProofFile.k4Lot Z, H2K5.lotN Z,
   ProofFile.P1K8.lot Z, ProofFile.k9Ninth Z, K11.lot Z, VerifiableInference.Desc.K12.lot Z,
   VerifiableInference.Desc.K13.lot Z, VerifiableInference.Desc.K13.lot4 Z,
   VerifiableInference.Desc.K13.lotEnd Z] ++ p4 Z

theorem thePure_with : ProofFile.onlineFirstChainBlockTables = pureWith ProofFile.p4Pure := rfl

theorem thePureBare_with : thePureBare = pureWith p4Bare := rfl

/-- `pureSeat`'s and `bareSeat`'s text, as a function of the lots and the guard's test. -/
def seatWith (lots : Pub → List Lot) (same : S → S → Bool) (o : SecondHashFunctionArgument) (Z : Pub) : PureSeat :=
  { links := ProofFile.pureRoad.links, lots := lots Z, shared := ProofFile.onlineSharedChain Z
    second := ProofFile.onlineLastChain Z, older := o, same := same }

theorem pureSeat_with : ProofFile.pureSeat = seatWith ProofFile.onlineFirstChainBlockTables ProofFile.sameReply := rfl

theorem bareSeat_with : bareSeat = seatWith thePureBare fun _ _ => true := rfl

/-- `onlineDescription` and `descBare`, as a function of the seat. -/
def descWith (seat : SecondHashFunctionArgument → Pub → PureSeat) (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) :
    Except String (FileDescription ProofFile.Inst) :=
  (ProofFile.pureRoad.pub o pol lay KL).bind fun Z => ProofFile.onlineDescriptionFromPublicPart Z (seat o Z)

theorem descPure_with : ProofFile.onlineDescription = descWith ProofFile.pureSeat := rfl

theorem descBare_with : descBare = descWith bareSeat := rfl

/-- `proofDataAndDecisionOfPublicFiles`'s and `laidPBare`'s text, as a function of the description. -/
def laidWith
    (desc : SecondHashFunctionArgument → ByteArray → ByteArray → ByteArray → Except String (FileDescription ProofFile.Inst))
    (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) :
    Except String (OnBytes.Maker.WholeD × LPFD.Full.RunPF) :=
  match desc o pol lay KL with
  | .error e => .error ("the proof file's description is not made: " ++ e)
  | .ok F => LPFD.Full.proofDataAndDecisionOfDescription o pol lay KL F

theorem laidPOf_with : LPFD.Full.proofDataAndDecisionOfPublicFiles = laidWith ProofFile.onlineDescription := rfl

theorem laidPBare_with : laidPBare = laidWith descBare := rfl

/-- **The six put together: what is laid for the proof file, as a function of what is laid around
the first half of the block at "H:1" and of the guard's test.** -/
def laidAll (wrap : Block S Unit → Block S Unit) (same : S → S → Bool) :
    SecondHashFunctionArgument → ByteArray → ByteArray → ByteArray →
      Except String (OnBytes.Maker.WholeD × LPFD.Full.RunPF) :=
  laidWith (descWith (seatWith (pureWith (p4With (h1With wrap))) same))

theorem laidPOf_all :
    LPFD.Full.proofDataAndDecisionOfPublicFiles = laidAll (fun b => b.guarded ProofFile.sameReply fun _ => false) ProofFile.sameReply :=
  rfl

theorem laidPBare_all : laidPBare = laidAll (fun b => b) fun _ _ => true := rfl

/-! ### The statements -/

/-- At a test that always says yes the guard is the identity on a block. So it is at place (b) of
the unguarded description. -/
def Spec.idle_block : Prop :=
  ∀ (but : Place → Bool) (b : Block S ProofFile.Cl), b.guarded (fun _ _ => true) but = b

/-- The like for a chain, as a structure: also what starts and ends a segment, and a segment's
batching at every function of claims. -/
def Spec.idle_chain : Prop :=
  ∀ (but : Place → Bool) (c : Chain S ProofFile.Cl), c.guarded (fun _ _ => true) but = c

/-- So at place (a): where the structure's test always says yes, the driver's first chain is its
bare chain, "without the guard". -/
def Spec.idle_first : Prop :=
  ∀ (H : Blocks S ProofFile.Cl) (links : List ModelPart) (several : Bool), (∀ t s, H.same t s = true) →
    firstChain H links several = firstChainWithoutReplyGuard H links several

/-- Two descriptions part in the first chain's structure alone, and the two first chains have one
flat list and one last block's rounds. -/
def Alike (F F' : FileDescription ProofFile.Inst) : Prop :=
  ∃ (o : SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat)
    (c c' : Chain S ProofFile.Cl),
    F = ProofFile.fileDescBy o mk Z A B (fun s => s) (ProofFile.startS Z) c ∧
      F' = ProofFile.fileDescBy o mk Z A B (fun s => s) (ProofFile.startS Z) c' ∧
      c'.blocksInOrder = c.blocksInOrder ∧ c'.last.rounds = c.last.rounds

/-- The two descriptions are made or refused together. -/
def Spec.strike_desc : Prop :=
  ∀ (o : SecondHashFunctionArgument) (pol lay KL : ByteArray),
    match ProofFile.onlineDescription o pol lay KL, descBare o pol lay KL with
    | .ok F, .ok F' => Alike F F'
    | .error e, .error e' => e' = e
    | _, _ => False

/-- **THE STRIKE**: what is laid for the proof file is the same without the guard as with it, at all
bytes for the three public files and every function o in the place of the second hash function. -/
def Spec.strike : Prop :=
  ∀ (o : SecondHashFunctionArgument) (pol lay KL : ByteArray),
    laidPBare o pol lay KL = LPFD.Full.proofDataAndDecisionOfPublicFiles o pol lay KL

/-- The same at `proofDataAndDecisionOrRefusalAt`, the name by which the goals' description takes what is laid for
the proof file. -/
def Spec.strike_the : Prop :=
  ∀ (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub),
    FlashProve.proofDataAndDecisionOrRefusalAt o Zk = laidPBare o Zk.pol Zk.lay Zk.KL

end LPFGuard

#print axioms LPFGuard.h1Own_text
#print axioms LPFGuard.p4Pure_text
#print axioms LPFGuard.thePure_text
#print axioms LPFGuard.pureSeat_text
#print axioms LPFGuard.bareSeat_turns
#print axioms LPFGuard.descPure_unfolds
#print axioms LPFGuard.laidPOf_text
#print axioms LPFGuard.h1Own_with
#print axioms LPFGuard.h1Bare_with
#print axioms LPFGuard.p4Pure_with
#print axioms LPFGuard.p4Bare_with
#print axioms LPFGuard.thePure_with
#print axioms LPFGuard.thePureBare_with
#print axioms LPFGuard.pureSeat_with
#print axioms LPFGuard.bareSeat_with
#print axioms LPFGuard.descPure_with
#print axioms LPFGuard.descBare_with
#print axioms LPFGuard.laidPOf_with
#print axioms LPFGuard.laidPBare_with
#print axioms LPFGuard.laidPOf_all
#print axioms LPFGuard.laidPBare_all
