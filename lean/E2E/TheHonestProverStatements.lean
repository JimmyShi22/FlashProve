-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/TheHonestProverStatements.lean: what the honest prover of the protocol is, and what must hold of
it. The value itself, honestProvers, stands in E2E/TheHonestProver.lean; this file adds no prover.

The protocol has three parts, named by what a user holds. offline: the proof in the key file, on the
committed table. link: from a further encoding to the first. online: the proof for a request (the
proof file).

1. The honest prover of the protocol is written as the prover of an interactive oracle proof.
   No random oracle or hash tree enters. The rounds have their place for the proof of work, and no
   search for it enters. The format's second, fixed hash function enters as it does in the
   verifier's description.
2. There is one prover for each part, in the type ThreeProvers that the compiler's theorems take. The
   offline and the online prover both send out-of-domain answers; the seeds are inputs of the
   provers, taken at every value.
3. The offline and the online prover stand in one frame, which pairs a sender with each of the
   verifier's blocks, over the description from which the verifier's decision is made: online, that
   is the proposition ReturnIsTheDescription. The link's prover is written round by round against
   its description's decision.
4. The link's prover is written in full: it takes no argument.
5. The online prover takes no argument. A sender is meant to stand at every place of the verifier's
   description but those of the batching (K9), where the round declares nothing (the proposition
   SidesAreWhole). At the places listed at the end it sends fixed values where a function that it
   calls refuses. At a zero challenge of the second token sumcheck it plays on, and the verifier's
   block is meant to refuse there (the proposition ZeroChallengeIsRefused). This term does not
   withhold a run that the verifier refuses. Such a run is shown: the refusing block's own messages
   go out to its end, each later round of that chain and of the last chain sends a fixed substitute,
   the shared chain plays whole, and the real tables and the stored table are still read and opened
   (Johnson/Desc/ProofFile/Honest/Walk.lean).
   The online prover is made from the three public files by the functions that also make the
   verifier's description; where one of them refuses, it sends the fixed messages, and it withholds
   nothing there. It is a definition at the full size and no program: it reads the trace by choices.
6. The offline prover is a skeleton over the verifier's description. The kinds of its senders and
   their order are fixed, and the forms of all senders are written. What they are applied to is an
   argument of honestProvers, the structure Parts: its book of coins, how the index and the
   committer's coins are read and which indices are in range, the stored table, what the sides pass
   on, the shared chain's data, the places of the senders of the first chain, what the test on the
   ranges reads, and what the three sendings, the two lookups and the batching of the first chain
   send.
7. So honestProvers is a function of the public files and of Parts. Neither file gives a value of
   Parts. A statement about the honest prover is about honestProvers at one named value of Parts.
8. The committer is no fourth prover. At this level it is the object's encoder encodeIndex, its
   out-of-domain record recOf, and their randomness. The compilation makes the committer of the
   scheme that publishes the whole key from these and from the first two provers
   (OnBytes.WholeKey.commitW); the committer whose commitment is one 256-bit identifier is made from
   that one.
9. No type of the value asks that the model has a result: a well-formed request is an input of the
   provers, also where the model has none, and their strategies are total. At a request without a
   trace, or at an index out of range, the online prover plays on with no side and withholds
   nothing. So honestProvers is not the value that the statements on completeness and zero knowledge
   and the compiler are meant to read. That value is honestProversAndSettingsAtFiles (Johnson/Face/HonestProversWithCompiledPart.lean):
   these provers under HonestProvers.refuseUnserved, which widens the private stop set to everything
   where the request is not served. Whether a request is served depends on the weights, which the
   prover holds.
10. This file and that one prove no property of the protocol. What must hold for the value to be
    the protocol's prover is listed below as named propositions, then the run values that a coin
    fixes, and then the places where a sender falls back on a fixed value.

Names from the library. FullSizeMatrix: the matrices of the full size's shape, the index. protocolAtFiles files: the object
with records at the public files; by object_description (E2E/DescriptionTie.lean) it is the object
in the verifier's compiled input, whose own three provers send the fixed messages and are read by no
verifier. Cz files: its configuration. descZ: the online description. onlineProversOfCommitter: the online prover as
a family, one member for each copy's number. offlineProverWithEncodedTable, linkProverAtFiles: the offline and the link's prover at the
object. KeyParts: the offline prover's senders. P12: the numbers of a proximity test's place.
-/
import E2E.TheHonestProver
import E2E.KeyPublic
import Johnson.WholeKey.Premises

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

/-! ## 1 What must hold for it to be the protocol's prover

The propositions below are stated at what the maker returned. They speak of the term under
`ReturnIsTheDescription` and `TableIsTheCommitters`: the term plays `descZ` and the committer's
table. `onlineFilling` is `OnlineProverParts.through` of the filling at which the kinds' laws are stated, so each
such law has to be carried through that wrapper; no such law is stated here. Served is a letter in
what follows: the value meant in every proposition is `ServedRequest` at the files
(E2E/CompleteAsIOPAtFiles.lean), the one set of the statements, and at an empty letter each of them
holds for nothing. -/

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open OnBytes (TableKey)
open VerifiableInference.Desc (Chain)
open P5J (TS)

/-- **The maker returns** where the verifier's test on the public files says yes. A set in scope is
read (`read_of_scope`, Johnson/LPFPol/LiveAtPolicy.lean). -/
def MakerReturns (files : VerifierAndGoals.PublicFiles) : Prop :=
  VerifierAndGoals.InScope files = true → FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true →
    ∃ returned, onlineMaker files = .ok returned

/-- **What the maker returned is the online description that the public part makes**: it is
`descZ` at the places and the first chain from which the filling lays its sides. `returned.F` is the
description of the verifier's decision, while the prover plays `descZ`, and its book is made of
`returned.F`: so this proposition is what ties the three. -/
def ReturnIsTheDescription (files : VerifierAndGoals.PublicFiles) : Prop :=
  VerifierAndGoals.InScope files = true → FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true →
  ∀ returned, onlineMaker files = .ok returned →
    ∃ places firstChain, H2U.placesOfMade returned.Z.made = .ok places ∧
      ProofFile.onlineFirstChainAt returned.Z = .ok firstChain ∧ returned.F = descZ returned.Z places firstChain

/-- **The shared chain's own sides are made**: where they are not, the filling lays none there. -/
def SharedSidesAreMade (publicPart : ProofFile.Pub) : Prop :=
  ∃ sides, nowSharedBy (matrixInput.weights publicPart) publicPart = .ok sides

/-- **The first chain's proximity test is laid.** -/
def FirstTestLaid (publicPart : ProofFile.Pub) (ground : Ground) : Prop :=
  (proxLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref).halves publicPart ground ≠ []

/-- **The test on the group U is made.** -/
def TestOnUMade (publicPart : ProofFile.Pub) : Prop :=
  K12.AtProof.halfU (matrixInput.weights publicPart)
    (fun w => Bind.ForProver.encW publicPart (matrixInput.weights publicPart w)) publicPart ≠ []

/-- **The test on the group Omega is made.** -/
def TestOnOmegaMade (publicPart : ProofFile.Pub) : Prop :=
  K12.AtProof.halfO (matrixInput.weights publicPart) publicPart ≠ []

/-- **The closings are laid.** -/
def ClosingsAreLaid (publicPart : ProofFile.Pub) (ground : Ground) : Prop :=
  (closeLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref).halves publicPart ground ≠ []

/-- **The last chain's test is made.** -/
def LastTestMade (publicPart : ProofFile.Pub) (ground : Ground) : Prop :=
  (secondW matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest publicPart ground :
    List (Placed _ _ Unit)) ≠ []

/-- **The sender of the message W is laid**: it lays nothing where the pile has one row. -/
def WSenderLaid (publicPart : ProofFile.Pub) (ground : Ground) : Prop :=
  (wLotAt (X := Unit) matrixInput OnBytes.secondHashFunction openHonest).halves publicPart ground ≠ [] ∧
    1 < publicPart.first.pendingRows

/-- **Every test and sender above is there, at a return of the maker.** -/
structure TestsAreLaid {files : VerifierAndGoals.PublicFiles} (returned : OnlineReturn files) : Prop where
  sharedSides : SharedSidesAreMade returned.Z
  closings : ClosingsAreLaid returned.Z returned.G
  first : FirstTestLaid returned.Z returned.G
  onU : TestOnUMade returned.Z
  onOmega : TestOnOmegaMade returned.Z
  last : LastTestMade returned.Z returned.G
  senderW : WSenderLaid returned.Z returned.G

/-- **The data of W read nothing of the pile but what its rows' g and psi say.** -/
def WDataIgnoresPlaceholders : Prop :=
  ∀ (p q : Pub → Ground → K13.PileOf Inst) (publicPart : Pub) (ground : Ground),
    (∀ instance₀ head, ((p publicPart ground instance₀ head).map fun row => (row.g, row.psi)) =
      (q publicPart ground instance₀ head).map fun row => (row.g, row.psi)) →
    K13.wDataAt p publicPart ground = K13.wDataAt q publicPart ground

/-- **The filling reads of the open functions claims, pile and keyOf alone.** -/
def OpenReadsPileAlone : Prop :=
  ∀ (O O' : OnlineProverArguments), O.claims = O'.claims → O.pile = O'.pile → O.keyOf = O'.keyOf →
    onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref O =
      onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref O'

end ProofFile.Honest.Term

namespace AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Cut AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open ProofFile.Honest (Local halvedAll rootedAll sealPlain)
open ProofFile.Honest.Term (OnlineReturn)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

local instance (priority := high) nonemptyPadAtStatements : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

variable {files : PublicFiles}

/-- **The table that the filling reads is the committer's**: the maker's key is the committer's, and
so are its stored columns, at item 0 and nowhere else. The online prover plays
`(cmAlong …).proverAt 0 returned.H`, with the committer's stored columns and key, while the test on
the group U and the threads that read `returned.H.storedWords` read the filling's: the two texts of
the table are one under this proposition alone. -/
def TableIsTheCommitters (returned : OnlineReturn files) : Prop :=
  returned.H.key = (cmAlong (AZ files) PadZ (holdZ files)).key ∧
    ∀ matrix coins item position, returned.H.stored matrix coins item position =
      if item == 0 then (cmAlong (AZ files) PadZ (holdZ files)).enc matrix coins position else none

/-- **No online side is missing**: every sub-protocol one of whose rounds sends something has its
side, every root that a round names is made, and the sealing round is plain. -/
def SidesAreWhole (returned : OnlineReturn files) : Prop :=
  halvedAll returned.F returned.H = true ∧ rootedAll returned.F returned.H = true ∧
    sealPlain returned.F = true

/-- **A served request has a trace**: at every request of the relation Served the index is in range
and the prover has a trace at what is written, at every out-of-domain sample. Served is a letter
here as in `refuseUnserved`, and what must hold is this proposition at one value: `ServedRequest`
at the files (E2E/CompleteAsIOPAtFiles.lean), the one set of the statements on completeness and
zero knowledge. At a free letter it can be false. -/
def TraceWhereServed (Served : FullSizeMatrix → LPFD.Full.XF → Prop) (returned : OnlineReturn files) : Prop :=
  ServesAt files returned.H Served

/-- **The offline description is the one that the verifier's seat makes**, wherever the test on the
public files says yes. -/
def OfflineDescriptionNamed (files : PublicFiles) : Prop :=
  protocolDataWellFormed (asDescriptionFiles files) = true →
    ∃ description, offlineDescription files = .ok description ∧
      KeySourced files description.source description.numbers description.later

/-- **No offline side is missing**, at the description that the public files make. -/
def OfflineSidesAreWhole (parts : Parts files) : Prop :=
  ∀ description, offlineDescription files = .ok description →
    halvedAll (keyFileDescription description.source description.numbers description.later)
        (parts.prover description) = true ∧
      rootedAll (keyFileDescription description.source description.numbers description.later)
        (parts.prover description) = true ∧
      sealPlain (keyFileDescription description.source description.numbers description.later) = true

/-- **The offline description has a test on the group Omega**, since the offline prover lays one. -/
def OfflineHasATestOnOmega (files : PublicFiles) : Prop :=
  ∀ description, offlineDescription files = .ok description → description.later.O.isSome = true

/-- **Each prover's external strings are the encodings of its private input.** -/
abbrev ExtEncAtTerm (files : PublicFiles) (parts : Parts files) : Prop :=
  OnBytes.WholeKey.ExtEnc (honestProvers files parts)

/-- **Some public files pass**: files at which the propositions above say something. -/
def SomeFilesPass : Prop := ∃ files, InScope files = true ∧ protocolDataWellFormed (asDescriptionFiles files) = true

/-- **The offline prover's senders stand at their places.** -/
def OfflineSendersAtTheirPlaces (parts : Parts files) : Prop :=
  ∀ description, offlineDescription files = .ok description →
    (AtPublicFiles.KeyLay.withTests parts.senders description.source description.numbers description.later
      (offlineTestParametersOnU description.later) (offlineTestOnOmega description.later) parts.rangeEntry
      parts.rangeGroups 0).AtPlaces

/-- **The offline prover's range is the online one's**, the test that a matrix holds an index, which
is the object's range (`Flat.InRange`). -/
def OfflineRangeIsTheCut (parts : Parts files) : Prop :=
  parts.senders.inRange = ProofFile.Honest.Term.matrixInput.inRange

/-- **How many run values there are.** A run value is a uniform coin of thirty-two bytes. -/
def RunValueCount : Prop := Fintype.card RunValue = 256 ^ 32

/-- **The matrix's reader and the index's reader agree**: where a matrix holds an index, the weights
that the kinds read off the matrix are the index's, so the trace, which goes through the index, and
the rows, which go through the matrix, speak of one table. -/
def MatrixReaderIsTheIndexReader : Prop :=
  ∀ (publicPart : ProofFile.Pub) (matrix : FullSizeMatrix) index,
    VerifiableInference.OnPublicFiles.Flat.indexOf matrix = some index →
      ProofFile.Honest.Term.matrixInput.weights publicPart matrix =
        ProofFile.Honest.fullIn.weights publicPart index

/-- **The input of a run at a served request**: the instance of a served request, with an
out-of-domain record made of the table's coins at some seed. -/
def ServedInput (Served : FullSizeMatrix → LPFD.Full.XF → Prop) (files : PublicFiles) (matrix : FullSizeMatrix)
    (tableCoins : (protocolAtFiles files).EncodingRandomness) (input : ProofFile.Inst) : Prop :=
  ∃ request seed, Served matrix request ∧
    input = LPFD.Full.instanceAsPlainRecord (request, (protocolAtFiles files).recOf matrix tableCoins seed)

/-- **The frame's run starts at every served request**: the prover's first half returns at every
coin, so its two private refusals, no trace and an index out of range, are not reached there. -/
def ReadyAtServedRequests (Served : FullSizeMatrix → LPFD.Full.XF → Prop) (returned : OnlineReturn files) :
    Prop :=
  ∀ matrix tableCoins input coins, ServedInput Served files matrix tableCoins input →
    ∃ first, ProofFile.Honest.ready returned.F returned.B returned.H matrix tableCoins input coins =
      .ok first

/-- **The description's test on the instance passes at every served input**, at every table coin and
seed. `ready` does not ask it: where it failed, the prover would play on at an input at which the
verifier refuses. -/
def OkStartAtServedRequests (Served : FullSizeMatrix → LPFD.Full.XF → Prop) (returned : OnlineReturn files) :
    Prop :=
  ∀ matrix tableCoins input, ServedInput Served files matrix tableCoins input →
    returned.F.okStart input = true

/-- **Only the kind K8 has a second stop**: the private stop set of the online prover is K8's
window, and what the refused value adds above this term. -/
def SecondStopsAreK8s (returned : OnlineReturn files) : Prop :=
  ∀ side ∈ returned.H.first ++ returned.H.second, side.place.kind ≠ .K8 →
    ∀ part ∈ side.parts, ∀ input front own, part.hid input front own = none

/-- **The first chain's proximity test has its public numbers**: the finish of the code switch is
there, and the test's parameters fit it, which among other things asks that the carrying message
has no mask row. Where it does not hold the test has no side. -/
def FirstTestFits (returned : OnlineReturn files) : Prop :=
  ∃ place, ProofFile.Honest.K12.AtProof.finishAt returned.Z returned.G = some place ∧
    ProofFile.Honest.K12.AtProof.fitsL (H2U.p12OfMade returned.Z.made) place = true

/-- **Where a run at a served request stands at the first chain's proximity test, its state on entry
is at hand**, so the default of that state is not taken. A run that a block in front has refused
does not stand there. -/
def FirstTestStateIsAtHand (Served : FullSizeMatrix → LPFD.Full.XF → Prop) (returned : OnlineReturn files) :
    Prop :=
  ∀ matrix tableCoins input coins challenges stand,
    ServedInput Served files matrix tableCoins input →
    challenges.due returned.F = true →
    ProofFile.Honest.silentAt returned.F returned.H matrix tableCoins input challenges = none →
    ProofFile.Honest.midAtW returned.F returned.B returned.H matrix tableCoins input coins challenges
      ⟨ProofFile.Honest.K12.AtProof.placeL, 0⟩ = .ok (some stand) →
    ∀ front : ProofFile.Honest.Front Unit, front.seen.rounds = stand.seen →
      ProofFile.Honest.K12.AtProof.atHandAtL returned.Z stand.st.input front = true

/-- **Where a run at a served request stands at the test on the group U, its state on entry is at
hand.** This refusal reads the stored table's columns, so it must never be taken there. -/
def TestOnUStateIsAtHand (Served : FullSizeMatrix → LPFD.Full.XF → Prop) (returned : OnlineReturn files) :
    Prop :=
  ∀ matrix tableCoins input coins challenges stand,
    ServedInput Served files matrix tableCoins input →
    challenges.due returned.F = true →
    ProofFile.Honest.silentAt returned.F returned.H matrix tableCoins input challenges = none →
    ProofFile.Honest.midSharedAtW returned.F returned.B returned.H matrix tableCoins input coins
      challenges ⟨ProofFile.Honest.K12.AtProof.placeU, 0⟩ = .ok (some stand) →
    ∀ front : ProofFile.Honest.Front Unit, front.seen.rounds = stand.seen →
      ProofFile.Honest.K12.AtProof.atHandAtU
        (fun index => Bind.ForProver.encW returned.Z
          (ProofFile.Honest.Term.matrixInput.weights returned.Z index))
        returned.Z (ProofFile.Honest.Common.thru id (ProofFile.Honest.Term.tableCoins files) stand.st.input)
        front = true

/-- **The head's public test says yes.** Where it does not, the kind K6 has no side. -/
def HeadFits (returned : OnlineReturn files) : Prop :=
  ProofFile.Honest.K6.headFitsB returned.Z returned.G = true

/-- **Every code switch has its public sizes.** -/
def SwitchesAreServedAndRoomy (returned : OnlineReturn files) : Prop :=
  ProofFile.Honest.K2.switchPlaces returned.Z returned.G ≠ [] ∧
    ∀ place ∈ ProofFile.Honest.K2.switchPlaces returned.Z returned.G,
      place.sizes.serves = true ∧ place.sizes.roomy = true

/-- **Every code switch's closing returns on public data.** -/
def ClosingIsOkAtEverySwitch (returned : OnlineReturn files) : Prop :=
  ∀ place ∈ ProofFile.Honest.K2.switchPlaces returned.Z returned.G,
    ProofFile.Honest.K2.closingOk ProofFile.Honest.K2.freshTable
      ((ProofFile.Honest.K2.segmentsOf returned.Z returned.G).take place.link) place = true

/-- **Every code switch's public test says yes at a served request.** -/
def PublicOkAtEverySwitch (Served : FullSizeMatrix → LPFD.Full.XF → Prop) (returned : OnlineReturn files) :
    Prop :=
  ∀ place ∈ ProofFile.Honest.K2.switchPlaces returned.Z returned.G,
    ∀ matrix tableCoins input, ServedInput Served files matrix tableCoins input →
      ProofFile.Honest.K2.publicOk returned.rows returned.G.first.layout place
        ((ProofFile.Honest.K2.segmentsOf returned.Z returned.G).take place.link) input = true

/-- **The first chain's test has stages that fit each other.** -/
def StagesAreOkAtTheFirstTest (returned : OnlineReturn files) : Prop :=
  ProofFile.Honest.K12.Light.StagesOk (H2U.p12OfMade returned.Z.made).nums.stages = true

/-- **A served request's covered positions are made.** -/
def RequestIsCoveredWhereServed (Served : FullSizeMatrix → LPFD.Full.XF → Prop)
    (returned : OnlineReturn files) : Prop :=
  ∀ matrix tableCoins input, ServedInput Served files matrix tableCoins input →
    ProofFile.Honest.K3.reqMadeB returned.Z input = true

/-- **A zero challenge of the second token sumcheck is refused by the verifier's block.** There is a
block of kind K4, the test on the challenge can fire there, and where it fires that block refuses,
at every state. This is why the prover may play on there. -/
def ZeroChallengeIsRefused (returned : OnlineReturn files) : Prop :=
  (∃ block ∈ returned.F.first.blocksInOrder, block.place.kind = .K4) ∧
    ∀ block ∈ returned.F.first.blocksInOrder, block.place.kind = .K4 →
      (∃ entry ∈ ProofFile.k4From returned.Z returned.G returned.G.built.toList 0 none, ∃ segment,
        ProofFile.Honest.K4.k4PubOf returned.Z entry.2 = some segment ∧
          ProofFile.Honest.K4.k4Place segment = block.place) ∧
      ∀ entry ∈ ProofFile.k4From returned.Z returned.G returned.G.built.toList 0 none, ∀ segment,
        ProofFile.Honest.K4.k4PubOf returned.Z entry.2 = some segment →
        ProofFile.Honest.K4.k4Place segment = block.place →
          (∃ own, ProofFile.Honest.drawsFit block.rounds own = true ∧
            (ProofFile.Honest.K4.k4CoinZero segment own).isSome = true) ∧
          ∀ firstTree state shown columns,
            (ProofFile.Honest.K4.k4CoinZero segment (shown.map (·.drawn))).isSome = true →
              ProofFile.Honest.judge firstTree block state shown columns = none

/-- **Every round of seeds declares its factors not to be 0**, and there is such a round. -/
def SeedRoundsAreMarked (returned : OnlineReturn files) : Prop :=
  (∃ declared ∈ returned.F.plans.1, Fmt.kindOf declared.entry.name = some .seeds) ∧
    ∀ declared ∈ returned.F.plans.1 ++ returned.F.plans.2.1 ++ returned.F.plans.2.2,
      Fmt.kindOf declared.entry.name = some .seeds → 0 < declared.entry.drawNZ

/-- **A challenge of the term's kit is one that its round can draw**: at the kit `ckP .two`, at
which the term stands, a draw that a round declares not to be 0 has a type without 0. -/
def ChallengesFitTheirRounds : Prop :=
  ∀ (declared : Fmt.DeclaredRound) (kind : Fmt.Kind), Fmt.kindOf declared.entry.name = some kind →
    declared.entry.drawNZ ≤ declared.entry.drawE →
    (kind = .seeds → 0 < declared.entry.drawNZ) →
    ∀ value : (_root_.Run.ckP .two).Ch declared.entry kind,
      ProofFile.Honest.drawFit declared ((_root_.Run.ckP .two).dr declared.entry kind value) = true

/-- **Rows of sides over the maker's prover meet `Owed` at the served requests.** `Owed` is the
premise of the rule on zero knowledge. By reading of `Good`, its fields `exact` and `fresh` are
where these duties of the coins would be shown, each at every sending: a tail for every row of every
oracle message, and every kept member anew at each sending; a pad for every sampled message, anew
at each sending; every mask entry that a ledger hands out; each fold's 2k + 1 coefficients; the
masking word, message and tails; no data on a pad's places; a later message that hangs on the
witness, the challenges and earlier coins only. Its field `acc`, outside the falls that `rows`
carries, is where every honest claim would be true; how wide these falls are is not said here, but
at each place of kind K4 they are meant to hold the zero challenge (`k4Fall`). Where the rows are
muted (`Sides.mute`) the fields `plays` and `acc` hold for nothing, so no statement on completeness
rests on this proposition. -/
def RowsAreOwed (Served : FullSizeMatrix → LPFD.Full.XF → Prop) (returned : OnlineReturn files)
    (rows : ProofFile.Honest.Sides returned.F returned.B FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey ProofFile.Honest.Cells Unit
      Unit) : Prop :=
  rows.prover returned.H = returned.H ∧
    ProofFile.Honest.Owed returned.F returned.B returned.H rows (ServedInput Served files)

end AtPublicFiles.AtFiles.HonestTerm

/-! ## 2 The run values

A run value is a coin of the prover: two of them at the offline prover, two at the online prover.
The maps here read them off a coin, where the public files make a prover; where they do not, the
prover sends the fixed messages and the maps return empty strings. -/

namespace AtPublicFiles.AtFiles.HonestTerm
open Iop Prob
open scoped ENNReal
open AtPublicFiles.Bridge AtPublicFiles.Cut
open ProofFile.Honest (Purse)
open ProofFile.Honest.Term (OnlineReturn onlineMaker familyOf)
open VerifiableInference.Desc (Chain)
open VerifierAndGoals (PublicFiles)
open P5J (TS)

variable {files : PublicFiles}

local instance (priority := high) nonemptyRunValueAtStatements : Nonempty RunValue :=
  ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValueAtStatements : Inhabited RunValue :=
  ⟨fun _ => 0⟩

/-- **The two run values of a file**, as bytes. -/
abbrev RunPair : Type := ByteArray × ByteArray

/-- The run values at the two slots of a coin of the frame. -/
def coinRuns {A B : Type} (coin : (A × RunValue) × (B × RunValue)) : RunPair :=
  (runValueBytes coin.1.2, runValueBytes coin.2.2)

/-- **What a coin of the online prover fixes**, at a return of the maker. -/
def onlineRunsAt (returned : OnlineReturn files) (places : H2U.Places4)
    (firstChain : Chain TS ProofFile.Cl) : (onlineProverAt returned places firstChain).Coin → RunPair :=
  coinRuns (A := Purse returned.B.shared) (B := Purse returned.B.first × Purse returned.B.second)

/-- **What a coin of the offline prover fixes**, at a description. -/
def offlineRunsAt (parts : Parts files) (description : OfflineDescription) :
    (offlineProverWithEncodedTable files (keyFileDescription description.source description.numbers description.later) parts.book
      (parts.prover description) runValueBytes runValueBytes (offlineStart description)).Coin →
      RunPair :=
  coinRuns (A := Purse parts.book.shared) (B := Purse parts.book.first × Purse parts.book.second)

/-- An online prover with the map that reads its coins. -/
structure OnlineWithRuns (files : PublicFiles) where
  family : Family (protocolAtFiles files).onlineBatch.loc (FullSizeMatrix × (protocolAtFiles files).EncodingRandomness × (protocolAtFiles files).OutOfDomainSeed)
  runs : family.Coin → RunPair

/-- An offline prover with the map that reads its coins. -/
structure OfflineWithRuns (files : PublicFiles) where
  prover : Honest (protocolAtFiles files).offline (FullSizeMatrix × (protocolAtFiles files).EncodingRandomness × (protocolAtFiles files).OutOfDomainSeed)
  runs : prover.Coin → RunPair

/-- The online prover, by the same match as `onlineProver`, with its map. -/
def onlineWithRuns (files : PublicFiles) : OnlineWithRuns files :=
  match onlineMaker files with
  | .ok returned =>
    match H2U.placesOfMade returned.Z.made, ProofFile.onlineFirstChainAt returned.Z with
    | .ok places, .ok firstChain =>
      ⟨onlineProverAt returned places firstChain, onlineRunsAt returned places firstChain⟩
    | _, _ => ⟨familyOf (filesAt files).fixedMessageProvers.hB.one, fun _ => (ByteArray.empty, ByteArray.empty)⟩
  | .error _ =>
    ⟨familyOf (filesAt files).fixedMessageProvers.hB.one, fun _ => (ByteArray.empty, ByteArray.empty)⟩

/-- The offline prover, by the same match as `offlineProver`, with its map. -/
def offlineWithRuns (parts : Parts files) : OfflineWithRuns files :=
  match offlineDescription files with
  | .ok description =>
    ⟨offlineProverWithEncodedTable files (keyFileDescription description.source description.numbers description.later) parts.book
      (parts.prover description) runValueBytes runValueBytes (offlineStart description),
      offlineRunsAt parts description⟩
  | .error _ => ⟨(filesAt files).fixedMessageProvers.hT, fun _ => (ByteArray.empty, ByteArray.empty)⟩

theorem onlineWithRuns_family (files : PublicFiles) :
    (onlineWithRuns files).family = onlineProver files := by
  unfold onlineWithRuns onlineProver
  generalize onlineMaker files = maker
  cases maker with
  | error _ => rfl
  | ok returned =>
    simp only
    generalize H2U.placesOfMade returned.Z.made = places
    generalize ProofFile.onlineFirstChainAt returned.Z = firstChain
    cases places <;> cases firstChain <;> rfl

theorem offlineWithRuns_prover (parts : Parts files) :
    (offlineWithRuns parts).prover = offlineProver parts := by
  unfold offlineWithRuns offlineProver
  generalize offlineDescription files = description
  cases description <;> rfl

/-- **The run values that a coin of the online prover fixes.** -/
def onlineRuns (files : PublicFiles) : (onlineProver files).Coin → RunPair :=
  onlineWithRuns_family files ▸ (onlineWithRuns files).runs

/-- **The run values that a coin of the offline prover fixes.** -/
def offlineRuns (parts : Parts files) : (offlineProver parts).Coin → RunPair :=
  offlineWithRuns_prover parts ▸ (offlineWithRuns parts).runs

/-- **Each run value is 32 zero bytes with chance at most 2^-256**, over a uniform coin. The
verifier refuses that one value (`Fmt.runOk`). -/
def RunsRarelyZero {Coin : Type} [Fintype Coin] [Nonempty Coin] (runs : Coin → RunPair) : Prop :=
  pr (unif Coin) {coin | Fmt.runOk (runs coin).1 = false} ≤ (2⁻¹ : ℝ≥0∞) ^ 256 ∧
    pr (unif Coin) {coin | Fmt.runOk (runs coin).2 = false} ≤ (2⁻¹ : ℝ≥0∞) ^ 256

end AtPublicFiles.AtFiles.HonestTerm

/-! ## 3 The places where a sender falls back on a fixed value

The online prover first. Where a function that a sender calls refuses, the sender sends the value
named here and does not stop. At a served request outside the stop sets each of these is meant never
to be taken; the statement on completeness needs that in any case. By reading, each refusal reads
public data and the view alone, but for those marked private. Some entries hold several places.

1. The maker, the places or the first chain refuse: the online prover sends the fixed messages
   (`MakerReturns`, `ReturnIsTheDescription`).
2. First chain's proximity test: zero rows and the zero message where `carryRows` refuses
   (`FirstTestFits`, `ClosingIsOkAtEverySwitch`).
3. The same test: the idle state where `atHandAtL` is false (`FirstTestStateIsAtHand`).
4. The same test: five steps of the verifier keep the state before them where they refuse
   (`TestJob.recB`), and four defaults stand above the state on entry (`lastOut`, `rowOf`, `aAns`,
   `aPoint`).
5. The shared chain: no side at all where `nowSharedBy` refuses (`SharedSidesAreMade`).
6. The test on the group U: a fall-back state where `atHandAtU` is false. PRIVATE: the refusal reads
   the stored table's columns (`TestOnUStateIsAtHand`).
7. The test on the group Omega: a fall-back state, and an empty array where the message o_u's shapes
   are not made.
8. The last chain's test: the idle state in `doorW`, and no side where `secondW`'s three functions
   refuse (`LastTestMade`).
9. The message W: no side where the pile has one row (`WSenderLaid`), and a value of no meaning in
   `K13.wDataAt` where the row data are not ready.
10. Kind K13: no row, or rows at default shapes, and 0 for a challenge that lacks.
11. Kind K11: no claim, default shapes, and 0 for a challenge without an element.
12. Kind K10: at each of the closings, the fold's words at empty tables where the ask refuses.
    PRIVATE, as typed: the ask takes the input and a carried coin.
13. Kind K2: a fold over the zero message, 0 in data where the rows' data are not ready, 0 for words
    of messages outside the sending, and a part that refuses at every coin where its public test
    fails (`SwitchesAreServedAndRoomy`, `PublicOkAtEverySwitch`).
14. Kind K4: mask entries over zeros where a maker yields nothing, and no side where the table test
    fails.
15. Kind K5: coins alone, or no side, where the named-point function refuses.
16. Kind K6: no side where the head's test fails (`HeadFits`). PRIVATE, as typed: the head's reader
    of the witness takes the input.
17. Every kind that pads: a list of values too short is padded with 0, one too long is cut. PRIVATE,
    as typed: the list of values may read the input.
18. Kind K1: 0 at a data place where the data are absent, no message where the test on the sending
    fails, tables of 0 where the trees are not made, and no side where the link's numbers refuse.
19. Kind K8: no message, or 0 in a stop's reading, where a list is shorter than it should be; zeros
    where a name of the matrices is no label; and digits lost where the layout does not seat them.
20. Kind K14: a default value beyond a count, and 0 in a committed table's row where that row's
    shape is not asked.
21. Kind K3: empty arrays where the covered positions are refused (`RequestIsCoveredWhereServed`),
    and 0 for an entry that the book does not lend.
22. The frame: where a request has no trace or the index is out of range, `ready` refuses, the
    strategy swallows that, and the prover plays on with no side. PRIVATE: these read the trace and
    the index (`ReadyAtServedRequests`, `TraceWhereServed`; outside the served requests the refused
    value of head line 9).

23. Behind a block of the verifier that refuses: each later round's fixed substitute. By reading,
    that is a function of the view.

The offline prover.

1. The public files make no description: the fixed messages (`OfflineDescriptionNamed`).
2. `offlineTestOnOmega`'s default where the description has no such test (`OfflineHasATestOnOmega`).
3. The idle state in `doorKW`, and the defaults in the two tests of the shared chain
   (E2E/KeyPartsHalves.lean).

The coins. The message of the group Omega is opened at the test on that group and again at the last
chain's test (said here without a theorem).

These stand in the text and reach no message: at the proximity tests' first part 0 for the switches'
coins and for a fresh table's tails that another part sent; the pile's mask form and target
(`WDataIgnoresPlaceholders`); the words of the closings' filler; the open functions' `req`, `cells`
and `enc` (`OpenReadsPileAlone`).

At the first chain's proximity test the carried mask table and its tails are 0 at every run, and no
message stands behind them: the carrying message has no mask row (the verifier's text: `reqGroupAt`,
OnBytes/Iop/Req.lean, and `switchTargetCheck`, OnBytes/Iop/Cs.lean; the prover's: `FirstTestFits`),
and the fresh table that masks the fold comes from the coins (`TestJob.first`).

Challenges. The senders do not test that a seed's factor is not 0: they rest on
`ChallengesFitTheirRounds`, and on each round of seeds declaring its factors not to be 0.
-/
