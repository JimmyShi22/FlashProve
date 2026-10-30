-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/TheHonestProverNotTaken.lean: for the fixed values that the honest prover's term lays, the
propositions that say that they are not taken at a served run, or are not sent.

1. The term is E2E/TheHonestProver.lean. Its senders fall back on fixed values where a function that
   they call refuses. A statement on completeness is about the protocol's prover only where no
   fall-back fires. For zero knowledge it is enough that whether one is taken is a function of the
   view and the simulator is exact on both arms, or that it is taken only inside the private stops.
2. Each proposition here speaks of a stand that exists: a run that a block in front has refused has
   no stand there. None says that a stand exists: that half is completeness's.
3. Some propositions stand in E2E/TheHonestProverStatements.lean.

4. In other files, over PlayedAt and StandsAtServed where they need a stand:
   K5RowWhole; LookupRowIsWholeAtServedRuns and KeyPointsAreTheLookupsOwnAtServedRuns; K14's
   K14RowIsWholeAtServedRuns. Stated in words alone: that carryRows
   returns at a stand at the first test, which is the fall-back's own guard for zero rows;
   RowDataCoversTheLayout, that the rows lay an element at every place of every sending's layout;
   padTo and challengesOr0 at the other kinds.
5. This file proves nothing.
-/
import E2E.TheHonestProverStatements
import Johnson.Desc.ProofFile.Honest.K12.AtProof.AtHandW

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm
open OnBytes (TableKey)
open ProofFile.Honest (Local Common Front Seen)
open ProofFile.Honest.K12.Light (atHandOf colsOpened)
open ProofFile.Honest.Term (OnlineReturn)
open VerifiableInference.Desc (Chain)
open VerifierAndGoals (PublicFiles)
open P5J (TS)

variable {files : PublicFiles}

/-- **What the term plays at these letters**: the places and first chain that the public part
makes. -/
structure PlayedAt (returned : OnlineReturn files) (places : H2U.Places4)
    (firstChain : Chain TS ProofFile.Cl) : Prop where
  places : H2U.placesOfMade returned.Z.made = .ok places
  chain : ProofFile.onlineFirstChainAt returned.Z = .ok firstChain

/-- **A run at a served request stands at an address**: the premises of the propositions below. -/
def StandsAtServed (Served : FullSizeMatrix → LPFD.Full.XF → Prop) (returned : OnlineReturn files)
    (places : H2U.Places4) (firstChain : Chain TS ProofFile.Cl) (matrix : FullSizeMatrix)
    (tableCoins : (protocolAtFiles files).EncodingRandomness) (input : ProofFile.Inst) (challenges : ProofFile.Honest.Draws) : Prop :=
  ServedInput Served files matrix tableCoins input ∧
    challenges.due (descZ returned.Z places firstChain) = true ∧
    ProofFile.Honest.silentAt (descZ returned.Z places firstChain) returned.H matrix tableCoins input
      challenges = none

/-- **Where such a run stands at the last chain's test, its state on entry is at hand.** -/
def LastTestStateIsAtHand (Served : FullSizeMatrix → LPFD.Full.XF → Prop) (returned : OnlineReturn files)
    (places : H2U.Places4) (firstChain : Chain TS ProofFile.Cl) : Prop :=
  PlayedAt returned places firstChain →
  ∀ matrix tableCoins input coins challenges stand,
    StandsAtServed Served returned places firstChain matrix tableCoins input challenges →
    ProofFile.Honest.midAtW (descZ returned.Z places firstChain) returned.B returned.H matrix tableCoins
      input coins challenges ⟨ProofFile.Honest.K12.AtProof.placeW, 0⟩ = .ok (some stand) →
    ∀ front : Front Unit, front.seen = stand.shown →
      ProofFile.Honest.K12.AtProof.atHandW (descZ returned.Z places firstChain) (·.x)
        VerifiableInference.Desc.K12.Seat.enterOwn ProofFile.Honest.K12.AtProof.placeW stand.st.input
        front = true

/-- The test that the state on entry at the test on the group Omega is at hand, at `doorOmegaF`'s
letters. The library's `atHandAtO` stands for it. False where the public letters are not
made. -/
def atHandAtOmega {W₀ X : Type} (publicPart : ProofFile.Pub) (input : Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey)
    (front : Front X) : Bool :=
  ((ProofFile.Honest.K12.AtProof.four publicPart).bind fun four =>
    (ProofFile.Honest.K12.AtProof.sendPub publicPart).bind fun send =>
      (_root_.Desc.K14.blocks send.P).map fun blocks =>
        atHandOf (blocks ++ [VerifiableInference.Desc.K12.Seat.onGu
            (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts four.U)])
          (fun w : Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey =>
            _root_.Desc.K14.first send.P.codes w.key)
          (VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none) colsOpened input
          front).getD false

/-- **Where such a run stands at the test on the group Omega, its state on entry is at hand.** -/
def TestOnOmegaStateIsAtHand (Served : FullSizeMatrix → LPFD.Full.XF → Prop) (returned : OnlineReturn files)
    (places : H2U.Places4) (firstChain : Chain TS ProofFile.Cl) : Prop :=
  PlayedAt returned places firstChain →
  ∀ matrix tableCoins input coins challenges stand,
    StandsAtServed Served returned places firstChain matrix tableCoins input challenges →
    ProofFile.Honest.midSharedAtW (descZ returned.Z places firstChain) returned.B returned.H matrix
      tableCoins input coins challenges ⟨ProofFile.Honest.K12.AtProof.placeO, 0⟩ = .ok (some stand) →
    ∀ front : Front Unit, front.seen = stand.shown →
      atHandAtOmega returned.Z
        (ProofFile.Honest.Common.thru id (ProofFile.Honest.Term.tableCoins files) stand.st.input) front = true

/-- **The filler's parameter of the pile's claims is read by nothing**: any value gives the same
pile. -/
def Q0IsIdle (returned : OnlineReturn files) : Prop :=
  ∀ firstChain head other, ProofFile.onlineFirstChainAt returned.Z = .ok firstChain →
    ProofFile.Honest.K13.pileAtChain firstChain returned.Z head (ProofFile.Honest.K13.q0Idle returned.Z) =
      ProofFile.Honest.K13.pileAtChain firstChain returned.Z head other

/-- **Every link's group has its plan**, so that the blank plan is not read. -/
def LayersPlansAreThere (returned : OnlineReturn files) : Prop :=
  ∀ segment, segment < returned.Z.p.built.links.size →
    (returned.Z.p.X.G[ProofFile.Honest.K13.groupOfSeg returned.Z segment]?).isSome = true

/-- **The pile has a row for every site** at each place that reads it: where one site's row cannot
be made there is no row at all. -/
def PileIsMade (Served : FullSizeMatrix → LPFD.Full.XF → Prop) (returned : OnlineReturn files)
    (places : H2U.Places4) (firstChain : Chain TS ProofFile.Cl) : Prop :=
  PlayedAt returned places firstChain →
  ∀ matrix tableCoins input coins challenges stand address,
    address = (⟨⟨1, none, 3, .K13⟩, 1⟩ : ProofFile.Honest.Addr) ∨
      address = ⟨⟨1, none, 4, .K1⟩, 0⟩ ∨ address = ⟨ProofFile.Honest.K12.AtProof.placeW, 0⟩ →
    StandsAtServed Served returned places firstChain matrix tableCoins input challenges →
    ProofFile.Honest.midAtW (descZ returned.Z places firstChain) returned.B returned.H matrix tableCoins
      input coins challenges address = .ok (some stand) →
    (ProofFile.Honest.openHonest.pile returned.Z returned.G stand.st.input.x
      stand.st.heard).length = (ProofFile.Honest.K13.mergeSitesOf firstChain returned.Z).length

/-- **W's data read a pile of a row for every site**, at the list that they hand the filler. -/
def PileIsMadeAtTheListOfW (Served : FullSizeMatrix → LPFD.Full.XF → Prop) (returned : OnlineReturn files)
    (places : H2U.Places4) (firstChain : Chain TS ProofFile.Cl) : Prop :=
  PlayedAt returned places firstChain →
  ∀ matrix tableCoins input coins challenges stand address,
    address = (⟨⟨1, none, 4, .K1⟩, 0⟩ : ProofFile.Honest.Addr) ∨
      address = ⟨ProofFile.Honest.K12.AtProof.placeW, 0⟩ →
    StandsAtServed Served returned places firstChain matrix tableCoins input challenges →
    ProofFile.Honest.midAtW (descZ returned.Z places firstChain) returned.B returned.H matrix tableCoins
      input coins challenges address = .ok (some stand) →
    (ProofFile.Honest.openHonest.pile returned.Z returned.G stand.st.input.x
      (ProofFile.Honest.K13.wFront returned.Z.first.lin (ProofFile.Honest.K13.wHeard returned.Z)
        stand.st.heard)).length = (ProofFile.Honest.K13.mergeSitesOf firstChain returned.Z).length

/-- **The verifier's state in front of a closing is made at a run at a served request**, so the
filler returns and `stAtZero_at_closing` says what it returns. The stand lies in front of the round
"BAT", which is the first move of the closing's one part. -/
def ClosingStatementsAreAtHand (Served : FullSizeMatrix → LPFD.Full.XF → Prop) (returned : OnlineReturn files)
    (places : H2U.Places4) (firstChain : Chain TS ProofFile.Cl) : Prop :=
  PlayedAt returned places firstChain →
  ∀ segment where_ parameters block, segment < 25 →
    ProofFile.Honest.K10.Tied firstChain returned.Z segment where_ parameters block →
    ∀ matrix tableCoins input coins challenges stand,
      StandsAtServed Served returned places firstChain matrix tableCoins input challenges →
      ProofFile.Honest.midAtW (descZ returned.Z places firstChain) returned.B returned.H matrix
        tableCoins input coins challenges ⟨block.place, 0⟩ = .ok (some stand) →
      ∃ columns state, ProofFile.Honest.K10.frontState 0 firstChain.blocksInOrder
        (ProofFile.startS returned.Z input.pub) block.place stand.seen columns = .ok state

/-- **At such a stand the closing's ask speaks**, so `bareAsk` is not taken, at every challenge of
the form that the block's first declared round, "BAT", draws. job: the job that the term lays at the
parameters, which is `lotJob`. The carried coins are every value, as in the library's
`ask_made_at_head` (Johnson/Desc/ProofFile/Honest/K10/Wipe/Speaks.lean). -/
def ClosingDataAreMade (Served : FullSizeMatrix → LPFD.Full.XF → Prop) (returned : OnlineReturn files)
    (places : H2U.Places4) (firstChain : Chain TS ProofFile.Cl)
    (job : VerifiableInference.Desc.First.Close.Par →
      ProofFile.Honest.K10.CloseJob (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst ProofFile.Honest.Cells)) : Prop :=
  PlayedAt returned places firstChain →
  ∀ segment where_ parameters block, segment < 25 →
    ProofFile.Honest.K10.Tied firstChain returned.Z segment where_ parameters block →
    ∀ matrix tableCoins input coins challenges stand,
      StandsAtServed Served returned places firstChain matrix tableCoins input challenges →
      ProofFile.Honest.midAtW (descZ returned.Z places firstChain) returned.B returned.H matrix
        tableCoins input coins challenges ⟨block.place, 0⟩ = .ok (some stand) →
      ∀ drawn : Fmt.Drawn, ProofFile.Honest.drawsFit (block.rounds.take 1) [drawn] = true →
        ∀ masks carried, ∃ ask,
          ProofFile.Honest.K10.closeAsk (job parameters) stand.st.input stand.shown stand.st.heard drawn
            masks carried = .ok (some ask)

/-- **What the closing hands to the fold reads no target**: it is the same at two statements that
agree once their targets are wiped. -/
def ClosingAskReadsNoTarget : Prop :=
  ∀ {W X : Type} (job : ProofFile.Honest.K10.CloseJob W) (other : W → Seen → List Fmt.Drawn →
            Except String (OnBytes.Statement × Nat)),
    (∀ input seen heard,
      (job.stAt input seen heard).map (fun y => (ProofFile.Honest.K10.wipeSt y.1, y.2)) =
        (other input seen heard).map fun y => (ProofFile.Honest.K10.wipeSt y.1, y.2)) →
    ∀ number coins seen (state : ProofFile.Honest.State W X),
      ProofFile.Honest.K10.closeAskAt job number coins seen state =
        ProofFile.Honest.K10.closeAskAt { job with stAt := other } number coins seen state

/-- **Row data are ready**: at a stand of such a run, where enough challenges have been heard for a
message's data, the filling's own test says yes. It speaks to the zeros of an unready message, and
it holds of `RowData.empty`: that no message is left to that value is a further sentence, on
`lays`, which is named in the head. -/
def RowDataIsReady (Served : FullSizeMatrix → LPFD.Full.XF → Prop) (returned : OnlineReturn files)
    (places : H2U.Places4) (firstChain : Chain TS ProofFile.Cl) : Prop :=
  PlayedAt returned places firstChain →
  ∀ matrix tableCoins input coins challenges address stand,
    StandsAtServed Served returned places firstChain matrix tableCoins input challenges →
    ProofFile.Honest.midAtW (descZ returned.Z places firstChain) returned.B returned.H matrix tableCoins
      input coins challenges address = .ok (some stand) →
    ∀ message, (returned.rows input).heardOk message stand.st.heard.length = true →
      (returned.rows input).readyAt stand.st.heard message = true

/-- **Muted rows of sides meet `Owed` at the served requests**, which is what the statements on zero
knowledge take. Alone it can be met emptily, since `plays` and `acc` are idle on muted rows: it is
quoted only beside the statement on acceptance at the same rows, and at a served set that is not
empty. -/
def RowsAreOwedMuted (Served : FullSizeMatrix → LPFD.Full.XF → Prop) (returned : OnlineReturn files)
    (rows : ProofFile.Honest.Sides returned.F returned.B FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey ProofFile.Honest.Cells Unit
      Unit) : Prop :=
  rows.prover returned.H = returned.H ∧
    ProofFile.Honest.Owed returned.F returned.B returned.H rows.mute (ServedInput Served files)

end AtPublicFiles.AtFiles.HonestTerm
