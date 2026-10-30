-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/AttentionSimulatorAtTheTerm.lean: the simulator of the attention segments' own rounds (kind K5:
the label of that sub-protocol in the description) at a return of the maker from which the online
prover of E2E/TheHonestProver.lean is made: its sides, its book and its description. Nothing here is
about onlineProversOfCommitter, its coins' type or refuseUnserved. This file proves nothing: every proposition in it
is a definition of type Prop.

1. attentionRows is the lot of rows of the kind: each part beside its simulator, with the letters
   On := True and bud := no position is read. It is a value of SLot.
2. AttentionLotIsTheFillingsOwn says that this lot, simulators left off, is the filling's lot of this
   kind, read through. AttentionSidesAreTheRows says of a return of the maker that each row's half is
   among the prover's sides, and each side of this kind is a row's half. It says nothing on order or
   on how often; the statement's count does.
3. The statement is two structures at a return of the maker. AttentionLaw: twelve rows at twelve
   places; a side at each; Good at each side; and the facts that say what a part and a simulator of the
   kind read and tell. AttentionBook: what the book lends this kind, and from whom.
4. Good stands at every A that holds nowhere, and every B, so its fields plays and acc are met for
   nothing here: of Good this file is about fits, exact and fresh, which are what the rule that joins
   the sides reads (Honest/Law/OwedRule.lean, head, (7); Honest/Law/Rule/Row.lean, head).
   What the parts pass on is of type Unit: nothing is handed on. What was shown stands in m.seen.
4a. Of the structure Owed (Honest/Owed.lean) this file states, at this kind's rows: seats; good; of
   owed the clause on bud, the clause on On, and that the carried blocks are lent. It does not state
   runs, nor that the walk has a state before a called part: these hang on the kind's playing at its
   borders (PlaysS and its kin, Honest/Thread/PaysS.lean) and on ready's return. Until these stand at
   the same return of the maker this statement alone does not give Owed at these rows.
5. The field exact is asked at every state m, and m.st.input holds the index and the stored tables'
   pads and encoding randomness. So it is asked at each fixed value of them. ExactAtOneTable writes
   that out, and it follows from the field. The field speaks of one part at a time, with all else
   fixed before the coins. It holds the blocks that the part spends as uniform and independent; that
   they are so in a run is not stated here. OwnerFresh, owed beside, is the owner's condition for it:
   until it stands, exact here is the spender's half.
6. The field fresh is about a part's own coins. The statement asks ownsNothing: where that holds, the
   field says nothing at this kind.
7. The statement asks that the book passes its tests and that each entry which hands coins to a part
   of this kind is marked as spent. Entries marked as carried may hand the same coins to later parts.
   This file does not speak of those parts; what their condition On will ask of what this kind has
   sent is not stated here.
8. AttentionAtTheTermHolds is the sentence to prove: its premises are the maker's return and the
   library's head. Owed beside it, each under its own name: AttentionPremisesMeet (without it the
   sentence may hold of nothing; it speaks where some public files pass, which T1's SomeFilesPass
   names) · OwnerFresh and AttentionOwnersAreSwitches (the owner's debt, with its address) · CarrierTie
   and AttentionCarriersAreAt (the debt to the parts that carry these coins, with its address) ·
   AttentionEndFactorIsNotZero (the one guard on a drawn value) · AttentionExactIsLive and
   AttentionShowsSome (the field's premises can meet, and where they do something is shown) ·
   AttentionHandsToTheRule (this form is what the rule that joins the kinds takes). Files beside this
   one prove those that they name, at this return; this file imports none of them.
9. The field exact is asked at lists of challenges that fit. AttentionEndFactorIsNotZero says that at
   such a list the factor on the end values' mask entries is not 0 in the field: at 0 an end value
   would go out as it is. A test beside this file shows that the field fails there.
10. The rows here stand at the online filling's types, the lot read through. The same law with the
   filling and the types free stands in Honest/K5/Law/AttentionAtAFilling.lean.
11. Each row's half is the half of the side seated from it (Side.half: one list of parts). No two
   blocks of the description stand at one place: the library's head gives that test (placesOk).
   That the sumcheck's message leaves one coefficient out is what the shapes of the rounds say.

No property is claimed. Nothing is claimed on soundness, completeness or hiding.
-/
import E2E.TheHonestProver
import Johnson.Desc.ProofFile.Honest.K5.Law.SLotRows
import Johnson.Desc.ProofFile.Honest.K5.Law.NoneSeen5
import Johnson.Desc.ProofFile.Honest.K5.Law.ExactAtOneTable
import Johnson.Desc.ProofFile.Honest.K5.Law.Script
import Johnson.Desc.ProofFile.Honest.K5.Law.AttentionScript
import Johnson.Desc.ProofFile.Honest.K5.Law.AttentionEndFactor
import Johnson.Desc.ProofFile.Honest.K2.Exact

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm.Attention
open AtPublicFiles.Cut
open OnBytes.Model (Reading)
open ProofFile.Honest ProofFile.Honest.K5
open ProofFile.Honest.Term (OnlineReturn onlineMaker onlineFilling tableCoins)
open VerifiableInference.Desc (Chain Place)
open P5J (AtMgA TS)

/-- **The online prover's input** at three public files. -/
abbrev OnlineInput (files : VerifierAndGoals.PublicFiles) : Type := Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Cells

/-- **The rows of the attention segments' own rounds at the online prover**, each part beside its
simulator, at the reader of key points that the filling names. -/
abbrev attentionRows (files : VerifierAndGoals.PublicFiles) :
    SLot (OnlineInput files) (OnlineInput files) Unit ProofFile.Inst :=
  k5SLot (W₀ := FullSizeMatrix) (Rc := (protocolAtFiles files).EncodingRandomness) (Xi := ProofFile.Inst) (X := Unit) (Pb := ProofFile.Inst) id keyOfK3

/-- **The lot is a lot of the filling.** -/
def AttentionLotIsInTheFilling (files : VerifierAndGoals.PublicFiles) : Prop :=
  (attentionRows files).toHLot ∈ (onlineFilling files).lots

/-- **The lot is the filling's own lot of this kind, read through.** -/
def AttentionLotIsTheFillingsOwn (files : VerifierAndGoals.PublicFiles) : Prop :=
  (attentionRows files).toHLot =
    HLot.thru (Local.thru id (tableCoins files)) (Local.thru id (tableCoins files))
      (k5LotK (W₀ := FullSizeMatrix) (Rc := IndexCommitterCoins) (Xi := ProofFile.Inst) (X := Unit) id openHonest.keyOf)

variable {files : VerifierAndGoals.PublicFiles}

/-- The rows at a return of the maker. -/
abbrev attentionRowsAt (returned : OnlineReturn files) :
    List (Unlettered (OnlineInput files) (OnlineInput files) Unit ProofFile.Inst) :=
  (attentionRows files).rows returned.Z returned.G

/-- **Each row's half is among the prover's sides, and each side of this kind is a row's half.** -/
def AttentionSidesAreTheRows (returned : OnlineReturn files) : Prop :=
  (∀ r ∈ attentionRowsAt returned, r.half ∈ returned.H.first) ∧
    ∀ h ∈ returned.H.first, h.place.kind = .K5 →
      ∃ r ∈ attentionRowsAt returned, h = r.half

/-- **Whose coins the rows spend**: the owners' addresses, read off the book. -/
def attentionOwners (returned : OnlineReturn files) : List Addr :=
  (returned.B.ahead.filter fun e =>
    (attentionRowsAt returned).any fun r => r.place == e.spender.place).map (·.owner)

/-- **The law of the rows at a return of the maker.** -/
structure AttentionLaw (returned : OnlineReturn files) : Prop where
  /-- the rows' halves and the prover's sides of this kind; it follows from count -/
  sides : AttentionSidesAreTheRows returned
  /-- in the prover's list, the sides of this kind are the rows' halves, in order and in number -/
  count : (returned.H.first.filter fun h => decide (h.place.kind = .K5)) =
    (attentionRowsAt returned).map (·.half)
  /-- one row at each of the twelve attention segments: the library's head pins that number -/
  twelve : (attentionRowsAt returned).length = 12
  /-- twelve places, of this kind, each with a part -/
  places : ((attentionRowsAt returned).map (·.place)).Nodup ∧
    ∀ r ∈ attentionRowsAt returned, r.place.kind = .K5 ∧ r.row ≠ []
  /-- the blocks of this kind in the description are at the rows' places, in the first chain alone -/
  kindPlaces : (∀ b ∈ returned.F.first.blocksInOrder, b.place.kind = .K5 →
      ∃ r ∈ attentionRowsAt returned, r.place = b.place) ∧
    (∀ b ∈ returned.F.shared.blocksInOrder, b.place.kind ≠ .K5) ∧
    (∀ b ∈ returned.F.second.blocksInOrder, b.place.kind ≠ .K5) ∧
    (∀ h ∈ returned.H.shared, h.place.kind ≠ .K5) ∧ ∀ h ∈ returned.H.second, h.place.kind ≠ .K5
  /-- On, as the rule's premise on it asks: it holds at all arguments -/
  on : ∀ r ∈ attentionRowsAt returned, ∀ u ca m front, r.On u ca m front
  /-- at each row: a side; Good at it, at every list of declared rounds and all falls; and what its
  members read and tell -/
  rows : ∀ r ∈ attentionRowsAt returned,
    (∃ σ, Side.seated returned.F.first.blocksInOrder r.place r.row [] = some σ) ∧
    ∀ (falls : List (Fall returned.F.S₁)) σ,
      Side.seated returned.F.first.blocksInOrder r.place r.row falls = some σ →
      (∀ pre (P Q : Coins returned.B → returned.F.S₁ → Mid (OnlineInput files) Unit → Env → Prop),
        (∀ k s m E, ¬ P k s m E) →
        Good pre .own σ returned.B (orderOf returned.F) 0 0 P Q r.On r.bud) ∧
      (∀ pre, ExactAtOneTable σ r.On r.bud pre) ∧
      ∀ u ∈ σ.members,
        u.part.takes = ⟨0, 0⟩ ∧ u.part.carries = [] ∧ HasNoStop u.part ∧
        ReadsTheTraceAlone u.part ∧ u.part.readsNoneSeen ∧ ReadsItsCoinsAlone u.sim ∧
        TellsItsCoins u.sim (u.rounds.map fun x => (x.1.items.filter (· != .root)).length) ∧
        ∀ (tree : Nat → List Nat) (n : Nat) (ds : List Fmt.Drawn),
          r.bud u.number ds (asksFrom tree (u.rounds.map (·.2.length)) n)

/-- **What the book does at the rows, at a return of the maker.** -/
structure AttentionBook (returned : OnlineReturn files) : Prop where
  /-- the book is the maker's, and it passes its own tests at the description -/
  book : returned.B.word returned.F = none
  /-- no entry of the book has its owner at a row's place -/
  ownsNothing : ∀ r ∈ attentionRowsAt returned, ∀ e ∈ returned.B.ahead, e.owner.place ≠ r.place
  /-- every entry that hands coins to a part of a row marks them as spent -/
  spentOnly : ∀ r ∈ attentionRowsAt returned, ∀ e ∈ returned.B.ahead,
    e.spender.place = r.place → e.once = true
  /-- every entry whose spender stands at a place of this kind has it at a row's place -/
  spendersAreRows : ∀ e ∈ returned.B.ahead, e.spender.place.kind = .K5 →
    ∃ r ∈ attentionRowsAt returned, e.spender.place = r.place
  /-- each owner of coins that this kind spends is a part of a side of the prover -/
  owners : ∀ a ∈ attentionOwners returned,
    ∃ h ∈ returned.H.first, h.place = a.place ∧ a.part < h.parts.length
  /-- at every run's coins the book lends each row what it spends -/
  lent : ∀ (k : Coins returned.B), ∀ r ∈ attentionRowsAt returned,
    ∃ c, lendRow returned.B (returned.B.rowsOf 0) (k.look 0) r.place r.half.parts 0 = .ok c
  /-- at every run's coins the book gives each member its carried blocks, which are none -/
  carried : ∀ (k : Coins returned.B), ∀ r ∈ attentionRowsAt returned, ∀ σ,
    Side.seated returned.F.first.blocksInOrder r.place r.row [] = some σ → ∀ u ∈ σ.members,
      ∃ ca, carriedAt returned.B k 0 ⟨r.place, u.number⟩ u.part = .ok ca

/-- **OWED BESIDE: the owners' debt.** For each entry of the book marked as spent that hands coins to a
part of a row: the owner stands at a switch's place, the prover has a side there, and the field fresh
of that owner holds toward that part, at the switch's own bound on positions. Whatever simulators
stand in the side: the field reads none. -/
def OwnerFresh (returned : OnlineReturn files) : Prop :=
  ∀ e ∈ returned.B.ahead, e.once = true →
    (∃ r ∈ attentionRowsAt returned, e.spender.place = r.place) →
    ∃ p ∈ K2.switchPlaces returned.Z returned.G, p.place = e.owner.place ∧
      ∃ σ : Side returned.F.S₁ returned.F.Cl (OnlineInput files) (OnlineInput files) Unit ProofFile.Inst,
        σ.block ∈ returned.F.first.blocksInOrder ∧ σ.half ∈ returned.H.first ∧
        σ.block.place = e.owner.place ∧ ∃ u ∈ σ.members, u.number = e.owner.part ∧
          FreshToward .own σ returned.B (orderOf returned.F) (K2.switchBud p) u e.spender

/-- **OWED BESIDE: the address of that debt**: each owner stands at a code switch. A file beside this
one holds it at this return, with the link. -/
def AttentionOwnersAreSwitches (returned : OnlineReturn files) : Prop :=
  ∀ a ∈ attentionOwners returned, a.place.kind = .K2

/-- **OWED BESIDE: whose coins the rows spend.** What a row spends, in order, is the entries of the book
that name its parts, each the owner's coins from the entry's start on. This is the lending's own text
at any book; with AttentionShowsItsScript it says what the owner's coins became. -/
def AttentionSpentAreTheOwnersCoins (returned : OnlineReturn files) : Prop :=
  ∀ (k : Coins returned.B), ∀ r ∈ attentionRowsAt returned, ∀ c,
    lendRow returned.B (returned.B.rowsOf 0) (k.look 0) r.place r.half.parts 0 = .ok c →
    ProofFile.Honest.K5.spentOf r.half.parts c =
      ((List.range r.half.parts.length).flatMap fun j =>
        returned.B.ahead.filter fun e => e.spender == (⟨r.place, j⟩ : Addr) && e.once).flatMap
        fun e => (((k.look 0 e.owner).2.cut e.start e.count).map coinsE).getD []

/-- **OWED BESIDE: what each member shows at the coins it is handed**, by the library's own functions.
It speaks of the seat of which the lot made the row, and not of every seat with an equal row: the
script is written at that seat's jobs. -/
def AttentionShowsItsScript (returned : OnlineReturn files) : Prop :=
  ∀ r ∈ attentionRowsAt returned,
    ∀ σ : Side returned.F.S₁ returned.F.Cl (OnlineInput files) (OnlineInput files) Unit ProofFile.Inst,
      Side.seated returned.F.first.blocksInOrder r.place r.row [] = some σ →
      ∃ y ∈ H2K5.k5Places returned.G, ∃ Y : Seat5,
        seatAtK keyOfK3 returned.Z returned.G y.1 y.2.1 y.2.2 = some Y ∧ r = r5 id Y ∧
        ∀ j s, (H2K5.Honest.shapes Y.P.x)[j]? = some s → ShowsItsScript id Y σ j s

/-- **OWED BESIDE: the tie to the parts that carry these coins**: whose coins the rows spend, and what
each member shows at them. -/
def CarrierTie (returned : OnlineReturn files) : Prop :=
  AttentionSpentAreTheOwnersCoins returned ∧ AttentionShowsItsScript returned

/-- The addresses that carry the coins of an owner of this kind's coins. -/
def attentionCarriers (returned : OnlineReturn files) : List Addr :=
  (returned.B.ahead.filter fun e =>
    !e.once && (attentionOwners returned).contains e.owner).map (·.spender)

/-- **OWED BESIDE: the address of the debt to them.** These three kinds are read off the text of the
book's maker; nothing holds them at this book yet. -/
def AttentionCarriersAreAt (returned : OnlineReturn files) : Prop :=
  ∀ a ∈ attentionCarriers returned, a.place.kind = .K2 ∨ a.place.kind = .K10 ∨ a.place.kind = .K12

/-- **OWED BESIDE: at challenges that fit, the factor on a sumcheck's end entries is not 0.** -/
def AttentionEndFactorIsNotZero (returned : OnlineReturn files) : Prop :=
  ∀ r ∈ attentionRowsAt returned,
    ∀ σ : Side returned.F.S₁ returned.F.Cl (OnlineInput files) (OnlineInput files) Unit ProofFile.Inst,
      Side.seated returned.F.first.blocksInOrder r.place r.row [] = some σ →
      ∃ y ∈ H2K5.k5Places returned.G, ∃ Y : Seat5,
        seatAtK keyOfK3 returned.Z returned.G y.1 y.2.1 y.2.2 = some Y ∧ r = r5 id Y ∧
        ∀ u ∈ σ.members, ∀ k, (H2K5.Honest.shapes Y.P.x)[u.number]? = some (.sum k) → ∀ ds,
          drawsFit (u.rounds.map (·.1)) ds = true → Reading.gl.val (endFactor k ds) ≠ 0

/-- **OWED BESIDE: the premises of the field exact can meet**, at each member of each row. -/
def AttentionExactIsLive (returned : OnlineReturn files) : Prop :=
  ∀ r ∈ attentionRowsAt returned, ∀ σ, Side.seated returned.F.first.blocksInOrder r.place r.row [] = some σ →
    ∀ pre, ∀ u ∈ σ.members, ExactIsLive r.On r.bud pre u

/-- **OWED BESIDE: where the field's premises hold, each member shows something at every coin.** It
follows from exact with TellsItsCoins. -/
def AttentionShowsSome (returned : OnlineReturn files) : Prop :=
  ∀ r ∈ attentionRowsAt returned, ∀ σ, Side.seated returned.F.first.blocksInOrder r.place r.row [] = some σ →
    ∀ pre, ShowsSome σ r.On r.bud pre

/-- **OWED BESIDE: this form is what the rule that joins the kinds takes.** From AttentionLaw: at rows of
the description whose lists of this kind have a row's place and parts and a bound no wider than the
row's, the premise of the rule at the muted rows at this kind (hand₁ of file_owed_rows_mute,
Honest/Thread/RowsMute.lean), and no list of this kind in the two other chains. A list's On may be any:
the field exact is asked under it, and a row's On is True. The rows stand at the outer types as they
are typed here: of the inner lot read through the rule asks the parts alone, which is the equation of
halves in count; the simulators, On and the bound are this file's to lay. -/
def AttentionHandsToTheRule (returned : OnlineReturn files) : Prop :=
  AttentionLaw returned →
  ∀ G : Sides returned.F returned.B FullSizeMatrix (protocolAtFiles files).EncodingRandomness OnBytes.TableKey Cells Unit Unit,
    G.seated = true →
    (∀ L ∈ G.first, L.place.kind = .K5 → ∃ r ∈ attentionRowsAt returned, L.place = r.place ∧
      L.row = r.row ∧ ∀ n ds asks, L.bud n ds asks → r.bud n ds asks) →
    (∀ L ∈ G.first, L.place.kind = .K5 → ∀ σ, L.side returned.F.first.blocksInOrder G.falls₁ = some σ →
      ∃ A' B', Good (preOf 0 0 (earlierOf returned.F 0) returned.F.first.blocksInOrder L.place) .own σ
        returned.B (orderOf returned.F) 0 0 A' B' L.On L.bud) ∧
    (∀ L ∈ G.shared, L.place.kind ≠ .K5) ∧ ∀ L ∈ G.second, L.place.kind ≠ .K5

/-- **THE SENTENCE TO PROVE.** At a return of the maker, under the library's head at its public part. -/
def AttentionAtTheTermHolds (files : VerifierAndGoals.PublicFiles) : Prop :=
  ∀ (returned : OnlineReturn files) (places : H2U.Places4) (firstChain : Chain TS ProofFile.Cl)
    (description : OnBytes.Maker.WholeD) (run : LPFD.Full.RunPF)
    (x : VerifiableInference.Desc.First.Look.Place),
    onlineMaker files = .ok returned →
    AtMgA OnBytes.secondHashFunction files description run returned.Z places firstChain x →
    AttentionLotIsInTheFilling files ∧ AttentionLotIsTheFillingsOwn files ∧
      AttentionLaw returned ∧ AttentionBook returned

/-- **The premises can be met together** where the verifier's test on the public files says yes. -/
def AttentionPremisesMeet (files : VerifierAndGoals.PublicFiles) : Prop :=
  VerifierAndGoals.InScope files = true → FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true →
    ∃ (returned : OnlineReturn files) (places : H2U.Places4) (firstChain : Chain TS ProofFile.Cl)
      (description : OnBytes.Maker.WholeD) (run : LPFD.Full.RunPF)
      (x : VerifiableInference.Desc.First.Look.Place),
      onlineMaker files = .ok returned ∧
        AtMgA OnBytes.secondHashFunction files description run returned.Z places firstChain x

end AtPublicFiles.AtFiles.HonestTerm.Attention

#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.attentionRows
#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.AttentionLotIsInTheFilling
#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.AttentionLotIsTheFillingsOwn
#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.AttentionSidesAreTheRows
#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.attentionOwners
#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.AttentionLaw
#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.AttentionBook
#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.OwnerFresh
#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.CarrierTie
#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.AttentionShowsSome
#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.AttentionOwnersAreSwitches
#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.AttentionSpentAreTheOwnersCoins
#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.AttentionShowsItsScript
#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.attentionCarriers
#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.AttentionCarriersAreAt
#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.AttentionEndFactorIsNotZero
#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.AttentionExactIsLive
#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.AttentionHandsToTheRule
#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.AttentionAtTheTermHolds
#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.AttentionPremisesMeet
