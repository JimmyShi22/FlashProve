-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/Statements.lean: THE OUTPUT HEAD's OWN ROUNDS (the kind K6 of
the online proof): WHAT THIS KIND OWES TO COMPLETENESS, AS STATEMENTS. Definitions alone.

WHAT IT IS NOT.
  * Nothing is proved here: every statement is a definition of type Prop.
  * None of them says that a verifier accepts a proof.
  * THEY MAY HOLD FOR NOTHING. Every statement but one (RowNeverStops) stands under the library's
    hypothesis on the first chain (h); five of them also under "the maker returns at the filling"
    (hA). h has a member at named public files. That the maker returns is had under h where the
    library's test on the public files accepts: at the base filling, under one premise more on the
    letter I (range), atPure_returns_fillW_at; at the honest prover's own filling
    atPure_returns_term (both: AtFullSide/K12/ReturnsAtAnyIndex.lean); at the filling read through
    other readers by neither. (HeadRowPaysAtAnyBook has the filling as a letter.)
  * The five statements at the border are forms of the honest side's frame
    (Honest/Thread/PaysS.lean). Each begins "wherever the thread's invariant holds in front of the
    member", so each holds for nothing at letters at which that invariant holds nowhere. Whether it
    holds at any run up to border 341 is other kinds' debt and the frame's.
  * AcceptedS IS LIGHT AT THIS SUB-PROTOCOL: the member's decision compares no sent value, so its
    yes is of form alone. THE WEIGHT OF THIS KIND's COMPLETENESS LIES IN ExchangeS: that the claims
    which the member hands on are true. ExchangeS is the one of the five that stays under a
    structure of twelve premises (K6HeadBelow), of which no value is shown at the honest prover; two
    statements here take that structure: DeliversAtTheBorder and AllFiveAtTheHeadsRiders.
  * Of the six imports five stand in no sealed tree (Thread/CsHead.lean does).
  * Nothing on soundness or on what a proof hides.

WORDS. A border is the point in front of a member of a chain's flat list; border 341 is in front of
this kind's member. A thread is the structure of parameters of one chain's invariant; its parameters
are called letters. The seat is the sentence "the prover's first side at the member's place is this
kind's row". A rider is a fact on the verifier's state that holds from one border to another.

WHAT IT IS. The index's type and its reader are letters throughout.
  StandsAtOneBorderUnderTheHead   the kind stands at one member of the online description: number
                                  341 of the first chain; at none of the two other chains
  SideIsTheHeadRowAtTheBase       at that member's place the prover that the maker returns at the
                                  base filling has the row headRow, and no other side of this kind
  SideIsTheHeadRowAtTheFilling    the same at that filling read through two readers, which is the
                                  form of the honest prover's own filling
  RowNeverStops                   no part of the row ever stops. No premise
  HeadRowPaysAtAnyBook            (P1), its core: the row pays (SidePays) at the book of any return
                                  of the maker, the filling a letter
  BookLendsTheKindAtTheBase       (P1) KindPays at all three chains, at the base filling
  BookLendsTheKindAtTheFilling    (P1) the same at the filling read through
  PlaysAndIsAcceptedAtTheBorder   (P2) PlaysS and AcceptedS at 341: under h and the seat, at all
                                  letters of the first chain's thread
  RidesPastAtTheBorder            (P2) RidesPastS at 341: under h and one premise on the letter for
                                  "keeps"; no seat
  FormHoldsBehindTheBorder        (P2) BehindS at 341: under h and KeepsAndRidersFit; no seat
  DeliversAtTheBorder             (P2) ExchangeS at 341: under h, the seat and K6HeadBelow
  FourAtTheHeadsRiders            (P2) these four at the frame's own list of riders (csHead) and at
                                  the border 339 for the reply: under h, the seat and two premises
                                  on the letter for "keeps"; the premises on the riders are met
  AllFiveAtTheHeadsRiders         (P2) all five there as one value of the frame's own structure
                                  FiveAtBorder (Honest/Thread/FiveAtBorder.lean), at every fall:
                                  under the same and K6HeadBelow

THE VALUE. The base filling is onlineProverPartsInUse I secondHashFunction S O, at the stored tables' randomness
IndexCommitterCoins. The honest prover's online filling (E2E/TheHonestProver.lean: onlineFilling files) is
onlineFillingAt at readIndex := id, readRandomness := tableCoins files, namedIndex :=
matrixInput.dummy, I := matrixInput, S := Sz.ref, O := openHonest. The statements (P2) name no
filling: they stand at every prover that has the seat, so at the base prover's threads and at the
threads of the prover read through alike. E2E/OutputHeadAtTheHonestProver.lean sets both values.
The row's reader does not read the stored tables' randomness, so the row read through is the row at
the reader composed. That spares the SIDE and the STATEMENTS a law that carries a thread. It does
not spare the premises: whoever pays K6HeadBelow pays it at the thread at which it is asked.

THE PREMISES, AND WHOSE EACH IS.
  h    the library's hypothesis on the first chain at the three public files (P5J.AtMgA).
  hA   the maker returns at the filling.
  the seat (K6HalfAt, Honest/K6/Law/SeatedAtHead.lean). SideIsTheHeadRow… pay it.
  KeepsAndRidersFit   four premises: one on the frame's letter for "keeps", one on the border for
       the reply, two on the riders. A second premise on "keeps" is RidesPastAtTheBorder's own.
  WHAT IS READ OF THE THREAD. The statements stand at the first chain's thread under h
       (lettersHead, Honest/Thread/FirstHead.lean), all thirteen of its letters bound by ∀; fixed
       are the trace's type (Cells), the own state's (Unit), the trace's reader (id) and the
       format's second hash function. For PlaysS the sealed law k6_playsS (Honest/K6/Law/Plays.lean) stands
       at ANY thread under the five fields of K6Seated: of the thread it reads the members and the
       sides.
  K6HeadBelow (Honest/K6/Law/ScriptBelowFree.lean)   twelve fields on the Script, the trace, the
       lookup in front, the mask row's sender and the book. All twelve are had at one set of
       letters, under h and thirteen named premises, the index's type a letter: headBelowUnderNamed
       (AtFullSide/K6/BelowAtAnyIndex.lean).
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill
import Johnson.Desc.ProofFile.Honest.ThruK13
import Johnson.Desc.ProofFile.Honest.Law.ReadyOfSides
import Johnson.Desc.ProofFile.Honest.K6.Law.ScriptBelowFree
import Johnson.Desc.ProofFile.Honest.Thread.CsHead
import Johnson.Desc.ProofFile.Honest.Thread.FiveAtBorder

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6.Term
open OnBytes (E)
open VerifiableInference.Desc (Chain Strs Place KindName FileDescription)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Kinds (Head.parOf Head.Par)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open VerifiableInference.Desc.Kinds.Head.Honest (K6Keeps plK6)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (K6HeadBelow)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)

variable {W₀ W₀' Rc' : Type}

/-! ## 1 The value -/

/-- **The online prover's filling, with six of its values left open**: the base filling read through
a reader of the index and a reader of the stored tables' randomness. -/
abbrev onlineFillingAt (readIndex : W₀' → W₀) (readRandomness : Rc' → IndexCommitterCoins) (namedIndex : W₀')
    (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) : OnlineProverParts W₀' Rc' Cells Unit Unit :=
  OnlineProverParts.through readIndex readRandomness namedIndex (onlineProverPartsInUse I OnBytes.secondHashFunction S O)

/-- The reader that makes the row's small input of the prover's input, at that filling. It reads
the instance, the trace and the index; it does not read the stored tables' randomness. -/
abbrev headReader (readIndex : W₀' → W₀) (I : WiderIn W₀) (Zp : Pub) (G : Ground) :
    Local W₀' Rc' Inst Cells → HeadAsk :=
  headWit' id (fun w => I.weights Zp (readIndex w)) Zp G

/-- The member's public numbers, as the description's public parameters fix them. -/
abbrev headNumbers (Zp : Pub) : Head.Par := Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))

/-- **The prover's side of the output head's own rounds**, at that filling. -/
abbrev headSide (readIndex : W₀' → W₀) (I : WiderIn W₀) (Zp : Pub) (G : Ground) :
    Placed (Local W₀' Rc' Inst Cells) (Local W₀' Rc' Inst Cells) Unit :=
  ⟨IM.k6Place, headRow (headReader readIndex I Zp G) (headNumbers Zp) IM.k6Place⟩

/-! ## 2 Where the kind stands -/

/-- **The kind stands at one member**: in the first chain at number 341 and nowhere else, at the
place IM.k6Place; in the two other chains nowhere. -/
def StandsAtOneBorder (F : FileDescription Inst) : Prop :=
  (∃ member, F.first.blocksInOrder[341]? = some member ∧ member.place = IM.k6Place) ∧
  (∀ number member, F.first.blocksInOrder[number]? = some member → member.place.kind = .K6 →
    number = 341) ∧
  (∀ member ∈ F.shared.blocksInOrder, member.place.kind ≠ .K6) ∧
  (∀ member ∈ F.second.blocksInOrder, member.place.kind ≠ .K6)

/-- **Under the library's hypothesis on the first chain, the kind stands at one member of the online
description.** -/
def StandsAtOneBorderUnderTheHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub) (Np : H2U.Places4)
    (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place),
    AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x → StandsAtOneBorder (F0T OnBytes.secondHashFunction Zp Np cF)

/-! ## 3 Which side the prover has there -/

/-- **The first side at the member's place is the given one, and no other side is of the kind.** -/
def SideIsTheOnlyOne {V W X : Type} (sides : List (Placed V W X)) (side : Placed V W X) : Prop :=
  sides.find? (fun q => q.place == IM.k6Place) = some side ∧
    ∀ q ∈ sides, q.place.kind = .K6 → q = side

/-- **At the prover that the maker returns at the base filling, the side at the member's place is
the row headRow at the filling's reader; no other side of the first chain is of this kind, and no
side of the two other chains.** -/
def SideIsTheHeadRowAtTheBase : Prop :=
  ∀ (W₀ : Type) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit),
    AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x →
    onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A →
    SideIsTheOnlyOne A.H.first (headSide id I Zp A.G) ∧
      (∀ q ∈ A.H.shared, q.place.kind ≠ .K6) ∧ (∀ q ∈ A.H.second, q.place.kind ≠ .K6)

/-- **The same at the filling read through.** -/
def SideIsTheHeadRowAtTheFilling : Prop :=
  ∀ (W₀ W₀' Rc' : Type) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (readIndex : W₀' → W₀) (readRandomness : Rc' → IndexCommitterCoins) (namedIndex : W₀') (I : WiderIn W₀)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit),
    AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x →
    onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineFillingAt readIndex readRandomness namedIndex I S O) = .ok A →
    SideIsTheOnlyOne A.H.first (headSide readIndex I Zp A.G) ∧
      (∀ q ∈ A.H.shared, q.place.kind ≠ .K6) ∧ (∀ q ∈ A.H.second, q.place.kind ≠ .K6)

/-- **No part of the row ever stops**: at every reader, public numbers and place, at whatever the
second stop may read and at all challenges. No premise. -/
def RowNeverStops : Prop :=
  ∀ (W₀ Rc Tr X : Type) (reader : Local W₀ Rc Inst Tr → HeadAsk) (numbers : Head.Par)
    (place : Place) (view : Option (Local W₀ Rc Inst Tr)) (before own : List Fmt.Drawn),
    rowStopAt view (headRow (X := X) reader numbers place) before own = none

/-! ## 4 (P1) The book lends -/

/-- **(P1), its core: the row pays at the book of any return of the maker**: the filling, the types
of the index and of the stored tables' randomness, and the row's reader are letters. -/
def HeadRowPaysAtAnyBook : Prop :=
  ∀ (W₀ Rc X₀ : Type) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (P : OnlineProverParts W₀ Rc Cells X₀ Unit) (A : OnlineProverWithDescription W₀ Rc Cells X₀ Unit)
    (reader : Local W₀ Rc Inst Cells → HeadAsk),
    AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x →
    onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A →
    SidePays A.B 0 (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
      (⟨IM.k6Place, headRow reader (headNumbers Zp) IM.k6Place⟩ :
        Placed (Local W₀ Rc Inst Cells) (Local W₀ Rc Inst Cells) Unit)

/-- **(P1) The kind pays, in all three chains, at the base filling**: at the maker's book,
description and prover. In the shared and the last chain it says nothing: there the prover has no
side of this kind (SideIsTheHeadRowAtTheBase). -/
def BookLendsTheKindAtTheBase : Prop :=
  ∀ (W₀ : Type) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit),
    AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x →
    onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A →
    KindPays A.B 0 (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder A.H.first .K6 ∧
      KindPays A.B 1 (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder A.H.shared .K6 ∧
      KindPays A.B 2 (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder A.H.second .K6

/-- **(P1) The same at the filling read through.** -/
def BookLendsTheKindAtTheFilling : Prop :=
  ∀ (W₀ W₀' Rc' : Type) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (readIndex : W₀' → W₀) (readRandomness : Rc' → IndexCommitterCoins) (namedIndex : W₀') (I : WiderIn W₀)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit),
    AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x →
    onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineFillingAt readIndex readRandomness namedIndex I S O) = .ok A →
    KindPays A.B 0 (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder A.H.first .K6 ∧
      KindPays A.B 1 (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder A.H.shared .K6 ∧
      KindPays A.B 2 (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder A.H.second .K6

/-! ## 5 (P2) The five statements at border 341

No filling is named. The prover H, the book Bk, the types of the index and of the stored tables'
randomness are letters. Of H the first chain's thread reads the first chain's sides and the stored
tables' words alone: at a prover whose stored tables are not the run's, the invariant holds at no
stand of that run, and the statements say nothing of it. -/

/-- **(P2) It plays, and its step says yes**: under the seat, at all letters of the first chain's
thread, at every fall. -/
def PlaysAndIsAcceptedAtTheBorder : Prop :=
  ∀ (W₀ Rc : Type) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (weights : W₀ → Weights) (G : Ground)
    (Ky X₀ : Type) (H : Prover W₀ Rc Inst Ky Cells X₀ Unit),
    K6HalfAt Zp H (headWit' id weights Zp G) →
    ∀ (Bk : ProverCoinCounts)
      (Q : Script Bk (Local W₀ Rc Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
      (test : Nat → TS → Option String) (carryX : Nat → InstPub × TS → Strs → WtF → Prop)
      (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc Inst Cells → Prop)
      (Rd : Nat → Local W₀ Rc Inst Cells → TS → Prop) (Kp : Place → TS → TS → Prop)
      (w : Local W₀ Rc Inst Cells)
      (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Cells) Unit → Prop),
    PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 ∧
    ∀ fall : Nat → TS → List Fmt.Drawn → Option String,
      AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall 341

/-- **(P2) What stays open past the member stays true**: where the letter for "keeps" gives, at this
kind's place, the kind's own clause. No seat. -/
def RidesPastAtTheBorder : Prop :=
  ∀ (W₀ Rc : Type) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Ky X₀ : Type) (H : Prover W₀ Rc Inst Ky Cells X₀ Unit) (Bk : ProverCoinCounts)
    (Q : Script Bk (Local W₀ Rc Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc Inst Cells → Prop)
    (Rd : Nat → Local W₀ Rc Inst Cells → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc Inst Cells)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Cells) Unit → Prop),
    (∀ s s', Kp plK6 s s' → K6Keeps s s') →
    RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341

section Border
variable {W₀ Rc : Type} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : Pub}
  {Np : H2U.Places4} {cF : Chain TS Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {Ky X₀ : Type}
  (H : Prover W₀ Rc Inst Ky Cells X₀ Unit)
  (Q : Script Bk (Local W₀ Rc Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc Inst Cells → Prop)
  (riders : List (RiderCl (Local W₀ Rc Inst Cells) TS))
  (keepsByKind : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc Inst Cells)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Cells) Unit → Prop)

/-- On the frame's letter for "keeps": behind a step, the kind's own clause gives what the letter
lays for this kind. -/
def KeepsIsGiven : Prop :=
  ∀ (k : Coins Bk) (s s' : TS) (m' : Mid (Local W₀ Rc Inst Cells) Unit), K6Keeps s s' →
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf riders) (kpBy keepsByKind)
      w).thread.Form (341 + 1) k s' m' → keepsByKind .K6 plK6 s s'

/-- **What the frame's letters for "keeps" and for the riders must meet, so that the form, the
riders and "keeps" hold behind this member.** A structure of premises. -/
structure KeepsAndRidersFit : Prop where
  /-- behind a step, the kind's own clause gives what the letter lays for this kind -/
  keepsIsGiven : KeepsIsGiven h H Q test carryX item n₁ n₂ b₀ Vd riders keepsByKind w
  /-- the border from which the state holds the reply does not lie right behind the member -/
  replyNotBehind : b₀ ≠ 341 + 1
  /-- each rider that spans the member stays past it -/
  ridersStay : ∀ c ∈ riders, c.lo ≤ 341 → 341 + 1 ≤ c.hi → StaysBy
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf riders) (kpBy keepsByKind)
      w).thread 341 c
  /-- each rider that begins right behind the member is the head's own, or is laid by the member -/
  ridersBegin : ∀ c ∈ riders, c.lo = 341 + 1 →
    (∃ hi, c = riderHead (341 + 1) hi fun o => o.x.isSome = true) ∨ LaysAtS
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf riders) (kpBy keepsByKind)
        w).thread Said 341 c

end Border

/-- **(P2) Behind the member's accepting step the form and the riders hold, and the step kept what
"keeps" names**: at letters for "keeps" and for the riders that fit. No seat. -/
def FormHoldsBehindTheBorder : Prop :=
  ∀ (W₀ Rc : Type) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Ky X₀ : Type) (H : Prover W₀ Rc Inst Ky Cells X₀ Unit) (Bk : ProverCoinCounts)
    (Q : Script Bk (Local W₀ Rc Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc Inst Cells → Prop)
    (riders : List (RiderCl (Local W₀ Rc Inst Cells) TS))
    (keepsByKind : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc Inst Cells)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Cells) Unit → Prop),
    KeepsAndRidersFit h H Q test carryX item n₁ n₂ b₀ Vd riders keepsByKind w Said →
    BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf riders)
      (kpBy keepsByKind) w).thread Said 341

/-- **(P2), THE WEIGHT: behind the member's accepting step, what the member owes is delivered**:
under the seat and the twelve fields of K6HeadBelow, at a reader of the committed digits and a
ground that are letters. The seven letters behind them are K6HeadBelow's own, on the mask row's
sender. -/
def DeliversAtTheBorder : Prop :=
  ∀ (W₀ Rc : Type) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (weights : W₀ → Weights) (G : Ground)
    (Ky X₀ : Type) (H : Prover W₀ Rc Inst Ky Cells X₀ Unit),
    K6HalfAt Zp H (headWit' id weights Zp G) →
    ∀ (Bk : ProverCoinCounts)
      (Q : Script Bk (Local W₀ Rc Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
      (test : Nat → TS → Option String) (carryX : Nat → InstPub × TS → Strs → WtF → Prop)
      (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc Inst Cells → Prop)
      (Rd : Nat → Local W₀ Rc Inst Cells → TS → Prop) (Kp : Place → TS → TS → Prop)
      (w : Local W₀ Rc Inst Cells)
      (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Cells) Unit → Prop)
      (o : Addr) (d : Due) (rowOf : Cs d → Nat → E) (own : Coins Bk → Cs d)
      (base cnt free : Nat),
    K6HeadBelow h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said id weights G o d rowOf own base
      cnt free →
    ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341

/-- **(P2) Four of the five at the frame's own riders**: at the list csHead, whatever its three
parameters, and at the border 339 for the reply. Under the seat and two premises on the letter for
"keeps": what it lays for this kind gives the kind's own clause, and behind a step is given by
it. -/
def FourAtTheHeadsRiders : Prop :=
  ∀ (W₀ Rc : Type) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (weights : W₀ → Weights) (G : Ground)
    (Ky X₀ : Type) (H : Prover W₀ Rc Inst Ky Cells X₀ Unit),
    K6HalfAt Zp H (headWit' id weights Zp G) →
    ∀ (Bk : ProverCoinCounts)
      (Q : Script Bk (Local W₀ Rc Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
      (test : Nat → TS → Option String) (carryX : Nat → InstPub × TS → Strs → WtF → Prop)
      (item n₁ n₂ : Nat) (Vd : Local W₀ Rc Inst Cells → Prop)
      (nextFree : Nat) (afterDigits : Nat → TS → Prop)
      (callsReturned : Nat → Option OnBytes.Model.Forest.Heard → Prop)
      (keepsByKind : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc Inst Cells)
      (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Cells) Unit → Prop),
    (∀ s s', keepsByKind .K6 plK6 s s' → K6Keeps s s') →
    KeepsIsGiven h H Q test carryX item n₁ n₂ 339 Vd (csHead nextFree afterDigits callsReturned)
      keepsByKind w →
    PlaysS (lettersHead h H Q test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead nextFree afterDigits callsReturned)) (kpBy keepsByKind) w).thread Said
      341 ∧
    BehindS (lettersHead h H Q test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead nextFree afterDigits callsReturned)) (kpBy keepsByKind) w).thread Said
      341 ∧
    RidesPastS (lettersHead h H Q test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead nextFree afterDigits callsReturned)) (kpBy keepsByKind) w).thread Said
      341 ∧
    ∀ fall : Nat → TS → List Fmt.Drawn → Option String,
      AcceptedS (lettersHead h H Q test carryX item n₁ n₂ 339 Vd
        (ridersOf (csHead nextFree afterDigits callsReturned)) (kpBy keepsByKind) w).thread Said
        fall 341

/-- **(P2) All five at the frame's own riders, as one value of the frame's structure**, at every
fall. Under the seat, the two premises on the letter for "keeps", and the twelve fields of
K6HeadBelow at these same letters. -/
def AllFiveAtTheHeadsRiders : Prop :=
  ∀ (W₀ Rc : Type) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (weights : W₀ → Weights) (G : Ground)
    (Ky X₀ : Type) (H : Prover W₀ Rc Inst Ky Cells X₀ Unit),
    K6HalfAt Zp H (headWit' id weights Zp G) →
    ∀ (Bk : ProverCoinCounts)
      (Q : Script Bk (Local W₀ Rc Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
      (test : Nat → TS → Option String) (carryX : Nat → InstPub × TS → Strs → WtF → Prop)
      (item n₁ n₂ : Nat) (Vd : Local W₀ Rc Inst Cells → Prop)
      (nextFree : Nat) (afterDigits : Nat → TS → Prop)
      (callsReturned : Nat → Option OnBytes.Model.Forest.Heard → Prop)
      (keepsByKind : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc Inst Cells)
      (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Cells) Unit → Prop)
      (o : Addr) (d : Due) (rowOf : Cs d → Nat → E) (own : Coins Bk → Cs d)
      (base cnt free : Nat),
    (∀ s s', keepsByKind .K6 plK6 s s' → K6Keeps s s') →
    KeepsIsGiven h H Q test carryX item n₁ n₂ 339 Vd (csHead nextFree afterDigits callsReturned)
      keepsByKind w →
    K6HeadBelow h H Q test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead nextFree afterDigits callsReturned)) (kpBy keepsByKind) w Said id weights
      G o d rowOf own base cnt free →
    ∀ fall : Nat → TS → List Fmt.Drawn → Option String,
      FiveAtBorder (lettersHead h H Q test carryX item n₁ n₂ 339 Vd
        (ridersOf (csHead nextFree afterDigits callsReturned)) (kpBy keepsByKind) w).thread Said
        fall 341

end ProofFile.Honest.K6.Term
