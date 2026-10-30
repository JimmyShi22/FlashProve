-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/AtTheBaseStatement.lean: what the code switch (the kind K2) owes at the honest online
prover.

1. The code switch moves a group of claims from one code to the next. It stands at the 25 members of
   the first chain that K2Stands counts. Each has two rounds: the roots of the new trees, then the
   out-of-domain answers.
2. The base prover is A.H, where the maker returns A at the filling onlineProverPartsInUse I. The index is
   a letter: I says how the prover reads it. The online prover of the protocol is this prover read
   through the table's coins, with the committer's key and stored columns
   (E2E/TheHonestProver.lean). That crossing is stated elsewhere, kind by kind for no kind.
3. K2Lends: the book lends each side of the kind its runs, so that chainSteps returns there, at every
   view and every run's coins. K2SidesThere says that such sides stand: at each of the 25 places a
   member of the chain, and the kind's side as the first found. Neither says what is played.
4. K2Plays: the side plays both rounds. K2Accepted: the verifier's step at the member says yes, at
   every list of falls. These two say little of the values: the step tests what is sent in its shape
   alone, so they would hold of a sender of false tables.
5. K2Exchange, in AtTheBaseExchange.lean of this folder: every item that the member's row owes is
   true behind it. With the form behind the member this is where the weight lies.
6. BehindS and RidesPastS are stated and proved in KeepsBehind.lean and RidesPast.lean of this folder,
   at the first thread's keeps.
7. The statements speak of the joined script with letters S; that the term's script is such a one is
   the threads' matter.
8. Where the maker does not return, or no head stands at the public files, every statement here holds
   of nothing. That they do is a proposition of E2E/TheHonestProver.lean.
9. Nothing says here that a state meets the thread's sentence.
10. This file states; it proves nothing.
-/
import Johnson.Desc.ProofFile.Honest.Law.ReadyOfSides
import Johnson.Desc.ProofFile.Honest.Thread.CsHead
import Johnson.Desc.ProofFile.Honest.Thread.KeepsBy
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill
import AtFullSide.K2.PlaysAtJoin
import AtFullSide.K2.FoundAtTheTerm
import Johnson.Desc.ProofFile.Honest.K2.Law.JoinShareAtHead
import Johnson.Desc.ProofFile.Honest.K12.JoinShare

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2.Base
open VerifiableInference.Desc (Chain Block Place KindName Strs)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open OnBytes.SendSim.Seat (wJobs)
open P5J (AtMgA CellsM TS F0T)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law

variable {W₀ : Type}

/-- The input of the first chain's sides at the base prover. -/
abbrev Input (W₀ : Type) := Local W₀ IndexCommitterCoins ProofFile.Inst Cells

/-- What the maker returns at the filling. -/
abbrev BaseReturn (W₀ : Type) := OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit

/-- **The maker returns at the filling.** -/
def Returns (I : WiderIn W₀) (Oh : OnlineProverArguments) (Z : VerifierAndGoals.PublicFiles) (A : BaseReturn W₀) : Prop :=
  onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Oh) = .ok A

/-- **The reader of the kind's side**: the filling's. -/
def reader (I : WiderIn W₀) (Zp : ProofFile.Pub) (v : Input W₀) : Readers :=
  ⟨v.trace, I.weights Zp v.w₀, v.rc⟩

/-- The same with the input's instance, as the script's senders read it. -/
def placeIn (I : WiderIn W₀) (Zp : ProofFile.Pub) (v : Input W₀) : K1.PlaceIn ProofFile.Inst :=
  ⟨v.x, reader I Zp v⟩

/-- The data of the main rows. -/
abbrev rowsAt (Zp : ProofFile.Pub) (Bs : ProofFile.PureBase) : RowDataOf ProofFile.Inst :=
  withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀

/-- **The joined script.** no, Dd, cellsQ, tokQ, own₀, Oth: its letters. -/
abbrev scriptAt {Y : Type} (I : WiderIn W₀) (A : BaseReturn W₀) (Zp : ProofFile.Pub) (Bs : ProofFile.PureBase)
    (cF : Chain TS ProofFile.Cl) (no : Place → Nat) (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
    (cellsQ : Input W₀ → CellsM OnBytes.Flat.numsFull) (tokQ : Input W₀ → P5J.At.Tok) (own₀ : Y)
    (Oth : Others A.B (Input W₀)) :
    Script A.B (Input W₀) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT :=
  joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) (placeIn I Zp) own₀
    (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
               wJobs (X := Y) no Dd Zp Bs.G₀)) Oth

/-- **The letters of the joined script, and what its share of the others is.** -/
structure ScriptLetters (I : WiderIn W₀) (A : BaseReturn W₀) (Zp : ProofFile.Pub) (Bs : ProofFile.PureBase)
    (cF : Chain TS ProofFile.Cl) (Y X₂ : Type) where
  no : Place → Nat
  Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst
  cellsQ : Input W₀ → CellsM OnBytes.Flat.numsFull
  tokQ : Input W₀ → P5J.At.Tok
  own₀ : Y
  rest : Nat → TreeLot A.B (Input W₀)
  ch : Nat
  Jt : K12.TestJob (Input W₀) X₂
  stages : Jt.p.nums.stages.length = 6
  own₂ : X₂
  n₀ : Nat
  ok : Input W₀ → List Fmt.Drawn → (Nat → K12.Stretch) → Bool
  codes : OnBytes.Codes
  sh : Nat → OnBytes.OracleShape
  sh₁ : Nat → OnBytes.OracleShape
  rest₂ : Nat → TreeLot A.B (Input W₀)
  Oth : Others A.B (Input W₀)
  share : Oth = (switchShareAt A.B cF.blocksInOrder 0 Zp Bs.G₀ (rowsAt Zp Bs) (reader I Zp) rest).add
    (K12.k12Share ch Jt own₂ n₀ 77 (P5J.At.arr Zp) ok codes sh sh₁ 354 rest₂)

/-- The script of these letters. -/
abbrev ScriptLetters.Q {I : WiderIn W₀} {A : BaseReturn W₀} {Zp : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {cF : Chain TS ProofFile.Cl} {Y X₂ : Type} (S : ScriptLetters I A Zp Bs cF Y X₂) :=
  scriptAt I A Zp Bs cF S.no S.Dd S.cellsQ S.tokQ S.own₀ S.Oth

/-- **The first chain's letters at the base prover.** -/
noncomputable abbrev baseLetters {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (A : BaseReturn W₀)
    (Q : Script A.B (Input W₀) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (item n₁ n₂ b₀ : Nat) (Vd : Input W₀ → Prop)
    (Rd : Nat → Input W₀ → TS → Prop) (Kp : Place → TS → TS → Prop) (w : Input W₀) :=
  lettersHead h A.H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp w

/-- **The kind stands at 25 members of the first chain.** -/
def K2Stands : Prop :=
  ((P5J.At.ps.zipIdx.filter fun x => decide (x.1.kind = KindName.K2)).map (·.2)).length = 25

/-- **The book lends the kind's sides.** -/
def K2Lends : Prop :=
  ∀ {W₀ : Type} (I : WiderIn W₀) (Oh : OnlineProverArguments) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF)
    (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
    (x : VerifiableInference.Desc.First.Look.Place) (A : BaseReturn W₀),
    Returns I Oh Z A → AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x →
    KindPays A.B 0 cF.blocksInOrder A.H.first KindName.K2

/-- **The kind's sides stand**: at each place of the kind a member of the chain, and the kind's side
as the first found. -/
def K2SidesThere : Prop :=
  ∀ {W₀ : Type} (I : WiderIn W₀) (Oh : OnlineProverArguments) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF)
    (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
    (x : VerifiableInference.Desc.First.Look.Place) (A : BaseReturn W₀) (Bs : ProofFile.PureBase)
    (base : List (Block TS ProofFile.Cl)),
    Returns I Oh Z A → AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x →
    IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np) →
    (switchPlaces Zp Bs.G₀).length = 25 ∧ ((switchPlaces Zp Bs.G₀).map (·.place)).Nodup ∧
      ∀ p ∈ switchPlaces Zp Bs.G₀, (∃ b ∈ cF.blocksInOrder, b.place = p.place) ∧
        (A.H.first.find? fun g => g.place == p.place) =
          some (switchHalf (coreSender freshTable) (rowsAt Zp Bs) (reader I Zp)
            (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p)

/-- **The side plays, at every member of the kind, at every letter Said.** start: the description's
first test accepts the run's input's instance. -/
def K2Plays : Prop :=
  ∀ {W₀ : Type} (I : WiderIn W₀) (Oh : OnlineProverArguments) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF)
    (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
    (x : VerifiableInference.Desc.First.Look.Place) (A : BaseReturn W₀) (Bs : ProofFile.PureBase)
    (base : List (Block TS ProofFile.Cl)),
    Returns I Oh Z A →
    ∀ (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
      (_ : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
        (seatZ Zp Np) (secondAt Zp Np))
      {Y X₂ : Type} (S : ScriptLetters I A Zp Bs cF Y X₂)
      (test : Nat → TS → Option String) (item n₁ n₂ b₀ : Nat) (Vd : Input W₀ → Prop)
      (Rd : Nat → Input W₀ → TS → Prop) (Kp : Place → TS → TS → Prop) (w : Input W₀)
      (Said : Nat → Coins A.B → Mid (Input W₀) Unit → Prop),
      (Vd w → (F0T OnBytes.secondHashFunction Zp Np cF).okStart w.x = true) →
      ∀ b q, P5J.At.ps[b]? = some q → q.kind = KindName.K2 →
        PlaysS (baseLetters h A S.Q test item n₁ n₂ b₀ Vd Rd Kp w).thread Said b

/-- **The member's step says yes, at every member of the kind, at every list of falls**: at every
script. -/
def K2Accepted : Prop :=
  ∀ {W₀ : Type} (I : WiderIn W₀) (Oh : OnlineProverArguments) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF)
    (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
    (x : VerifiableInference.Desc.First.Look.Place) (A : BaseReturn W₀) (Bs : ProofFile.PureBase)
    (base : List (Block TS ProofFile.Cl)),
    Returns I Oh Z A →
    ∀ (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
      (_ : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
        (seatZ Zp Np) (secondAt Zp Np))
      (Q : Script A.B (Input W₀) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
      (test : Nat → TS → Option String) (item n₁ n₂ b₀ : Nat) (Vd : Input W₀ → Prop)
      (Rd : Nat → Input W₀ → TS → Prop) (Kp : Place → TS → TS → Prop) (w : Input W₀)
      (Said : Nat → Coins A.B → Mid (Input W₀) Unit → Prop),
      (∀ b k m, Said b k m → SaidOk b k m) →
      ∀ b q, P5J.At.ps[b]? = some q → q.kind = KindName.K2 →
        ∀ fall, AcceptedS (baseLetters h A Q test item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall b

end AtFullSide.K2.Base
