-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/K11AtTheTerm.lean: what the head's merge (the kind K11) owes at the honest online prover.

1. The head's merge reduces the claim on the weights at the output head to one equation on the
   committed matrix. It stands at one member of the first chain, number 346, sends 2 lk + 3 scalars
   and no table. The merge's runs that are gathered inside the batchings, at other members, are not
   treated here.
2. The statements stand at the base prover A.H: the maker's return at the filling
   onlineProverPartsInUse at openHonest, at a letter I for what depends on the index. The online prover
   of E2E/TheHonestProver.lean reads that filling through the table's randomness, and plays the
   return with the committer's key and columns. The kind's own part of that crossing is
   E2E/K11Crossing.lean: the side that the online prover holds here is this side read through. The
   rest of the crossing, for the five debts, for the lending and for the rule, is general in the
   kinds; those three laws are not stated here.
3. K11Lends: the book lends the kind's side its runs, so that chainSteps returns there at every view
   and every run's coins. It says nothing on what is played.
4. K11Five: the five debts of the thread (Honest/Thread/PaysS.lean) at every member of the kind, at
   the first chain's thread at the base prover. BehindS and ExchangeS carry the weight: the
   verifier's step at this member tests nothing of the values, so that a sender that merged false
   claims would meet PlaysS and AcceptedS.
5. The premises of K11Five, beside the library's head, the maker's return and its base, are of
   three sorts. What the script says at this member: K11ScriptMsg, K11CellsQ. K11ScriptAtTheTerm
   shows both at the joined list of all three senders, under the light test on the reads at the
   valid inputs, which is shown nowhere yet. What the thread's letter f says at the kind: two
   premises. What belongs to the head's lookup: the letter st stays past the merge's clause, and two
   of its items ride past.
6. K11Found: the base prover's search at the kind's place finds the kind's side. K11SimulatorOwed,
   at any filling that lays the kind's lot and no other side of the kind: the simulator beside that
   sender is exact and fresh at the book of the return, at the list of rounds in front that the rule
   asks; and the row's fields of Owed, On and bud, hold at every run. On and bud are True at this
   row: the simulator reads nothing that it is handed, and the kind sends no table. Its instances
   at the base prover and at the online prover are K11SimulatorOwedBase and, in E2E/K11Crossing.lean,
   K11SimulatorOwedOnline.
7. The end value's mask and the hiding polynomial's coefficients are runs of the coins of other
   parts: the hiding polynomial's 38 entries of the code switch into link 24, and the end value's one
   entry of message 4 of the first opening. exact takes them as uniform; that their owners hand them
   on so is fresh at those owners, at the kind's part 1.
8. Good stands here at A := B := False: its fields plays and acc say nothing; the rule that joins
   the rows reads neither, and K11Five says what is said of the playing.
9. That the thread's sentence holds at any state is not said here: the five debts take it as their
   premise by their form. Where the maker does not return, or no head stands at the files, every
   statement here holds of nothing.
10. K11Lends holds of nothing where the prover has no side of the kind: K11Found, at the base prover,
    excludes that.
11. This file states; it proves nothing.
-/
import Johnson.Desc.ProofFile.Honest.OpenHonest
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill
import Johnson.Desc.ProofFile.Honest.Law.ReadyOfSides
import Johnson.Desc.ProofFile.Honest.K11.Plays.FiveAtHeadStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.SLotStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.ClaimsNStatement
import Johnson.Desc.ProofFile.Honest.K2.JoinShare
import Johnson.Desc.ProofFile.Honest.K12.JoinShare
import Johnson.Desc.ProofFile.Honest.K2.Law.LightDebts
import Johnson.Desc.ProofFile.Honest.Thread.JoinAtHead
import Johnson.Desc.ProofFile.Honest.Thread.CsHead
import Johnson.Desc.ProofFile.Honest.Thread.KeepsBy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles.HonestTerm.K11Term
open VerifiableInference.Desc (Chain Strs Place KindName)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles.Flat (Holds)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open Johnson.Desc.First.ForkMerge.Returns (K11KeepsYes)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest
open ProofFile.Honest.SumLaw (SumCoins)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K1 (PlaceIn)
open ProofFile.Honest.K2 (withSwitchData switchShareAt)
open ProofFile.Honest.K11

variable {W₀ : Type}

/-- The input of the first chain's sides at the base prover. -/
abbrev Input (W₀ : Type) := Local W₀ IndexCommitterCoins ProofFile.Inst Cells

/-- **The base prover's maker**, at the three public files: the filling of the online prover before
it is read through the table's randomness. -/
abbrev baseMaker (I : WiderIn W₀) (Z : VerifierAndGoals.PublicFiles) :
    Except String (OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit) :=
  onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref openHonest)

/-- **The first chain's thread at the base prover.** The border from which the reply rides is the
written one; rides are the written clauses; keeps is by kind. -/
noncomputable abbrev baseThread {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit)
    (Q : Script A.B (Input W₀) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (Vd : Input W₀ → Prop) (ν : Nat) (st : Nat → TS → Prop)
    (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)
    (f : KindName → Place → TS → TS → Prop) (w : Input W₀) :=
  (lettersHead h A.H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w).thread

/-- **The book lends the kind's side.** -/
def K11Lends : Prop :=
  ∀ (W₀ : Type) (I : WiderIn W₀) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF)
    (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
    (x : VerifiableInference.Desc.First.Look.Place) (A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit),
    baseMaker I Z = .ok A → AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x →
    KindPays A.B 0 cF.blocksInOrder A.H.first KindName.K11

/-- **The five debts at every member of the kind.** Said: whatever is said along the thread, at
least SaidOk. c₀: what stands where the book does not lend. The premises, in order: the script's two
facts; the letter f at the kind, both ways; the letter st past the merge's clause; the two items of
the head's lookup that ride past. -/
def K11Five : Prop :=
  ∀ (W₀ : Type) (I : WiderIn W₀) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF)
    (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
    (x : VerifiableInference.Desc.First.Look.Place) (A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit)
    (Bs : ProofFile.PureBase),
    baseMaker I Z = .ok A →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    ∀ (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
      (Q : Script A.B (Input W₀) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
      (test : Nat → TS → Option String)
      (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
      (Vd : Input W₀ → Prop) (ν : Nat) (st : Nat → TS → Prop)
      (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)
      (f : KindName → Place → TS → TS → Prop) (w : Input W₀)
      (Said : Nat → Coins A.B → Mid (Input W₀) Unit → Prop)
      (c₀ : SumCoins (runName maskRowRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "sum")
        (runName indexMaskRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "ends")
        (headMergeJob (_root_.K11.parOf Zp Bs.G₀).lay)),
      (∀ b k m, Said b k m → SaidOk b k m) →
      K11ScriptMsg (baseThread h A Q test carryX item n₁ n₂ Vd ν st R f w) SaidOk 346
        (_root_.K11.parOf Zp Bs.G₀)
        (headMergeCoins (baseThread h A Q test carryX item n₁ n₂ Vd ν st R f w)
          (_root_.K11.parOf Zp Bs.G₀) (headClaimsAt cF Zp Bs.G₀) (I.weights Zp) IM.k11Place c₀)
        id id (dataAtHead h Q carryX) 24 →
      K11CellsQ Q (_root_.K11.parOf Zp Bs.G₀).lay (I.weights Zp) Vd →
      (∀ s s', f KindName.K11 IM.k11Place s s' → K11KeepsYes (_root_.K11.parOf Zp Bs.G₀) s s') →
      (∀ blk k s m E ds y cols s',
        ThrS (baseThread h A Q test carryX item n₁ n₂ Vd ν st R f w) Said 346 k s m E →
        (baseThread h A Q test carryX item n₁ n₂ Vd ν st R f w).Stepped blk k s m E ds y cols s' →
        cF.blocksInOrder[346]? = some blk → K11KeepsYes (_root_.K11.parOf Zp Bs.G₀) s s' →
        f KindName.K11 IM.k11Place s s') →
      (∀ s s', K11KeepsYes (_root_.K11.parOf Zp Bs.G₀) s s' → st 24 s → st 24 s') →
      RidesPastAtS (baseThread h A Q test carryX item n₁ n₂ Vd ν st R f w) Said 346
        (Item.worth 24 8 "planes") →
      RidesPastAtS (baseThread h A Q test carryX item n₁ n₂ Vd ν st R f w) Said 346
        (Item.worth 24 8 "keys") →
      ∀ b q, P5J.At.ps[b]? = some q → q.kind = KindName.K11 →
        PlaysS (baseThread h A Q test carryX item n₁ n₂ Vd ν st R f w) Said b ∧
        (∀ fall, AcceptedS (baseThread h A Q test carryX item n₁ n₂ Vd ν st R f w) Said fall b) ∧
        BehindS (baseThread h A Q test carryX item n₁ n₂ Vd ν st R f w) Said b ∧
        ExchangeS (baseThread h A Q test carryX item n₁ n₂ Vd ν st R f w) Said b ∧
        RidesPastS (baseThread h A Q test carryX item n₁ n₂ Vd ν st R f w) Said b

/-- The senders' other shares at the joined list: the code switches', then the proximity test's. -/
abbrev termShare (A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit) (cF : Chain TS ProofFile.Cl) (front : Nat)
    (Zp : ProofFile.Pub) (G : ProofFile.Ground) (readers : Input W₀ → Readers)
    (rest : Nat → TreeLot A.B (Input W₀)) {X₂ : Type} (ch : Nat)
    (Jt : ProofFile.Honest.K12.TestJob (Input W₀) X₂) (own₂ : X₂) (n₀ : Nat)
    (ok : Input W₀ → List Fmt.Drawn → (Nat → ProofFile.Honest.K12.Stretch) → Bool)
    (codes : OnBytes.Codes) (sh sh₁ : Nat → OnBytes.OracleShape)
    (rest₂ : Nat → TreeLot A.B (Input W₀)) : Others A.B (Input W₀) :=
  (switchShareAt A.B cF.blocksInOrder front Zp G
    (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) readers rest).add
      (ProofFile.Honest.K12.k12Share ch Jt own₂ n₀ 77 (P5J.At.arr Zp) ok codes sh sh₁ 354 rest₂)

/-- **The joined script of the first chain.** mat: the cells, of the index. -/
abbrev termScript (A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit) (cF : Chain TS ProofFile.Cl) (front : Nat)
    (Zp : ProofFile.Pub) (G : ProofFile.Ground) {Xi Y : Type} (mat : W₀ → CellsM OnBytes.Flat.numsFull)
    (tok : Input W₀ → P5J.At.Tok) (wit : Input W₀ → PlaceIn Xi) (own₀ : Y) (no : Place → Nat)
    (Dt Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Oth : Others A.B (Input W₀)) :
    Script A.B (Input W₀) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT :=
  joinQ cF.blocksInOrder front (fun v => mat v.w₀) tok (P5J.At.arr Zp) wit own₀
    (byNo cF.blocksInOrder (k1Jobs (X := Y) no Dt Dd Zp G)) Oth

/-- **What the kind asks of the script holds at the joined list.** Beyond the head and the maker's
return: the proximity test's six stages; that the valid inputs Vd have their index in range; the
light test at the reads' filling at each valid input; at an index in range the cells hold an index whose
entries the reader reads. -/
def K11ScriptAtTheTerm : Prop :=
  ∀ (W₀ : Type) (I : WiderIn W₀) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF)
    (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
    (x : VerifiableInference.Desc.First.Look.Place) (A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit)
    (Bs : ProofFile.PureBase) (Xi Y X₂ : Type),
    baseMaker I Z = .ok A →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    ∀ (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (front : Nat)
      (mat : W₀ → CellsM OnBytes.Flat.numsFull) (tok : Input W₀ → P5J.At.Tok)
      (wit : Input W₀ → PlaceIn Xi) (own₀ : Y) (no : Place → Nat)
      (Dt Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (readers : Input W₀ → Readers)
      (rest : Nat → TreeLot A.B (Input W₀)) (ch : Nat)
      (Jt : ProofFile.Honest.K12.TestJob (Input W₀) X₂) (own₂ : X₂) (n₀ : Nat)
      (ok : Input W₀ → List Fmt.Drawn → (Nat → ProofFile.Honest.K12.Stretch) → Bool)
      (codes : OnBytes.Codes) (sh sh₁ : Nat → OnBytes.OracleShape)
      (rest₂ : Nat → TreeLot A.B (Input W₀))
      (test : Nat → TS → Option String)
      (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
      (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)
      (f : KindName → Place → TS → TS → Prop) (w : Input W₀) (Vd : Input W₀ → Prop)
      (c₀ : SumCoins (runName maskRowRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "sum")
        (runName indexMaskRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "ends")
        (headMergeJob (_root_.K11.parOf Zp Bs.G₀).lay)),
      Jt.p.nums.stages.length = 6 →
      (∀ v, Vd v → I.inRange v.w₀ = true) →
      (∀ v, Vd v → ProofFile.Honest.K2.Law.ReadsLight Zp Bs.G₀ v.x) →
      (∀ w₀, I.inRange w₀ = true → ∃ i : Cm.Idx, Holds (mat w₀) i ∧
        ∀ a b, algebraMap Cb.Gl.F Cb.Gl.E ((I.weights Zp w₀).entry a b) =
          ((i.mat a b : ℤ) : Cb.Gl.E)) →
      K11ScriptMsg
        (baseThread h A
          (termScript A cF front Zp Bs.G₀ mat tok wit own₀ no Dt Dd
            (termShare A cF front Zp Bs.G₀ readers rest ch Jt own₂ n₀ ok codes sh sh₁ rest₂))
          test carryX item n₁ n₂ Vd ν st R f w)
        SaidOk 346 (_root_.K11.parOf Zp Bs.G₀)
        (headMergeCoins
          (baseThread h A
            (termScript A cF front Zp Bs.G₀ mat tok wit own₀ no Dt Dd
              (termShare A cF front Zp Bs.G₀ readers rest ch Jt own₂ n₀ ok codes sh sh₁ rest₂))
            test carryX item n₁ n₂ Vd ν st R f w)
          (_root_.K11.parOf Zp Bs.G₀) (headClaimsAt cF Zp Bs.G₀) (I.weights Zp) IM.k11Place c₀)
        id id
        (dataAtHead h
          (termScript A cF front Zp Bs.G₀ mat tok wit own₀ no Dt Dd
            (termShare A cF front Zp Bs.G₀ readers rest ch Jt own₂ n₀ ok codes sh sh₁ rest₂))
          carryX) 24 ∧
      K11CellsQ
        (termScript A cF front Zp Bs.G₀ mat tok wit own₀ no Dt Dd
          (termShare A cF front Zp Bs.G₀ readers rest ch Jt own₂ n₀ ok codes sh sh₁ rest₂))
        (_root_.K11.parOf Zp Bs.G₀).lay (I.weights Zp) Vd

/-- The row of the kind K11: parts with their simulators. weights: the reader of the index. -/
abbrev k11Row {W₀ Rc Tr X : Type} (weights : W₀ → Weights) (Zp : ProofFile.Pub) (G : ProofFile.Ground) :
    Unlettered (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst :=
  headMergeBare (_root_.K11.parOf Zp G) (headClaimsByPlace Zp G) weights

/-- The row with its letters for the rule, at a book. A and B are False: the rule reads neither. -/
abbrev k11Lettered {W₀ Rc Tr X : Type} (weights : W₀ → Weights) (Zp : ProofFile.Pub) (G : ProofFile.Ground)
    (Bk : ProverCoinCounts) : Lettered Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst :=
  { place := (k11Row (Rc := Rc) (Tr := Tr) (X := X) weights Zp G).place
    row := (k11Row weights Zp G).row
    A := fun _ _ _ _ => False, B := fun _ _ _ _ => False
    On := (k11Row weights Zp G).On
    bud := (k11Row (Rc := Rc) (Tr := Tr) (X := X) weights Zp G).bud }

/-- **The simulator's three clauses at a return of the maker.** First: the row's sender is what the
prover holds at the row's place. Second: Good, so exact and fresh, at the side that the row makes with
the first chain's own member, at the return's book, its order of places, and at the list of rounds
in front that the rule asks, at every list of earlier rounds. Third: the row's fields of Owed, at
every run at which the row's parts that it has called have a stand: at all coins. -/
def K11OwedAt {W₀ Rc Tr X₀ X : Type} (weights : W₀ → Weights) (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl)
    (A : OnlineProverWithDescription W₀ Rc Tr X₀ X) (Bs : ProofFile.PureBase) : Prop :=
  (A.H.first.find? fun g =>
      g.place == (k11Row (Rc := Rc) (Tr := Tr) (X := X) weights Zp Bs.G₀).place) =
    some (k11Row (Rc := Rc) (Tr := Tr) (X := X) weights Zp Bs.G₀).half ∧
  (∀ (fs : List (Fall TS)) (earlier : List (Nat × Nat × List Fmt.DeclaredRound)),
    (k11Lettered (Rc := Rc) (Tr := Tr) (X := X) weights Zp Bs.G₀ A.B).goodAt earlier .own cF.blocksInOrder
      (orderOf A.F) 0 0 fs) ∧
  ∀ (k : Coins A.B) (mid : Addr → Except Refusal (Mid (Local W₀ Rc ProofFile.Inst Tr) X)) (run : Run)
    (st : List (Nat × Nat × List UInt64)) (called : Addr → Bool),
    (∀ n, called ⟨(k11Row (Rc := Rc) (Tr := Tr) (X := X) weights Zp Bs.G₀).place, n⟩ = true →
      ∃ m, mid ⟨(k11Row (Rc := Rc) (Tr := Tr) (X := X) weights Zp Bs.G₀).place, n⟩ = .ok m) →
    (k11Lettered (Rc := Rc) (Tr := Tr) (X := X) weights Zp Bs.G₀ A.B).owedAt cF.blocksInOrder k 0 mid run st
      called

/-- **The simulator of the kind K11, at any filling that lays the kind's lot and no other side of the
kind.** The index type, the randomness type, the reader and the filling are letters. -/
def K11SimulatorOwed : Prop :=
  ∀ (W₀ Rc Tr X₀ X : Type) (P : OnlineProverParts W₀ Rc Tr X₀ X) (weights : W₀ → Weights)
    (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF)
    (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
    (x : VerifiableInference.Desc.First.Look.Place) (A : OnlineProverWithDescription W₀ Rc Tr X₀ X)
    (Bs : ProofFile.PureBase),
    onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A →
    AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    (∃ M ∈ P.lots, M.halves A.Z A.G = (headMergeLot headClaimsByPlace weights).halves A.Z A.G) →
    (∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ KindName.K11) ∨
      M.halves A.Z A.G = (headMergeLot headClaimsByPlace weights).halves A.Z A.G) →
    K11OwedAt weights Zp cF A Bs

/-- **The base prover's search at the kind's place finds the kind's side**, at I's reader. -/
def K11Found : Prop :=
  ∀ (W₀ : Type) (I : WiderIn W₀) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF)
    (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
    (x : VerifiableInference.Desc.First.Look.Place) (A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit)
    (Bs : ProofFile.PureBase),
    baseMaker I Z = .ok A →
    AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    (A.H.first.find? fun g => g.place == IM.k11Place) =
      some (headMergeHalf (headClaimsByPlace Zp Bs.G₀) (I.weights Zp) (_root_.K11.parOf Zp Bs.G₀))

/-- **The simulator's three clauses at the base prover.** -/
def K11SimulatorOwedBase : Prop :=
  ∀ (W₀ : Type) (I : WiderIn W₀) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF)
    (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
    (x : VerifiableInference.Desc.First.Look.Place) (A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit)
    (Bs : ProofFile.PureBase),
    baseMaker I Z = .ok A →
    AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    K11OwedAt (I.weights Zp) Zp cF A Bs

end AtPublicFiles.AtFiles.HonestTerm.K11Term
