-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/TheFirstThread.lean: the invariant along the first chain of
the online part, at a return of the maker.

The protocol has three parts, named by what a user holds. offline: the proof in the key file, on
the committed table. link: from a further encoding to the first. online: the proof for a request
(the proof file). The online part has three chains, the first, the shared and the second.
A thread (Honest/Thread/Thr.lean) is the invariant that ties the verifier's state at each border of
a chain to the honest prover's run. Here the thread of the first chain is one term, firstThread,
of a return A of the maker, of the head at that return, of the run's input and of one structure,
FirstThreadParts, which holds what is supplied from outside this file. Every other argument of
lettersHead is a value.

  letter    value                                                 who gives it
  h         HeadAtReturn.head                                     the head's law at a return
  H         A.H, the prover that the maker returned               the maker
  Q         FirstThreadParts.script                               the senders' record
  test      the falls at the member behind a segment's batching   fallsHead, each kind's records
  carryX    carryExact at the public part                         the code switch's definition
  item      0, the statement's item that holds the index's root   the format (p14Of)
  n₁        F.t₁, the trees of the description's first chain      the description
  n₂        F.t₂, the trees of the description's shared chain     the description
  b₀        339, the border behind the member that hears the reply
  Vd        ReadyInput: the instance's start is fit, the index is in range, the trace the prover's
  Rd        ridersOf (csHead ν st R)                              the table of riders
  ν         3531, the ledger's next free slot behind the head's lookup on the digits
  st        digitsStand: at the head's link what its lookup heard stands for some rounds
  R         heardByAttention: the sentence on the field g         K5's sentence and its laying
  Kp        kpBy fHeadJ at the public numbers of the return       each kind's clause
  w         the run's input

Here F is the online description P5J.F0T at the head's places and first chain.

The shared chain's thread and the second chain's are terms of the same form, sharedThread and
lastThread. Both take the numbers of the library's shared table, HeadAtReturn.sharedNumbers, and the
second chain takes its own item from the library's table, HeadAtReturn.lastMeaning, its form from
HeadAtReturn.lastForm, and its witness from lastWitness: the first chain's Script's witness with the
shared chain's sampled messages laid over it. What else they take stands in SharedThreadParts and
LastThreadParts.
-/
import Johnson.Desc.ProofFile.Honest.AtPure
import Johnson.Desc.ProofFile.Honest.Law.FallFree
import Johnson.Desc.ProofFile.Honest.Law.FallsHead
import Johnson.Desc.ProofFile.Honest.Thread.CsHead
import Johnson.Desc.ProofFile.Honest.Thread.FHeadJ
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.Join
import Johnson.Desc.ProofFile.Honest.Thread.KeepsBy
import Johnson.Desc.ProofFile.Honest.Thread.LastHead
import Johnson.Desc.ProofFile.Honest.Thread.ReadyInput
import Johnson.Desc.ProofFile.Honest.K1.LotJobs
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LaysStands
import Johnson.Desc.ProofFile.Honest.K14.AskedAtShared
import Johnson.Desc.ProofFile.Honest.K14.Holds2
import Johnson.Desc.ProofFile.Honest.K14.SecondBehind
import Johnson.Desc.BlockSlot
import Johnson.Desc.K5.Honest.Law.LookR
import Johnson.Desc.K2.Honest.Carry.Exact
import Johnson.IMR.WrittenList
import Johnson.P5J.FreeShared
import Johnson.P5J.HeadOfLive
import Johnson.P5J.L0.Last
import Johnson.SendSim.Seat.LotW

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Place KindName)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.LinkJoin (batchAt)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS F0T fullLinks)
open VerifierAndGoals (asDescriptionFiles)
open FlashProve (theProofRun)
open VerifierAndGoals.AtTheName (dpZ)
open ProofFile.Honest.K1 (PlaceIn lotJobs)
open OnBytes.SendSim.Seat (wJobs)

/-- **The test that the item totalB of a segment is stated under**: the falls at the member without
a round behind the segment's batching, at the state in front of that member. One list of falls
serves this test and the fall of the acceptance statements. -/
def fallsAfterBatching (falls : List (Fall TS)) (cF : Chain TS ProofFile.Cl) (m : Nat) (s : TS) :
    Option String :=
  fallsBy falls cF.blocksInOrder (14 * m + IM.nAt m + 3) s []

set_option maxRecDepth 1000000 in
/-- The number in fallsAfterBatching is the member behind the segment's batching, at each of the 25
segments of the written list. -/
theorem behind_batching_number :
    (List.range 25).all (fun m => batchAt fullLinks P5J.At.ps m + 1 == 14 * m + IM.nAt m + 3) =
      true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- One member of the written list is of the kind K12: the relation at that kind in keeps speaks of
it alone. -/
theorem one_proximity_test :
    (P5J.At.ps.filter (fun p => p.kind == VerifiableInference.Desc.KindName.K12)).length = 1 := by
  decide +kernel

variable {W₀ Rc Tr X₀ X : Type}

/-- **The head at a return of the maker**: A is what the maker returns at the public files and some
filling; the places and the first chain from which the online description is made; and the
library's head at the return's public part. -/
structure HeadAtReturn (files : VerifierAndGoals.PublicFiles) (A : OnlineProverWithDescription W₀ Rc Tr X₀ X) where
  returned : ∃ filling, onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL filling = .ok A
  places : H2U.Places4
  firstChain : Chain TS ProofFile.Cl
  look : VerifiableInference.Desc.First.Look.Place
  head : AtMgA OnBytes.secondHashFunction files (dpZ files) (theProofRun (asDescriptionFiles files)) A.Z places firstChain
    look

/-- The online description at the head. -/
abbrev HeadAtReturn.description {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : HeadAtReturn files A) :=
  F0T OnBytes.secondHashFunction A.Z h.places h.firstChain

/-- **The ground of the kinds' clauses**: the one that the public part's seat makes; where it makes
none, the return's blank ground. -/
def seatGround (A : OnlineProverWithDescription W₀ Rc Tr X₀ X) : ProofFile.Ground :=
  match ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) with
  | .ok base => base.G₀
  | .error _ => A.G

/-- Where the seat makes a base, the ground is that base's. -/
theorem seatGround_of_base {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} {base : ProofFile.PureBase}
    (hb : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok base) :
    seatGround A = base.G₀ := by
  unfold seatGround
  rw [hb]

/-- **The stated numbers of the first chain's falls**, as in fallsHead: no fall's test reads them. -/
structure FallNumbers where
  /-- the two numbers of which the stated number of the fall of the smallness test's columns is made
  -/
  columns : Nat → Nat
  tau : Nat → Nat
  /-- the stated number of the fall of the smallness test's share -/
  share : Nat → Odds
  /-- the chance that the state in front of a batching is not good -/
  notGood : Nat → Odds
  /-- the rounds in front of the first round of a feed-forward segment -/
  roundsBefore : Nat → Nat

/-- **The first chain's falls at a return.** -/
def firstFalls (A : OnlineProverWithDescription W₀ Rc Tr X₀ X) (n : FallNumbers) : List (Fall TS) :=
  fallsHead A.Z (seatGround A) n.columns n.tau n.share n.notGood n.roundsBefore

/-- **Where the falls behind a batching say nothing, each fall seated at that member says
nothing.** -/
theorem silent_of_fallsAfterBatching {falls : List (Fall TS)} {cF : Chain TS ProofFile.Cl} {m : Nat}
    {s : TS} {blk : VerifiableInference.Desc.Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[14 * m + IM.nAt m + 3]? = some blk)
    (h : fallsAfterBatching falls cF m s = none) {F : Fall TS} (hF : F ∈ falls)
    (hp : F.place = blk.place) : F.test s [] = none := by
  unfold fallsAfterBatching fallsBy at h
  rw [hb] at h
  unfold fallOf at h
  rw [List.findSome?_eq_none_iff] at h
  exact h F (List.mem_filter.2 ⟨hF, by simp [hp]⟩)

/-- **K9's share at the member behind the batching is silent where the test is.** -/
theorem quiet_of_fallsAfterBatching {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} {n : FallNumbers}
    {cF : Chain TS ProofFile.Cl} {l : Nat} {s : TS} {blk : VerifiableInference.Desc.Block TS ProofFile.Cl}
    (hl : l < 25) (hb : cF.blocksInOrder[14 * l + IM.nAt l + 3]? = some blk)
    {p : VerifiableInference.Desc.K9.Where}
    {u : VerifiableInference.Desc.K9.SegSort × Nat × VerifiableInference.Desc.K9.TWhere}
    (hp : IM.k9At A.Z l = some p)
    (hu : VerifiableInference.Desc.K9.testsWhere A.Z.p.X l 0 = some u)
    (hq : K9.quietPlace p = blk.place)
    (h : fallsAfterBatching (firstFalls A n) cF l s = none) :
    K9.freeSlotShare u.2.2.filled s = none :=
  silent_of_fallsAfterBatching hb h (fallsHead_quiet hl hp hu) hq

/-- **The smallness test's share at the member behind the batching is silent where the test is.** -/
theorem share_of_fallsAfterBatching {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} {n : FallNumbers}
    {cF : Chain TS ProofFile.Cl} {l : Nat} {s : TS} {blk : VerifiableInference.Desc.Block TS ProofFile.Cl}
    (hl : l < 25) (hb : cF.blocksInOrder[14 * l + IM.nAt l + 3]? = some blk)
    {Xl : OnBytes.Model.Stages.LinkH} (hX : (seatGround A).built[l]? = some Xl)
    (hq : K8.quietPlace l (oAt l) = blk.place)
    (h : fallsAfterBatching (firstFalls A n) cF l s = none) :
    K8.k8Share (ProofFile.k8ParW A.Z (seatGround A) Xl l).nU s = none :=
  silent_of_fallsAfterBatching hb h (fallsHead_share hl hX) hq

/-- The ledger's next free slot behind the output head's lookup on the digits: the value that
lays_nextHead_3531 (Honest/K3/Law/Thread/LaysNextLight.lean) lays. -/
def nextSlotBehindTheHead : Nat := 3531

/-- **What the lookup on the digits of a segment establishes**: at the output head's link, that what
the lookup has heard stands for some rounds, at the place's first slot. Items of that link ride past
the head's merge on it. At the other links no member reads the clause. -/
def digitsStand (publicPart : ProofFile.Pub) (l : Nat) (s : TS) : Prop :=
  l = 24 → ∀ p, VerifiableInference.Desc.First.Look.placeAt publicPart.p.X 24 true = some p →
    ProofFile.Honest.K3.Law.AtThr.StandsHere true 5 p.first s

/-- **What the lookup on the calls of attention segment g returned**: the sentence on the field g
(lookR, Johnson/Desc/K5/Honest/Law/LookR.lean), at the segment's plan. -/
def heardByAttention (publicPart : ProofFile.Pub) (g : Nat) (o : Option OnBytes.Model.Forest.Heard) :
    Prop :=
  ∀ a, (P5J.At.X publicPart).A[g]? = some a → H2K5.Honest.lookR a o

/-- **What the first thread takes from outside this file.** -/
structure FirstThreadParts (A : OnlineProverWithDescription W₀ Rc Tr X₀ X) where
  /-- the honest prover's messages and tables as functions of the coins, the input and the
  challenges -/
  script : Script A.B (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT
  /-- the stated numbers of the falls -/
  numbers : FallNumbers

/-- **The senders' record**: what the first chain's Script is laid from. Of the first chain's
sub-protocols the kinds K1, K2 and K12 alone send oracle messages (sentAtPlace,
Johnson/Desc/K12/Door/SentAtPlace.lean). K1's jobs are written out; others holds the shares of K2's
code switches and K12's proximity test. -/
structure SendersRecord (A : OnlineProverWithDescription W₀ Rc Tr X₀ X) (Xj : Type) where
  /-- a place's number in the first chain's flat list -/
  number : Place → Nat
  /-- the rows' data of K1's lot, and of the sending of W -/
  lotData : ProofFile.Pub → ProofFile.Ground → RowDataOf Xj
  sendingWData : ProofFile.Pub → ProofFile.Ground → RowDataOf Xj
  /-- the stored table's cells, the asked token, and how K1's sender reads the input -/
  cells : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull
  token : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok
  reader : Local W₀ Rc ProofFile.Inst Tr → PlaceIn Xj
  /-- the shares of the senders beside K1 -/
  others : Others A.B (Local W₀ Rc ProofFile.Inst Tr)

/-- **The Script of a senders' record**: the join of K1's jobs and the other senders' shares. -/
def SendersRecord.script {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} {Xj : Type}
    (h : HeadAtReturn files A) (r : SendersRecord A Xj) :
    Script A.B (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT :=
  joinQ h.firstChain.blocksInOrder 0 r.cells r.token (P5J.At.arr A.Z) r.reader A.H.own₀
    (byNo h.firstChain.blocksInOrder
      (lotJobs r.number r.lotData A.Z (seatGround A) ++
        wJobs r.number r.sendingWData A.Z (seatGround A)))
    r.others

/-- **The first thread's Script is the join of a senders' record.** -/
def ScriptIsTheSenders {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : HeadAtReturn files A) (parts : FirstThreadParts A) : Prop :=
  ∃ (Xj : Type) (r : SendersRecord A Xj), parts.script = SendersRecord.script h r

/-- **Each kind's clause of keeps, at the public numbers of a return.** -/
def firstClauses {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : HeadAtReturn files A) :
    KindName → Place → TS → TS → Prop :=
  fHeadJ A.Z h.firstChain (seatGround A) P1L20.bearing (K11.parOf A.Z (seatGround A))
    (H2U.p12OfMade A.Z.made) (VerifiableInference.Desc.K13.whereOf A.Z) h.head.𝔇.pubD

/-- **The first chain's letters at a return of the maker, at the run's input.** -/
def firstLetters {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : HeadAtReturn files A)
    (parts : FirstThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr) :=
  lettersHead h.head A.H parts.script
    (fallsAfterBatching (firstFalls A parts.numbers) h.firstChain)
    (carryExact A.Z (P5J.At.arr A.Z)) 0 h.description.t₁ h.description.t₂ 339
    (ReadyInput h.description A.H)
    (ridersOf (csHead nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z)))
    (kpBy (firstClauses h)) w

/-- **The first thread at a return of the maker.** -/
def firstThread {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : HeadAtReturn files A)
    (parts : FirstThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr) :=
  (firstLetters h parts w).thread

/-- **The first thread is lettersHead's thread at these values, to the letter.** -/
theorem firstThread_is {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : HeadAtReturn files A)
    (parts : FirstThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr) :
    firstThread h parts w =
      (lettersHead h.head A.H parts.script
        (fallsAfterBatching (firstFalls A parts.numbers) h.firstChain)
        (carryExact A.Z (P5J.At.arr A.Z)) 0 h.description.t₁ h.description.t₂ 339
        (ReadyInput h.description A.H)
        (ridersOf (csHead nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z)))
        (kpBy (fHeadJ A.Z h.firstChain (seatGround A) P1L20.bearing
          (K11.parOf A.Z (seatGround A)) (H2U.p12OfMade A.Z.made)
          (VerifiableInference.Desc.K13.whereOf A.Z) h.head.𝔇.pubD)) w).thread := rfl

/-- **The first thread of a run**: at the input that ready hands the chain. -/
def firstThreadOfRun {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : HeadAtReturn files A)
    (parts : FirstThreadParts A) (R : Ready W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X) :=
  firstThread h parts R.own

/-! ## The shared and the second chain -/

open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.Shared (Msg2 NumbersS MeaningS)
open VerifiableInference.Desc.Last (MeaningL PromMeaningL)

section Library
variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : HeadAtReturn files A)

/-- The shared chain's numbers, tied to the first chain's, in the library's table. -/
def HeadAtReturn.sharedNumbers : NumbersS :=
  _root_.Desc.K14.Law.Sh.nums h.head.toAtMg.shPlan (h.head.toAtMg.shOpen h.head.𝔇)

/-- The shared chain's items' meaning in the library's table. -/
def HeadAtReturn.sharedMeaning :=
  _root_.Desc.K14.Law.Sh.mg h.head.toAtMg.shPlan (h.head.toAtMg.shOpen h.head.𝔇)

/-- The second chain's one item of its own, in the library's table. -/
def HeadAtReturn.lastMeaning :=
  P5J.L0.mlAt OnBytes.secondHashFunction (dpZ files) A.Z h.places h.firstChain

/-- The second chain's form: the filling at the two chains' own records. -/
def HeadAtReturn.lastForm :
    PromMeaningL Desc.K14.St VerifiableInference.Desc.Third.S₃ (ProofFile.InstPub × TS) :=
  VerifiableInference.Desc.Last.fillZ (ToldDesc.p14At A.Z) (LLT25.c2 h.places).rounds
    (fun q => q.2)

end Library

/-- **How the index and the committer's coins are read**, at both later chains. -/
structure IndexReaders (W₀ Rc : Type) where
  weights : W₀ → Weights
  rand : Rc → TableRand

/-- What the shared chain's first sending sends. -/
def sentFirstOf (publicPart : ProofFile.Pub) (places : H2U.Places4) : Array OnBytes.OracleNotice :=
  (_root_.Desc.K14.withU (VerifiableInference.Desc.K1.qAt publicPart places).S).getD #[]

/-- **What the shared chain's thread takes from outside this file.** The kind K14 lays its own part
of each letter over these; each is free at K14's borders, members, items and messages. -/
structure SharedThreadParts (A : OnlineProverWithDescription W₀ Rc Tr X₀ X) (Wt : Type) where
  /-- how K14's words are read off a witness -/
  lens : ProofFile.Honest.K14.WitLens Wt
  /-- the items' meaning outside K14's items, at the chain's input -/
  meaning : Common W₀ Rc OnBytes.TableKey → MeaningS Desc.K14.St (ProofFile.InstPub × TS) Wt
  /-- the form outside K14's borders -/
  shape : Nat → Desc.K14.St → Bool
  /-- the witness outside K14's words, as a function of the coins, the input and the challenges -/
  rest : Coins A.B → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn → Wt
  /-- the trees' tables -/
  table : Fmt.TreeSource → Coins A.B → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn → Place × Table
  fixed : Fmt.TreeSource → Nat
  /-- the riders, and what a place's step keeps outside K14's members -/
  rides : Nat → Common W₀ Rc OnBytes.TableKey → Desc.K14.St → Prop
  keeps : Place → Desc.K14.St → Desc.K14.St → Prop

/-- **The shared chain's thread at a return of the maker.** Its flat list, the prover's sides, the
stored table, the first state and the item are lettersShared's values; the two counts of trees are
the description's; the meaning, the form, the order, the witness and keeps are made by K14's own
makers (Johnson/Desc/ProofFile/Honest/K14/AskedAtShared.lean, asked_laid). -/
def sharedThread {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} {Wt : Type}
    (h : HeadAtReturn files A) (reads : IndexReaders W₀ Rc) (parts : SharedThreadParts A Wt)
    (w : Common W₀ Rc OnBytes.TableKey) :=
  (SharedThread.lettersShared A.Z h.places h.firstChain A.H h.sharedNumbers
    (fun v => ProofFile.Honest.K14.mgWords parts.lens (VerifiableInference.Desc.K1.qAt A.Z h.places)
      h.sharedNumbers (parts.meaning v))
    (ProofFile.Honest.K14.form2 (VerifiableInference.Desc.K1.qAt A.Z h.places) parts.shape)
    (fun d => (_root_.Desc.K14.ended d).isSome) (fun s => OnBytes.Means.InOrder s.st)
    (ProofFile.Honest.K14.witL parts.lens (VerifiableInference.Desc.K1.qAt A.Z h.places)
      (sentFirstOf A.Z h.places)
      (ProofFile.Honest.K14.holds2 (VerifiableInference.Desc.K1.qAt A.Z h.places) reads.weights
        reads.rand) parts.rest)
    parts.table parts.fixed h.description.t₁ h.description.t₂
    (fun v => A.H.inRange v.w₀ = true) parts.rides
    (ProofFile.Honest.K14.kp2 (VerifiableInference.Desc.K1.qAt A.Z h.places) (sentFirstOf A.Z h.places)
      parts.keeps)
    w).thread

/-- **What the second chain's thread takes from outside this file.** -/
structure LastThreadParts (A : OnlineProverWithDescription W₀ Rc Tr X₀ X) where
  /-- the items' meaning, at the run's input -/
  meaning : Local W₀ Rc ProofFile.Inst Tr → MeaningS Desc.K14.St (ProofFile.InstPub × TS) WtF
  /-- the trees taken over from the two earlier chains -/
  taken : List Fmt.TreeSource
  /-- the two earlier chains' last states, as functions of the coins, the input and the challenges
  -/
  ends : Coins A.B → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → (ProofFile.InstPub × TS) × Desc.K14.St
  /-- the trees' tables as functions of the coins, the input and the challenges -/
  table : Fmt.TreeSource → Coins A.B → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Place × Table
  fixed : Fmt.TreeSource → Nat
  /-- the riders, and what each place's step keeps -/
  rides : Nat → Local W₀ Rc ProofFile.Inst Tr → VerifiableInference.Desc.Third.S₃ → Prop
  keeps : Place → VerifiableInference.Desc.Third.S₃ → VerifiableInference.Desc.Third.S₃ → Prop

/-- **A message's table from its words**: the inverse of the reading wordsOn
(Johnson/Desc/Means/ItemsTab.lean): the word at a row and a place of a part stands at the index
row + place · 2 ^ (the bits of a row). -/
def tableOfWords (shape : OnBytes.OracleShape) (words : OnBytes.Part → Nat → Cb.Gl.E) :
    MsgT :=
  fun mask row place =>
    let part := if mask then OnBytes.Part.mask else OnBytes.Part.main
    words part (row + place * 2 ^ OnBytes.ceilLog2 (shape.rows part))

/-- Read back at a real row of a message of that shape, the table gives the words. -/
theorem wordsOn_tableOfWords {S : OnBytes.Statement} {o : Nat} {x : OnBytes.OracleNotice}
    (hx : (S.oracles[o]?).map (·.shape) = some x.shape)
    (words : OnBytes.Part → Nat → Cb.Gl.E) (part : OnBytes.Part) (i : Nat)
    (hr : i % 2 ^ S.rowBits o part < OnBytes.Means.realRows S o part) :
    OnBytes.Means.wordsOn S (fun _ => tableOfWords x.shape words) o part i = words part i := by
  have hb : S.rowBits o part = OnBytes.ceilLog2 (x.shape.rows part) := by
    unfold OnBytes.Statement.rowBits
    cases h : S.oracles[o]? with
    | none => rw [h] at hx; cases hx
    | some y =>
      rw [h] at hx
      have e : y.shape = x.shape := Option.some.inj hx
      simp [e]
  unfold OnBytes.Means.wordsOn
  rw [if_pos hr]
  unfold tableOfWords
  rw [hb]
  cases part <;> simp [Nat.mod_add_div']

/-- The shape of each of the shared chain's three sampled messages, by the plan. -/
def sharedShape (publicPart : ProofFile.Pub) (places : H2U.Places4) : Msg2 → OnBytes.OracleShape
  | .oU => ((sentFirstOf publicPart places).getD 0 default).shape
  | .oOmega =>
    ((_root_.Desc.K14.withOmega (VerifiableInference.Desc.K1.qAt publicPart places).S).getD 0
      default).shape
  | .oSp =>
    ((_root_.Desc.K14.withOmega (VerifiableInference.Desc.K1.qAt publicPart places).S).getD 1
      default).shape

/-- **A sampled message of the shared chain as a table**: K14's honest words at its number in that
chain, at the coins, that chain's input and its challenges. -/
def sharedTable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : HeadAtReturn files A)
    (reads : IndexReaders W₀ Rc) (k : Coins A.B) (input : Common W₀ Rc OnBytes.TableKey)
    (heard : List Fmt.Drawn) (m : Msg2) : MsgT :=
  tableOfWords (sharedShape A.Z h.places m) fun part i =>
    _root_.Desc.K14.Honest.words2 (VerifiableInference.Desc.K1.qAt A.Z h.places)
      (sentFirstOf A.Z h.places)
      (_root_.Desc.K14.first (VerifiableInference.Desc.K1.qAt A.Z h.places).codes input.key)
      (ProofFile.Honest.K14.firstRv heard)
      (ProofFile.Honest.K14.holds2 (VerifiableInference.Desc.K1.qAt A.Z h.places) reads.weights reads.rand
        k input)
      (ProofFile.Honest.K14.num m) part i

/-- **The second chain's witness**: the first chain's Script's witness, with the shared chain's three
sampled messages laid over it at their seats. The second chain reads both: the rows of its own group
name the first chain's messages, and Omega is the shared chain's. The shared chain's part is read at
that chain's input and at the challenges behind the first chain's. -/
def lastWitness {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : HeadAtReturn files A)
    (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc) (k : Coins A.B)
    (w : Local W₀ Rc ProofFile.Inst Tr) (heard : List Fmt.Drawn) : WtF :=
  let v := first.script.wit k w heard
  let input : Common W₀ Rc OnBytes.TableKey := ⟨w.w₀, w.rc, A.H.key w.x⟩
  let behind := heard.drop (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length
  let table := sharedTable h reads k input behind
  let sampled : List Msg2 := [.oU, .oOmega, .oSp]
  let tenant := h.sharedNumbers.tenant
  { v with
    msg := fun n =>
      match sampled.find? fun m => P5J.At.arr A.Z (tenant m).1 (tenant m).2 == n with
      | some m => table m
      | none => v.msg n
    pad := fun j t =>
      match sampled.find? fun m => tenant m == (j, t) with
      | some m => table m
      | none => v.pad j t }

/-- **The three sampled messages of the shared chain have numbers of their own**: the numbering keeps
them apart, and apart from every message of the first chain's trees. lastWitness lays them at these
numbers, so it is read as meant where this holds. -/
def SharedTenantsApart {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : HeadAtReturn files A) :
    Prop :=
  Function.Injective (fun m : Msg2 =>
      P5J.At.arr A.Z (h.sharedNumbers.tenant m).1 (h.sharedNumbers.tenant m).2) ∧
    ∀ m j t, j < h.description.t₁ →
      P5J.At.arr A.Z j t ≠ P5J.At.arr A.Z (h.sharedNumbers.tenant m).1 (h.sharedNumbers.tenant m).2

/-- **The second chain's thread at a return of the maker.** The label of its first own tree, its
flat list, the prover's sides, the rounds ahead, the stored table and the first state are
lettersLast's values; the item is 0 and the two counts of trees are the description's. -/
def lastThread {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
    (parts : LastThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr) :=
  (LastThread.lettersLast A.Z h.places h.firstChain A.H h.sharedNumbers parts.meaning
    h.lastMeaning h.lastForm (fun s => OnBytes.Means.InOrder s.st) parts.taken parts.ends
    (lastWitness h first reads) parts.table
    parts.fixed 0 h.description.t₁ h.description.t₂ (ReadyInput h.description A.H) parts.rides
    (ProofFile.Honest.K14.kpSecond (ToldDesc.p14At A.Z) parts.keeps) w).thread

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.firstThread
#print axioms ProofFile.Honest.FirstThread.firstThread_is
#print axioms ProofFile.Honest.FirstThread.firstThreadOfRun
#print axioms ProofFile.Honest.FirstThread.sharedThread
#print axioms ProofFile.Honest.FirstThread.lastThread
#print axioms ProofFile.Honest.FirstThread.behind_batching_number
#print axioms ProofFile.Honest.FirstThread.one_proximity_test
#print axioms ProofFile.Honest.FirstThread.seatGround_of_base
#print axioms ProofFile.Honest.FirstThread.ScriptIsTheSenders
#print axioms ProofFile.Honest.FirstThread.wordsOn_tableOfWords
#print axioms ProofFile.Honest.FirstThread.lastWitness
#print axioms ProofFile.Honest.FirstThread.silent_of_fallsAfterBatching
#print axioms ProofFile.Honest.FirstThread.quiet_of_fallsAfterBatching
#print axioms ProofFile.Honest.FirstThread.share_of_fallsAfterBatching
