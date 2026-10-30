-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Term/ValuesStatements.lean: THE OUTPUT HEAD's OWN ROUNDS (the kind
K6 of the online proof): WHAT THIS KIND OWES TO "THE RUN ON SHAPES", AS STATEMENTS. Definitions
alone. The proofs: Honest/K6/Term/Values.lean.

WHAT IT IS NOT.
  * Nothing is proved here: every statement is a definition of type Prop.
  * None of them says that a verifier accepts a proof, or that a member's step accepts. ValuesJ
    (Honest/Thread/ShapeJV.lean) is one premise of another house's rule
    (Johnson/AtFull/Shape/RuleAtTable.lean); that rule asks besides that
    the run on shapes returns over all 358 members, and a test on the prover's sides (halved); and
    the file's rule for acceptance asks much more.
  * THEY MAY HOLD FOR NOTHING. The eight statements at a border stand under the library's hypothesis
    on the first chain (h), and each begins "wherever the thread's invariant holds in front of the
    member, and what is said with it". At letters at which that invariant holds at no run up to
    border 341 (or 347) they say nothing. Whether it holds there is other kinds' debt and the
    frame's. WHOSE THE CLAUSES ARE THAT ARE SPENT: at 341 the record comes out of the promise's item
    "left 24", which the lookup's member 340 lays, and "a token is heard" out of the item that the
    reply's member 338 lays; the test on the request comes from "the state was made by the chain's
    steps". At 347 the record comes out of the item "leftOn 24", which this kind's own member lays
    and the five members 342 to 346 hand on. ValuesJ has six premises more (a member stands at the
    number, the family J holds at the state, the draws fit, nothing of the member stops, no fall
    speaks, the prover's side has moved): NONE OF THEM IS SPENT.
  * NOT THE WHOLE FIELD AT MEMBER 347. The batching's test on values (cellV,
    Johnson/AtFull/Shape/BatchCells.lean) asks that the ledger of the fork is empty and, along
    eleven rows, each row's own test. Four rows are this kind's. Of the ledger and of the test
    eqPreB of the row "K8.equations" nothing is said here (the six other rows' tests always accept).
  * THE TWO TESTS ARE LIGHT. They compare no value that this kind's prover sends: they read what the
    lookup on the calls left in the verifier's state, and the request's words. What is shown is that
    the verifier's own book-keeping in front, as the thread's invariant has it, passes them.
  * Nothing on soundness or on what a proof hides.

WORDS. A border is the point in front of a member of a chain's flat list; border 341 is in front of
this kind's member, border 347 in front of the batching member of the head's link. A thread is the
structure of parameters of one chain's invariant; its parameters are called letters. A row is one
run of claims of the batching member, with its run on shapes and its own test (Row,
BatchCells.lean). "What the lookup heard" is the record that the lookup on the calls lays in the
verifier's state (the reader S.lookHeard?, Johnson/Desc/First/State.lean).

WHAT IT IS.
  HeadTestAcceptsAtTheBorder      wherever the invariant holds at border 341: the table's test on
                                  values at this kind's member (k6V) accepts the state
  ValuesAtTheOutputHeadAtAnyShape the field "head": ValuesJ at 341, at every shape whose test at 341
                                  is k6V, every family J and every fall
  ValuesAtTheOutputHead           the same at the table's own shape, at every ground
  KeepsWhatTheLookupHeard run     a run of claims, where it returns, leaves that record as it was
  behindTheRuns                   the count and the state behind a list of runs, run one behind the
                                  other as the batching's test runs them; none where one refuses
  EachRowsTestGivesTheBatchingsTest   WHY THE FORM FITS: the batching's test along the rows
                                  (preAllT, Johnson/AtFull/Shape/BatchTerms.lean) accepts if each
                                  row's test accepts at every state that the runs in front of it
                                  reach. General; no premise on the runs
  HeadRowsKeepWhatTheLookupHeard  each of the eleven rows' runs at the head's link, behind its
                                  guard, leaves the record; so does the idle row's (it never
                                  returns). At all public parameters. No premise
  LookupIsHeardAtTheBatching      wherever the invariant holds at border 347: the record is laid,
                                  and the four rows' one test on values (endsB) accepts it: the
                                  library's EndsHeard (Johnson/Desc/K6/Shape/Pays.lean). The library
                                  has it at a state reached there (endsHeard_347,
                                  K6/Shape/PaysAtBatch.lean); here it is had from the invariant's
                                  clause on the promise, and nothing is read of the sentence Said
  EndsTestAcceptsWhereTheLookupIsHeard   THE HALF THAT NAMES NO THREAD: at every state at which
                                  EndsHeard holds, endsS accepts. General in the public numbers
  EndsTestAcceptsAtTheBatching    THE ONE SENTENCE THAT THE FIELD "batchHead" ASKS OF THESE ROWS
                                  (the row's test holds at the stand; the way from the stand to
                                  each run is paid there): wherever the
                                  invariant holds at border 347, endsS accepts the state
  EndsTestAcceptsAtTheBatchingInTheTablesLetters   the same, and EndsHeard, at the public parameters
                                  as the table names them
  EndsTestAcceptsAtEveryStandOfTheBatching   the same in the form of that field's own premise
  HeadRowsTestsAcceptAlongTheRows MORE THAN THE FIELD ASKS: THE ROWS' SHARE OF IT, WITH
                                  THE WAY PAID: wherever the invariant holds at border 347, behind
                                  the draw, at every state that runs of the head's rows reach,
                                  whichever and in whatever order: EndsHeard holds, endsS accepts,
                                  and so does the test of each of the rows "norm", "join", "policy",
                                  "logits"

WHICH ARM OF endsS IS MET. endsS (Johnson/AtFull/Shape/BatchBools.lean) says yes where no record is
laid. THAT ARM IS NOT THE ONE MET: the record is laid at each of these states (EndsHeard says so).

THE VALUE. No filling, no prover's side and no seat is named: of the prover H the first chain's
thread reads the first chain's sides and the stored tables' words, and these statements spend
neither. The types of the index, of the stored tables' randomness, of the trace and of a side's own
state are letters; all thirteen letters of the thread (lettersHead, Honest/Thread/FirstHead.lean)
and the sentence Said are bound by ∀. So they hold at the base prover's threads and at the threads
of the prover read through alike. NO PREMISE ON THE LETTER b₀ (the border from which the state holds
the reply) is needed, nor on any other letter.

THE PREMISES, AND WHOSE EACH IS.
  h    the library's hypothesis on the first chain at the three public files (P5J.AtMgA).
  the base (the three last statements alone): ProofFile.baseOf returns Bs at the public part. It names the
       public parameters as the table names them (Bs.G₀.W). Under h it is met by one Bs
       (h.laid.opened).
-/
import Johnson.AtFull.Shape.RuleAtTable
import Johnson.Desc.K6.Shape.Pays
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6.Term
open VerifiableInference.Desc (Chain Strs Place Claim)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Kinds.Head (parOf)
open VerifiableInference.Desc.Kinds.Head.Law (workAtW)
open VerifiableInference.Desc.Kinds.Head.Shape (EndsHeard)
open VerifiableInference.Desc.K9 (Where atS drawAlone)
open VerifiableInference.Desc.K9.Shape (guardRun)
open Johnson.AtFull.Shape (k6V endsS rowsHead tabOf firstZA preAllT Tab.g Tab.vals)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)

/-- A run of claims, as a sub-protocol states it: from the running count of claims and a state to
the claims and the state behind, or a refusal. -/
local notation "RunOfClaims" => VerifiableInference.Desc.K9.Shape.Run

/-! ## 1 The field "head": the test on values at member 341 -/

/-- **Wherever the first chain's invariant holds at border 341, and what is said with it, the
table's test on values at the output head's own rounds accepts the verifier's state**: the state's
own test on the request's words accepts; what the lookup heard is laid; each call's key point has
the size that the head's text asks and ends as the lookup's point does. -/
def HeadTestAcceptsAtTheBorder : Prop :=
  ∀ (W₀ Rc Tr X : Type) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Ky X₀ : Type) (H : Prover W₀ Rc Inst Ky Tr X₀ X) (Bk : ProverCoinCounts)
    (Q : Script Bk (Local W₀ Rc Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop)
    (k : Coins Bk) (s : TS) (m : Mid (Local W₀ Rc Inst Tr) X) (E : Env),
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E →
    k6V (P5J.At.X Zp) s = true

/-- **The field "head", at any shape**: the values at member 341, at every shape whose test on
values at 341 is k6V at the description's public parameters, at every family J and every fall. -/
def ValuesAtTheOutputHeadAtAnyShape : Prop :=
  ∀ (W₀ Rc Tr X : Type) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Ky X₀ : Type) (H : Prover W₀ Rc Inst Ky Tr X₀ X) (Bk : ProverCoinCounts)
    (Q : Script Bk (Local W₀ Rc Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop)
    (shape : Shape TS) (J : Nat → TS → Prop) (fall : Nat → TS → List Fmt.Drawn → Option String),
    (∀ s rounds shown, shape.vals 341 s rounds shown = k6V (P5J.At.X Zp) s) →
    ValuesJ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said J shape fall
      341

/-- **The field "head", at the table's own shape**: at every ground, every family J (so at the run
on shapes from the written first shape) and every fall. -/
def ValuesAtTheOutputHead : Prop :=
  ∀ (W₀ Rc Tr X : Type) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Ky X₀ : Type) (H : Prover W₀ Rc Inst Ky Tr X₀ X) (Bk : ProverCoinCounts)
    (Q : Script Bk (Local W₀ Rc Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop)
    (G : Ground) (J : Nat → TS → Prop) (fall : Nat → TS → List Fmt.Drawn → Option String),
    ValuesJ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said J
      (firstZA (Tab.g Zp G) (Tab.vals Zp G)) fall 341

/-! ## 2 The form in which a row's house pays its test at a batching member -/

/-- A run of claims, wherever it returns, leaves what the lookup heard as it was. -/
def KeepsWhatTheLookupHeard (run : RunOfClaims) : Prop :=
  ∀ (count : Nat) (state : TS) (y : List Claim × TS), run count state = .ok y →
    y.2.lookHeard? = state.lookHeard?

/-- The running count of claims and the state behind the runs that a list names, run one behind the
other from a count and a state, as the batching's test on values runs them (preAllT). Where one of
them refuses: none. -/
def behindTheRuns (runOf : Nat × String → RunOfClaims) :
    List (Nat × String) → Nat → TS → Option (Nat × TS)
  | [], count, state => some (count, state)
  | name :: names, count, state =>
    match runOf name count state with
    | .ok y => behindTheRuns runOf names (count + y.1.length) y.2
    | .error _ => none

/-- **Why the form fits**: the batching's test along the rows accepts, if each row's own test
accepts at every count and state that the runs in front of that row reach. General in the two
tables. -/
def EachRowsTestGivesTheBatchingsTest : Prop :=
  ∀ (runOf : Nat × String → RunOfClaims) (testOf : Nat × String → Nat → TS → Bool)
    (names : List (Nat × String)) (count : Nat) (state : TS),
    (∀ front name rest, names = front ++ name :: rest → ∀ count' state',
      behindTheRuns runOf front count state = some (count', state') →
      testOf name count' state' = true) →
    preAllT runOf testOf names count state = true

/-! ## 3 The four rows of the head's link: the test on values at member 347, this kind's share -/

/-- **Each run of the head's link's table of rows, behind its guard, leaves what the lookup heard**:
the eleven rows' runs, and the idle row's under every other name. At all public parameters and at
both of the table's numbers. No premise. -/
def HeadRowsKeepWhatTheLookupHeard : Prop :=
  ∀ (W : OnBytes.Model.Verify.Public) (readsArray planesLog : Nat) (name : Nat × String),
    KeepsWhatTheLookupHeard (guardRun sameReply (tabOf (rowsHead W readsArray planesLog) name).run)

/-- **Wherever the first chain's invariant holds at border 347, what the lookup heard is laid, and
the four rows' one test on values accepts it**: the last coordinates of each call's key point are
those of the lookup's point. -/
def LookupIsHeardAtTheBatching : Prop :=
  ∀ (W₀ Rc Tr X : Type) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Ky X₀ : Type) (H : Prover W₀ Rc Inst Ky Tr X₀ X) (Bk : ProverCoinCounts)
    (Q : Script Bk (Local W₀ Rc Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop)
    (k : Coins Bk) (s : TS) (m : Mid (Local W₀ Rc Inst Tr) X) (E : Env),
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 347 k s m E →
    EndsHeard (parOf (P5J.At.X Zp).hS (workAtW (P5J.At.X Zp))) s

/-- **The half that names no thread**: at every state at which what the lookup heard is laid and
passes the one test on values, endsS accepts. -/
def EndsTestAcceptsWhereTheLookupIsHeard : Prop :=
  ∀ (numbers : VerifiableInference.Desc.Kinds.Head.Par) (s : TS),
    EndsHeard numbers s → endsS numbers s = true

/-- **AT THE STAND**: wherever the first chain's invariant holds at border 347, the test of this
kind's four rows accepts the state. -/
def EndsTestAcceptsAtTheBatching : Prop :=
  ∀ (W₀ Rc Tr X : Type) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Ky X₀ : Type) (H : Prover W₀ Rc Inst Ky Tr X₀ X) (Bk : ProverCoinCounts)
    (Q : Script Bk (Local W₀ Rc Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop)
    (k : Coins Bk) (s : TS) (m : Mid (Local W₀ Rc Inst Tr) X) (E : Env),
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 347 k s m E →
    endsS (parOf (P5J.At.X Zp).hS (workAtW (P5J.At.X Zp))) s = true

/-- **At the stand, in the table's own letters**: the same, and EndsHeard, at the public parameters
as the table names them. -/
def EndsTestAcceptsAtTheBatchingInTheTablesLetters : Prop :=
  ∀ (W₀ Rc Tr X : Type) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Ky X₀ : Type) (H : Prover W₀ Rc Inst Ky Tr X₀ X) (Bk : ProverCoinCounts)
    (Q : Script Bk (Local W₀ Rc Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop)
    (Bs : PureBase) (k : Coins Bk) (s : TS) (m : Mid (Local W₀ Rc Inst Tr) X) (E : Env),
    baseOf Zp (pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 347 k s m E →
    EndsHeard (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) s ∧
      endsS (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) s = true

/-- **At the stand, in the form in which the field "batchHead" asks it** (its
premise "ends" of batch_values_head, with its StandJ written out): at every state at which the
invariant holds at some coins and some state of the prover's run, and a family J besides, which is
not spent. The number is written as that house writes it. -/
def EndsTestAcceptsAtEveryStandOfTheBatching : Prop :=
  ∀ (W₀ Rc Tr X : Type) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Ky X₀ : Type) (H : Prover W₀ Rc Inst Ky Tr X₀ X) (Bk : ProverCoinCounts)
    (Q : Script Bk (Local W₀ Rc Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop)
    (Bs : PureBase) (J : Nat → TS → Prop) (s : TS),
    baseOf Zp (pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    (∃ k m E, ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (337 + 10) k s m E ∧ J (337 + 10) s) →
    endsS (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) s = true

/-- **THE ROWS' SHARE OF THE FIELD "batchHead"**: wherever the invariant holds at border 347: behind
the batching's draw, at every count and state that runs of the head's table of rows reach (whichever
names, in whatever order, from whatever count): what the lookup heard is laid and passes the one
test on values; so endsS accepts the state, and so does the test of each of this kind's four rows.
In the table's own letters. -/
def HeadRowsTestsAcceptAlongTheRows : Prop :=
  ∀ (W₀ Rc Tr X : Type) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Ky X₀ : Type) (H : Prover W₀ Rc Inst Ky Tr X₀ X) (Bk : ProverCoinCounts)
    (Q : Script Bk (Local W₀ Rc Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop)
    (Bs : PureBase) (k : Coins Bk) (s : TS) (m : Mid (Local W₀ Rc Inst Tr) X) (E : Env)
    (place : Where) (rounds : List Fmt.RoundView) (shown : List (List (Nat × List UInt64))) (drawn : TS)
    (readsArray planesLog : Nat) (names : List (Nat × String)) (start count : Nat) (state : TS),
    baseOf Zp (pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 347 k s m E →
    (drawAlone (Cl := Claim) atS place).decide s rounds shown = .ok drawn →
    behindTheRuns
      (fun name => guardRun sameReply (tabOf (rowsHead Bs.G₀.W readsArray planesLog) name).run)
      names start drawn = some (count, state) →
    EndsHeard (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) state ∧
      endsS (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) state = true ∧
      ∀ name ∈ ["norm", "join", "policy", "logits"],
        (tabOf (rowsHead Bs.G₀.W readsArray planesLog) (3, name)).pre count state = true

end ProofFile.Honest.K6.Term
