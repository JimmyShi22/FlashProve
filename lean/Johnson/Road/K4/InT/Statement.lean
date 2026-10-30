-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/InT/Statement.lean: THE STATEMENT, AND NO PROOF: "BEHIND AN ACCEPT OF K4's
SUB-PROTOCOL THE TABLE OF JOINTS' PUBLIC TEST formsInT IS TRUE AT K4's TWO RUNS". Definitions alone:
the sentence (`FormsInTOwn`) and every premise by name. The proofs stand in the files beside
(InT/…).

WHO SPENDS IT. K4's row in the promise's table opens the item formsT m 3 "own"; the public item
formsInT m 3 "own" is tied to it, and K4's row must MAKE it behind its accept (the line make of
`K4Keeps`, K4PromiseBehind.lean). At the table's filling (Johnson/Desc/First/Batch/FormsPub.lean)
that item is: for each of the runs (2, "front"), (2, "back"): `K9.formsInT (Rd m) own piece run s`
(Johnson/Desc/First/Batch/FormsIn.lean), own := the seats of the segment's first sending.

WHAT THE TEST ASKS (by its text): the open segment's part is there · the run's reader answers at the
verifier's state: THE READER IS THE RUN ITSELF (`K9.readerOf`, ReaderOf.lean): the run returns; each
claim is plain; each entry names row 0 of an array with one own row · each slot that the run itself
fills is below the number of slots and free · each form names only what is there: an entry: a cell
of an array that is there or that the segment's second sending will bring; a slot: below the number
of slots, the mask row's seat there, not the merge's slot, filled or filled by the run.

THE SENTENCE (`FormsInTOwn`). `KeptAtS p s s'` (what an accept of K4's sub-protocol leaves) ·
`KeptAsks` (the totality law's premises at the verifier's state: Total/AtKept.lean) · `InTAsks` ·
`StatesAt`, at each of the two names (THE SEAT's TIE, POINTWISE AT s': the run that the readers'
sub-protocol number 2 states does at s' what K4's sub-protocol's run does): then `InTAt` at "front"
and at "back", at s': THE TEST's OWN CLAUSES, UNFOLDED: the part · the reader's answer · the late
slots · every form. WHY UNFOLDED: the table's item stands at a segment's readers
(`K9.readersOfLink`: an if on one name, then the run's own reader, then a hole): another term than
the generic readers: from the unfolded form both follow: `InTOfStates`, `InTOfLink`.

THE PREMISES OF `InTAsks`, EACH WITH ITS PAYER.
  names: what the lookup returned names no entry, and slots alone that are filled in the ledger in
    front of K4's hearing (`Fo.Tp.PadNames`: THE LOOKUP's law).
  hK: the public parameters' number of reads is at most the reads' array's number of columns (the
  public parameters' make). mask: the mask row's message sits at a seat of own (A TEST WITH CODE on
    the verifier's state: the frame's and the book's).
  oneRow (`oneRowB`): the reads' array has one own row in the ledger (A TEST WITH CODE).
  reads (`readsThereB`): the reads' array is in the segment's list of arrays and in the layout,
    belongs to the segment's second sending, has a row, and as many columns as the plan has reads (A
    TEST WITH CODE: the item linkFresh says that the list is the public parameters').

Limits. A SENTENCE: NOTHING IS PROVED HERE. AT THE VERIFIER's STATE RIGHT BEHIND THE YES: that the
test stays true up to the sending of the reads is the sub-protocols' between. `StatesAt` is the
seat's tie: typed by nobody. The three tests
with code have run nowhere as they stand here. K04_law, the law of K4's sub-protocol itself, IS NOT
PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.Total.AtKept
import Johnson.Top.H.Keep.PadNamed
import Johnson.Desc.First.K4.AtC
import Johnson.Desc.First.Batch.ReadersOfLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.InT

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Pub Own)
open OnBytes.Desc.First.K4 (Par blockAtC)
open OnBytes.Desc.First.K4.Total (KeptAsks)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc (Claim Link K9.Part K9.RunOf K9.Readers K9.formsInT K9.segAt?
K9.maskSeat
  K9.atMoment1 K9.Read K9.readerOf K9.lateOk K9.affInT K9.mergeOf K9.LinkHoles K9.statesOfLink
  K9.readersOfLink)

/-- The reads' array has one own row in the ledger. -/
def oneRowB (F : Fork) (iU3 : ℕ) : Bool := (F.trees[iU3]?).any fun T => T.R == 1

/-- The reads' array is in the segment's list and in the layout, belongs to the segment's second
sending, has a row, and at least n columns. -/
def readsThereB (A : K9.Part) (iU3 n : ℕ) : Bool :=
  match A.L.arrayOf[iU3]? with
  | none => false
  | some b =>
    match reqArray A.L.check.rows.layout b.1 b.2 with
    | none => false
    | some Ar => K9.atMoment1 A b Ar && (decide (0 < Ar.sizeI) && decide (n ≤ Ar.sizeC))

/-- **What is asked beside `KeptAtS` and `KeptAsks`.** -/
structure InTAsks (own : List (ℕ × ℕ)) (p : Par) (s s' : S) : Prop where
  names : ∀ a fo, s.here = .lay a → a.fo = some fo → _root_.Fo.Tp.PadNames fo a.F
  hK : ∀ o, s'.own? = some o → p.hp.nU.getD 2 0 ≤ o.v.K3
  mask : ∀ A, K9.segAt? s' = some A → (K9.maskSeat own A).isSome = true
  oneRow : ∀ G o, s'.fork? = some G → s'.own? = some o → oneRowB G o.v.iU3 = true
  reads : ∀ A o, K9.segAt? s' = some A → s'.own? = some o →
    readsThereB A o.v.iU3 (p.hp.nU.getD 2 0) = true

/-- **The seat's tie, POINTWISE**: the readers' sub-protocol number b states, under that name, a run
that
AT THE VERIFIER's STATE s (and the count 0) does what K4's sub-protocol's run of that name does, at
the one
type of a claim.
NOT an equation of lists of functions: a seat may wrap the sub-protocol (a guard in front, a test
behind
each
run): what is asked is the wrapped run's answer at one state. -/
def StatesAt (states : ℕ → List (K9.RunOf S)) (b : ℕ) (p : Par) (name : String) (s : S) : Prop :=
  ∃ (r : K9.RunOf S) (runC : ℕ → S → Except String (List Claim × S)),
    (states b).find? (fun r => r.1 == name) = some r ∧
      (blockAtC p).claims.lookup name = some runC ∧ r.2 0 s = runC 0 s

/-- **What the public test asks, unfolded, for one run**: the segment's part is there; the run's
reader
answers; the late slots pass; every form names only what is there. -/
def InTAt (states : ℕ → List (K9.RunOf S)) (own : List (ℕ × ℕ)) (b : ℕ) (name : String) (s : S) :
    Prop :=
  ∃ (A : K9.Part) (R : K9.Read), K9.segAt? s = some A ∧ K9.readerOf states b name s = some R ∧
    K9.lateOk R.late A = true ∧ ∀ f ∈ R.forms, K9.affInT own (K9.mergeOf s) R.late A f = true

/-- **THE SENTENCE.** -/
def FormsInTOwn : Prop :=
  ∀ (own : List (ℕ × ℕ)) (p : Par) (s s' : S) (P₀ : Pub) (o₀ : Own)
    (states : ℕ → List (K9.RunOf S)), KeptAtS p s s' → KeptAsks p s s' P₀ o₀ →
    InTAsks own p s s' → StatesAt states 2 p "front" s' → StatesAt states 2 p "back" s' →
    InTAt states own 2 "front" s' ∧ InTAt states own 2 "back" s'

/-- The test at the generic readers follows. -/
def InTOfStates : Prop :=
  ∀ (states : ℕ → List (K9.RunOf S)) (own : List (ℕ × ℕ)) (b : ℕ) (name : String) (s : S),
    InTAt states own b name s → K9.formsInT (K9.Readers.ofStates states) own b name s = true

/-- And at a segment's readers, whatever fills their two holes: where the run's own reader answers,
the
holes are not asked. -/
def InTOfLink : Prop :=
  ∀ (H : K9.LinkHoles) (l : Link S Claim) (own : List (ℕ × ℕ)) (b : ℕ) (name : String) (s : S),
    (name == "K8.equations") = false → InTAt (K9.statesOfLink l) own b name s →
    K9.formsInT (K9.readersOfLink H l) own b name s = true

end OnBytes.Road.K4.InT
