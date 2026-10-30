-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/TheOneObject.lean: what the honest online prover owes at every served request, as
one structure, and the premise of completeness that follows from a value of it.

The protocol has three parts, named by what a user holds. offline: the proof in the key file, on the
committed table. link: from a further encoding to the first. online: the proof for a request (the
proof file). The online part has three chains of sub-protocols: the first, the shared, the second.
TheOneObject says: every claim that the honest prover lays is true of its own words, from one
sub-protocol's border to the next, at every coin, outside the falls and behind the block's own yes.
Its letters are the named holes of TheLetters.lean; every other field is a hypothesis. TheThreadsHalf
is what the run's return reads. atTheThreads gives the rule's structure at the three threads;
atEveryTiedRun is an implication from a value to BaseThreadsJAt at the public files;
TheOneObject.threads is the value whose invariants atEveryTiedRunAtItsThreads names.
-/
import AtFullSide.Honest.TheLetters
import AtFullSide.Honest.TheLettersFit
import AtFullSide.Honest.TheSocketStatements
import AtFullSide.Honest.TheThreeThreads
import AtFullSide.Honest.ThreadsPaidAtTheTerm
import AtFullSide.K1.FirstScript
import AtFullSide.K1.FirstScriptFixed
import AtFullSide.K1.FirstScriptIsSenders
import E2E.CompleteAsIOPAtTheSides
import E2E.CompleteAsIOPByBase
import E2E.CompleteAsIOPServedLaws
import E2E.ThruAtTerm
import Johnson.Desc.ProofFile.Honest.K14.AtFilling
import Johnson.Desc.ProofFile.Honest.K9.StepSilent
import Johnson.Desc.ProofFile.Honest.Law.ReadyAny
import Johnson.Desc.ProofFile.Honest.Law.ReadyAtBaseProver
import Johnson.Desc.ProofFile.Honest.Thread.FromThreadsJ
import Johnson.Desc.ProofFile.Honest.Thread.TheLaterThreads
import Johnson.Desc.ProofFile.Honest.ThruAtPure
import Johnson.Desc.ProofFile.Honest.ThruRowsMore
import Johnson.ToldDescR.PureChainOfOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

/-! ## Where the structure stands, and what crosses

The structure stands at the base prover A.H, which the maker returns at matrixFilling, and at the
first chain's Script firstScriptAt. The online prover of honestProvers is that prover read through
the table's coins (onlineProver_is_the_base_read_through). The structure has no field for that
crossing. The form that crosses is ThreadsP with the yes along the run: ThreadsCJ.toP and
ThreadsCJ.along (Honest/ThruAlongFromJ.lean), handed to yesAt_of_base_alongJ
(E2E/ThruYesBaseAlong.lean), which goes by yesAt_of_base (E2E/ThruYesBase.lean) over runC_rows_thru
(Honest/ThruRows.lean). It is crossed once, inside the law that takes BaseThreadsJAt.
 -/

namespace AtFullSide.Honest
open ProofFile.Honest ProofFile.Honest.FirstThread
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Scope
open ProofFile.Honest.Term (matrixInput matrixFilling tableCoins onlineMaker OnlineReturn named_in_range
  ready_at_base_of_online)
open ProofFile.Honest.K1 (firstScriptAt)
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm AtPublicFiles.Committed AtPublicFiles.TheFalls
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifierAndGoals (PublicFiles readFiles InScope)
open LPFD.Full (instanceAsPlainRecord)
open FlashProve (committerCoinCountLessOne)

local instance (priority := high) nonemptyPadZ_theOneObject : Nonempty PadZ :=
  pads_nonempty frS 402653181

/- Given by hand, as in E2E/TheHonestProver.lean: the search for these runs out of its budget. -/
local instance (priority := high) nonemptyRunValue_theOneObject : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_theOneObject : Inhabited RunValue := ⟨fun _ => 0⟩

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn Z A)

/-! ## 1 The letters that have a value -/

/-- **The online return**: the base return read through the table's coins. -/
abbrev onlineReturn (Z : PublicFiles) (A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit) : OnlineReturn Z :=
  A.thru id (tableCoins Z) matrixInput.dummy

/-- **The sides that completeness is stated with**, at the online return. -/
abbrev theSides :=
  sidesForCompleteness (onlineReturn Z A) h.places h.firstChain
    (theSlots (onlineReturn Z A) h.places h.firstChain)

variable {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)

/-- **The inputs of which something is said**: a served request of the index, written with the
out-of-domain sample of this private input, and tied. No out-of-domain seed is set aside. -/
abbrev TiedRequest : ℕ → WZ Z → ProofFile.Inst → Prop :=
  TiedOut Z (onlineReturn Z A).Z h.places h.firstChain runValueBytes runValueBytes
    (onlineReturn Z A).B (theSides h) (onlineReturn Z A).H (ServedRequest committerCoinCountLessOne Z hr)
    fun _ _ => ∅

/-- **One run of the base prover at such an input**: the copy's number, the private input, the
instance, the prover's coin, and what ready returned there. -/
structure TiedRun where
  n : ℕ
  w : WZ Z
  x : ProofFile.Inst
  c : CoinG A.B RunValue RunValue
  R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit
  tied : TiedRequest h hr n w x
  ready : ProofFile.Honest.ready h.description A.B A.H w.1 (tableCoins Z w.2.1) x (pursesOf c) = .ok R

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- The shared chain has no rider. -/
theorem shared_riders_late (O : TheLetters.OpenShared A) :
    ∀ c ∈ (TheLetters.later (h := h) O).riders, 0 < c.lo := by
  intro c hc
  have e : (TheLetters.later (h := h) O).riders = [] := rfl
  rw [e] at hc
  cases hc

/-! ## 2 The structure

Each field's comment names what is laid in it: the term that `theOneObjectValue`
(AtFullSide/Honest/TheOneObjectValue.lean; its premises: h, hr, made, live and the two Inhabited
letters of the frames) lays in the field. Most fields are implications from a thread's invariant, so
this does not show that a thread stands at a run; open₂ is laid at zeros.

The run on shapes in publicData, shapesToEnd and shapesEnd is stated at the stored files
VerifierAndGoals.storedPublicFiles. Under the head, at any files, run_at_scope
(Johnson/AtFull/Shape/Scope/YesAll.lean) relates the run at these files to that one, with no
further premise.

yes₂ and yes₃ stand at empty lists of falls: that no fall is wanted at the later chains is these two
fields, and they are laid. By reading, the step at shared member 3 refuses a
key with a factor 0, and the field tied keeps that input out, not a fall. -/

/-- **WHAT THE RUN'S RETURN READS.** Two letters, then what the premise of completeness asks beside
the invariants, then the sockets of the invariants. The value of ThreadsP stands on this half alone.
-/
structure TheThreadsHalf where
  /-- LETTER. The named hole of the shared chain. One value for all runs. -/
  open₂ : TheLetters.OpenShared A
  /-- LETTER. The named holes of the last chain. One value for all runs. -/
  open₃ : TheLetters.OpenLast h open₂
  /-- the sides' hypotheses for ready at the online return. Laid: `readyDebts_online`, at
  `onlinePayments_at_return`. -/
  readyDebts : ReadyDebts (onlineReturn Z A).F (onlineReturn Z A).B (onlineReturn Z A).H
  /-- the trace is there at every tied input. Laid: `traceAtTied_filled`. -/
  traceAtTied : ∀ n w x, TiedRequest h hr n w x → (A.H.trace w.1 x).isSome = true
  /-- the plan serves. Laid: `planServes_filled`. -/
  planServes : ∀ r : TiedRun h hr, PlanServes A.H r.w.1 (tableCoins Z r.w.2.1) r.R
  /-- Laid: `fix₂_filled`. -/
  fix₂ : Socket.fix₂ h (TheLetters.shared h open₂)
  /-- Laid: `fix₃_filled`. -/
  fix₃ : ∀ r : TiedRun h hr, Socket.fix₃ h (TheLetters.first h) (TheLetters.reads h) (lastParts h (TheLetters.first h) (TheLetters.last h open₃)) r.R
  /-- each tree in the second chain's list of taken trees is declared as taken over. Laid:
  `takenAre_filled`. -/
  takenAre : Socket.takenAre (lastParts h (TheLetters.first h) (TheLetters.last h open₃))
  /-- the first chain's four hypotheses at every member. Laid: `owes₁_filled`. -/
  owes₁ : ∀ r : TiedRun h hr, Socket.owes₁ h (TheLetters.first h) r.R
  /-- the shared chain's. Laid: `owes₂_filled`. -/
  owes₂ : ∀ r : TiedRun h hr, Socket.owes₂ h (TheLetters.reads h) (TheLetters.shared h open₂) r.R
  /-- the second chain's. Laid: `owes₃_whole_filled`. -/
  owes₃ : ∀ r : TiedRun h hr, Socket.owes₃ h (TheLetters.first h) (TheLetters.reads h) (TheLetters.shared h open₂) (lastParts h (TheLetters.first h) (TheLetters.last h open₃)) r.R
  /-- at a member of the second chain with a new tree the sender plays, at the letter without the
  tie. Laid: `playsAtTrees₃_filled`: member 2 alone (TheLetters' last_fresh). -/
  playsAtTrees₃ : ∀ r : TiedRun h hr, Socket.playsAtTrees₃ h (TheLetters.first h) (TheLetters.reads h) (lastParts h (TheLetters.first h) (TheLetters.last h open₃)) r.R
  /-- every member that sends a root has a side. Laid: `rootedSides_filled`. -/
  rootedSides : Socket.rootedSides h
  /-- what the kinds' laws ask of the run's own input: K2's TypedAtRun and K14's KeyIsTheCommitters.
  Laid: `tied_filled`. Spent by K14's five_at_sharedThread and K2's five -/
  tied : ∀ r : TiedRun h hr, Socket.tied (A := A) (TheLetters.reads h) r.R
  /-- at the second chain: each source that a round opens and takes over stands in the list of taken
  trees. Laid: `opensTaken_filled`. -/
  opensTaken : ∀ r : TiedRun h hr, Socket.opensTaken h (TheLetters.first h) (TheLetters.reads h) (lastParts h (TheLetters.first h) (TheLetters.last h open₃)) r.R
  /-- the instance's start is fit. Laid: `startFit_filled`. -/
  startFit : ∀ r : TiedRun h hr, Socket.startFit h r.x
  /-- the request's bytes parse. Laid: `requestParses_filled`. -/
  requestParses : ∀ r : TiedRun h hr, Socket.requestParses h r.x
  /-- the request is served, and the Script meets the honest trace. Laid: `served_filled`. -/
  served : ∀ r : TiedRun h hr, Socket.served h (TheLetters.first h) r.R (pursesOf r.c)
  /-- at the door: the trees taken over, the form, the items and the riders at the second chain's
  first state. Laid: `doorTrees_filled`. -/
  doorTrees : ∀ r : TiedRun h hr, Socket.doorTrees h (TheLetters.first h) (TheLetters.reads h) (TheLetters.shared h open₂) (lastParts h (TheLetters.first h) (TheLetters.last h open₃)) r.R (pursesOf r.c)
  /-- Laid: `doorFive_filled`. -/
  doorFive : ∀ r : TiedRun h hr, Socket.doorFive h (TheLetters.first h) (TheLetters.reads h) (TheLetters.shared h open₂) (lastParts h (TheLetters.first h) (TheLetters.last h open₃)) r.R r.x (pursesOf r.c)
  /-- Laid: `doorRides_filled`. -/
  doorRides : ∀ r : TiedRun h hr, Socket.doorRides h (TheLetters.first h) (TheLetters.reads h) (TheLetters.shared h open₂) (lastParts h (TheLetters.first h) (TheLetters.last h open₃)) r.R r.x (pursesOf r.c)

/-- **THE ONE OBJECT.** The half that the run's return reads, then the verifier's yes and the third
family: the named holes at the stored files, and five fields. -/
structure TheOneObject extends TheThreadsHalf h hr where
  /-- LETTER. The named holes at the stored files. -/
  files : TheLetters.OpenFiles A
  /-- the yes at every member of the first chain. Laid: `yes₁_filled`, from the closed facts on the
  run on shapes and K12 at member 354. -/
  yes₁ : ∀ r : TiedRun h hr, Socket.yes₁ h (TheLetters.first h) r.R (TheLetters.J₁ h files) (TheLetters.falls₁ h)
  /-- J₁ one member on. Laid: `carry₁_filled`. -/
  carry₁ : ∀ r : TiedRun h hr, Socket.carry₁ h (TheLetters.first h) r.R (TheLetters.J₁ h files) (TheLetters.falls₁ h)
  /-- the yes at every member of the shared chain. Laid: `yes₂_filled`. No fall is allowed here. -/
  yes₂ : ∀ r : TiedRun h hr, Socket.yes₂ h (TheLetters.reads h) (TheLetters.shared h open₂) r.R []
  /-- the yes at every member of the second chain. Laid: `yes₃_whole_filled`. No fall is allowed
  here. -/
  yes₃ : ∀ r : TiedRun h hr, Socket.yes₃ h (TheLetters.first h) (TheLetters.reads h) (TheLetters.shared h open₂) (lastParts h (TheLetters.first h) (TheLetters.last h open₃)) r.R []
  /-- J₁ at the first state. Laid: `HonestTraceRun.Meets.startJ_filled`. -/
  startJ : ∀ r : TiedRun h hr, Socket.startJ h (TheLetters.J₁ h files) r.x

/-! ## 3 What needs no field -/

variable {h hr}

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- The maker returns the online return. -/
theorem onlineMaker_returns
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) :
    onlineMaker Z = .ok (onlineReturn Z A) :=
  atPure_through id (tableCoins Z) matrixInput.dummy made named_in_range

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- **The online prover of honestProvers is the base prover read through.** onlineProver is the third
of the three provers of which honestProvers is made. -/
theorem onlineProver_is_the_base_read_through
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) :
    onlineProver Z = onlineProverAt (onlineReturn Z A) h.places h.firstChain ∧
      (onlineReturn Z A).H = A.H.thru id (tableCoins Z) matrixInput.dummy := by
  have hM := onlineMaker_returns made
  obtain ⟨Bs, base, O⟩ := h.head.laid.opened
  have hp : H2U.placesOfMade (onlineReturn Z A).Z.made = .ok h.places := h.head.laid.places
  have hc : ProofFile.onlineFirstChainAt (onlineReturn Z A).Z = .ok h.firstChain :=
    ToldDesc.pureChainAt_of_open O
  exact ⟨by simp only [onlineProver, hM, hp, hc], rfl⟩

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- **The first thread's falls are the sides' first list.** -/
theorem falls₁_are_the_sides
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) :
    TheLetters.falls₁ h = (theSides h).falls₁ := by
  obtain ⟨Bs, _, O⟩ := h.head.laid.opened
  have hG : Bs.G₀ = A.G :=
    ground_of_head (onlineReturn Z A) h.places h.firstChain
      (onlineMaker_returns made) h.head O.made
  show firstFalls A (TheLetters.numbers h) = theFalls₁ A.Z h.places h.firstChain A.G (FallSlots.nothing _)
  rw [(theFalls_nothing A.Z h.places h.firstChain A.G).1]
  unfold firstFalls
  rw [seatGround_of_base O.made, hG]
  rfl

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- The sides' two other lists are empty. -/
theorem no_later_fall : (theSides h).falls₂ = [] ∧ (theSides h).falls₃ = [] :=
  ⟨(theFalls_nothing A.Z h.places h.firstChain A.G).2.1,
    (theFalls_nothing A.Z h.places h.firstChain A.G).2.2⟩

/-! ## 4 The last line -/

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- Every coin of the three chains is a prover's coin. -/
theorem pursesOf_onto {B : ProverCoinCounts} (k : Coins B) :
    ∃ c : CoinG B RunValue RunValue, pursesOf c = k := by
  cases k with
  | mk a b c => exact ⟨((b, fun _ => 0), ((a, c), fun _ => 0)), rfl⟩

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- At the base prover a request with a trace has its index in range. -/
theorem inRange_of_trace
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) {M : FullSizeMatrix} {x : ProofFile.Inst}
    (ht : (A.H.trace M x).isSome = true) : A.H.inRange M = true := by
  rw [(inRange_of_atPure made).1]
  have e := congrArg (fun A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit => A₀.H.trace M x) (eq_ofFill made)
  dsimp only at e
  rw [e] at ht
  show (VerifiableInference.OnPublicFiles.Flat.indexOf M).isSome = true
  cases hi : VerifiableInference.OnPublicFiles.Flat.indexOf M with
  | some i => rfl
  | none =>
    have z : ((VerifiableInference.OnPublicFiles.Flat.indexOf M).bind fun i =>
        fullIn.trace A.Z i x).isSome = true := ht
    rw [hi] at z
    cases z

/-- **ready returns at the base prover, at every tied input and coin.** -/
theorem TheThreadsHalf.readyReturns
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) (O : TheThreadsHalf h hr)
    (n : ℕ) (w : WZ Z) (x : ProofFile.Inst) (c : CoinG A.B RunValue RunValue)
    (hx : TiedRequest h hr n w x) :
    ∃ R, ProofFile.Honest.ready h.description A.B A.H w.1 (tableCoins Z w.2.1) x (pursesOf c) = .ok R := by
  have e := (atPure_at_laid h.head.laid made).2
  have hR := ready_at_base_of_online (onlineMaker_returns made) made O.readyDebts
    (inRange_of_trace made (O.traceAtTied n w x hx)) (O.traceAtTied n w x hx)
    (tableCoins Z w.2.1) (pursesOf c)
  rw [e] at hR
  exact hR

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- At a run the shared chain's input is the one that the first chain's gives. -/
theorem common_at_run (r : TiedRun h hr) : r.R.common = TheLetters.toCommon (A := A) r.R.own := by
  obtain ⟨-, tr, -, hown, hcom, -, -, -⟩ := ready_ok r.ready
  rw [hcom, hown]

/-- The fields for the run to return, from the first half. -/
theorem TheThreadsHalf.fields
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (O : TheThreadsHalf h hr) (r : TiedRun h hr) :
    ThreadFieldsP h (TheLetters.first h) (TheLetters.reads h) (TheLetters.shared h O.open₂)
      (lastParts h (TheLetters.first h) (TheLetters.last h O.open₃)) r.R r.x (pursesOf r.c) :=
  { fix₁ := ProofFile.Honest.K1.treesFixed_first h.head made,
    endsAtRun := fun k hd => TheLetters.endsAt_at_run h O.open₃ (common_at_run r) k hd,
      fix₂ := O.fix₂,
      fix₃ := O.fix₃ r,
      takenAre := O.takenAre,
      owes₁ := O.owes₁ r,
      owes₂ := O.owes₂ r,
      owes₃ := O.owes₃ r,
      playsAtTrees₃ := O.playsAtTrees₃ r,
      rootedSides := O.rootedSides,
      tied := O.tied r,
      opensTaken := O.opensTaken r,
      startFit := O.startFit r,
      requestParses := O.requestParses r,
      served := O.served r,
      doorTrees := O.doorTrees r,
      doorFive := O.doorFive r,
      doorRides := O.doorRides r }

/-- **The invariants of a run, from the first half alone.** -/
def TheThreadsHalf.threads
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (O : TheThreadsHalf h hr) (r : TiedRun h hr) :
    ThreadsP h.description A.B A.H r.w.1 (tableCoins Z r.w.2.1) r.x (pursesOf r.c) r.R :=
  threadsPAtTheTerm (I := matrixInput) (S := OnBytes.HonestTrace.Sz.ref) (O := openHonest) made
    (theDebtsP (I := matrixInput) (S := OnBytes.HonestTrace.Sz.ref) (O := openHonest) made r.ready
      (shared_riders_late h O.open₂) (O.fields made r)) r.ready

/-- **The rule's structure at the three threads of a run**, from the sockets. -/
theorem TheOneObject.atTheThreads
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (O : TheOneObject h hr) (r : TiedRun h hr) :
    FromThreadsJ h.description A.H (TheLetters.thread₁ h r.R) (TheLetters.thread₂ h r.R (O := O.open₂))
      (TheLetters.thread₃ h O.open₃ r.R) (TheLetters.said₁ h r.R) (TheLetters.said₂ h r.R (O := O.open₂))
      (TheLetters.said₃ h O.open₃ r.R) (TheLetters.J₁ h O.files) (fun _ _ => True) (fun _ _ => True)
      (TheLetters.falls₁ h) [] [] r.w.1 (tableCoins Z r.w.2.1) r.x (pursesOf r.c) r.R :=
  have D : ThreadFields h (TheLetters.first h) (TheLetters.reads h) (TheLetters.shared h O.open₂)
      (lastParts h (TheLetters.first h) (TheLetters.last h O.open₃)) r.R (TheLetters.J₁ h O.files) (TheLetters.falls₁ h) [] [] r.x
      (pursesOf r.c) :=
    { toThreadFieldsP := O.toTheThreadsHalf.fields made r,
      yes₁ := O.yes₁ r,
      carry₁ := O.carry₁ r,
      yes₂ := O.yes₂ r,
      yes₃ := O.yes₃ r,
      startJ := O.startJ r }
  fromThreadsAtTheTerm (I := matrixInput) (S := OnBytes.HonestTrace.Sz.ref) (O := openHonest) made
    (theDebts (I := matrixInput) (S := OnBytes.HonestTrace.Sz.ref) (O := openHonest) made O.files.seat
      O.files.publicData O.files.shapesToEnd O.files.shapesEnd r.ready (shared_riders_late h O.open₂) D) r.ready

/-- **The object's value at a run**: the invariants are the three threads with what is said at each. -/
def TheOneObject.threads
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (O : TheOneObject h hr) (r : TiedRun h hr) :
    ThreadsCJ h.description A.B A.H r.w.1 (tableCoins Z r.w.2.1) r.x (pursesOf r.c) r.R :=
  (O.atTheThreads made r).threadsCJ (head_planOk h.head)

/-- **At every tied input and coin, with the invariants named**: at the base prover ready returns,
the plan serves, and the object's value at that run has the sides' own falls and the three threads'
invariants. -/
theorem atEveryTiedRunAtItsThreads
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (O : TheOneObject h hr) :
    ∀ n w x (c : CoinG (onlineReturn Z A).B RunValue RunValue), TiedRequest h hr n w x →
      ∃ R, ProofFile.Honest.ready (descZ (onlineReturn Z A).Z h.places h.firstChain) (onlineReturn Z A).B
          A.H (id w.1) (tableCoins Z w.2.1) x (pursesOf c) = .ok R ∧
        PlanServes A.H (id w.1) (tableCoins Z w.2.1) R ∧
        ∃ T : ThreadsCJ (descZ (onlineReturn Z A).Z h.places h.firstChain) (onlineReturn Z A).B A.H
            (id w.1) (tableCoins Z w.2.1) x (pursesOf c) R,
          (T.f₁ = (theSides h).falls₁ ∧ T.f₂ = (theSides h).falls₂ ∧
            T.f₃ = (theSides h).falls₃) ∧
          T.I₁ = ThrS (TheLetters.thread₁ h R) (TheLetters.said₁ h R) ∧
          T.I₂ = ThrS (TheLetters.thread₂ h R (O := O.open₂)) (TheLetters.said₂ h R (O := O.open₂)) ∧
          T.I₃ = ThrS (TheLetters.thread₃ h O.open₃ R) (TheLetters.said₃ h O.open₃ R) ∧
          T.J₁ = TheLetters.J₁ h O.files := by
  intro n w x c hx
  obtain ⟨R, hR⟩ := O.toTheThreadsHalf.readyReturns made n w x c hx
  exact ⟨R, hR, O.planServes ⟨n, w, x, c, R, hx, hR⟩, O.threads made ⟨n, w, x, c, R, hx, hR⟩,
    ⟨falls₁_are_the_sides made, no_later_fall.1.symm, no_later_fall.2.symm⟩, rfl, rfl, rfl, rfl⟩

/-- **At every tied input and coin**: at the base prover ready returns, the plan serves, and a value
of ThreadsCJ stands with the sides' own falls. This is BaseThreadsJAt written out. -/
theorem atEveryTiedRun
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (O : TheOneObject h hr) :
    ∀ n w x (c : CoinG (onlineReturn Z A).B RunValue RunValue), TiedRequest h hr n w x →
      ∃ R, ProofFile.Honest.ready (descZ (onlineReturn Z A).Z h.places h.firstChain) (onlineReturn Z A).B
          A.H (id w.1) (tableCoins Z w.2.1) x (pursesOf c) = .ok R ∧
        PlanServes A.H (id w.1) (tableCoins Z w.2.1) R ∧
        ∃ T : ThreadsCJ (descZ (onlineReturn Z A).Z h.places h.firstChain) (onlineReturn Z A).B A.H
            (id w.1) (tableCoins Z w.2.1) x (pursesOf c) R,
          T.f₁ = (theSides h).falls₁ ∧ T.f₂ = (theSides h).falls₂ ∧
            T.f₃ = (theSides h).falls₃ := by
  intro n w x c hx
  obtain ⟨R, hR, hP, T, hf, -⟩ := atEveryTiedRunAtItsThreads made O n w x c hx
  exact ⟨R, hR, hP, T, hf⟩

/-! ## 5 The binder is met, and two facts on the fields -/

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- **Every served request is tied**, at every copy's number, every table's randomness and every
out-of-domain seed: so the fields speak of all of these. -/
theorem every_served_request_is_tied (scope : InScope Z = true) :
    ∀ n i r e x', ServedRequest committerCoinCountLessOne Z hr i x' →
      TiedRequest h hr n (i, r, e) (instanceAsPlainRecord (x', (protocolAtFiles Z).recOf i r e)) := fun n i r e x' hx =>
  validOut Z (onlineReturn Z A).Z h.places h.firstChain runValueBytes runValueBytes
    (onlineReturn Z A).B (theSides h) (onlineReturn Z A).H
    (fun _ _ hs => servedRequest_below committerCoinCountLessOne Z scope hr hs)
    (AtPublicFiles.AtZero.itemsZero_of_data h.head.laid.data) (fun _ _ => ∅) n i r e x' hx
    (Set.notMem_empty e)

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- **In scope there is a tied request**, at every table's randomness and out-of-domain seed. -/
theorem a_tied_request_exists (scope : InScope Z = true) (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) :
    ∃ i x, TiedRequest h hr 0 (i, r, e) x := by
  obtain ⟨i, x', hx⟩ := servedRequest_met committerCoinCountLessOne Z scope hr
  exact ⟨i, _, every_served_request_is_tied scope 0 i r e x' hx⟩

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- **The field readyReturns, from premises that the law on completeness takes beside the object**:
one return of ready at the term's prover, the three equations under which the run crosses, and the
trace. -/
theorem readyReturns_of_one
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (one : ∃ w₀ rc x k R, ProofFile.Honest.ready (descZ (onlineReturn Z A).Z h.places h.firstChain)
      (onlineReturn Z A).B
      (provG Z (onlineReturn Z A).Z h.places h.firstChain (onlineReturn Z A).B (theSides h)
        (A.H.thru id (tableCoins Z) matrixInput.dummy)) w₀ rc x k = .ok R)
    (hd : A.H.inRange (id matrixInput.dummy) = A.H.inRange A.H.dummy)
    (hrows : (theSides h).prover (A.H.thru id (tableCoins Z) matrixInput.dummy) =
      A.H.thru id (tableCoins Z) matrixInput.dummy)
    (hk : (cmAlong (AZ Z) PadZ (holdZ Z)).key = A.H.key)
    (htr : ∀ n w x, TiedRequest h hr n w x → (A.H.trace (id w.1) x).isSome = true) :
    ∀ n w x (c : CoinG A.B RunValue RunValue), TiedRequest h hr n w x →
      ∃ R, ProofFile.Honest.ready h.description A.B A.H w.1 (tableCoins Z w.2.1) x (pursesOf c) =
        .ok R := by
  intro n w x c hx
  obtain ⟨w₀, rc, x₀, k, R', h1⟩ := one
  obtain ⟨R, hR, -⟩ := ready_rows_back id (tableCoins Z) matrixInput.dummy (theSides h)
    (cmAlong (AZ Z) PadZ (holdZ Z)) 0 A.H hrows hk w₀ rc x₀ k hd h1
  exact ready_any hR (inRange_of_trace made (htr n w x hx)) (htr n w x hx) (pursesOf c)

/-- **A tied run exists** at every table's randomness, seed and coin, in scope. -/
theorem a_tied_run_exists (scope : InScope Z = true)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (O : TheThreadsHalf h hr) (r : (protocolAtFiles Z).EncodingRandomness)
    (e : (protocolAtFiles Z).OutOfDomainSeed) (c : CoinG A.B RunValue RunValue) : Nonempty (TiedRun h hr) := by
  obtain ⟨i, x, hx⟩ := a_tied_request_exists (h := h) (hr := hr) scope r e
  obtain ⟨R, hR⟩ := O.readyReturns made 0 (i, r, e) x c hx
  exact ⟨⟨0, (i, r, e), x, c, R, hx, hR⟩⟩

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- **The guard of the item totalB**: where the member behind a segment's batching says yes, the
falls at that member say nothing. -/
theorem totalB_guard : ∀ l, l < 25 → ∀ blk, h.firstChain.blocksInOrder[14 * l + IM.nAt l + 3]? = some blk →
    ∀ s rs cols s' n, blk.step 0 s rs cols = .ok (s', n) →
      fallsAfterBatching (firstFalls A (TheLetters.numbers h)) h.firstChain l s = none :=
  ProofFile.Honest.K9.step_silent_first h (TheLetters.numbers h)

end AtFullSide.Honest

#print axioms AtFullSide.Honest.onlineProver_is_the_base_read_through
#print axioms AtFullSide.Honest.falls₁_are_the_sides
#print axioms AtFullSide.Honest.pursesOf_onto
#print axioms AtFullSide.Honest.TheOneObject.atTheThreads
#print axioms AtFullSide.Honest.TheOneObject.threads
#print axioms AtFullSide.Honest.atEveryTiedRunAtItsThreads
#print axioms AtFullSide.Honest.every_served_request_is_tied
#print axioms AtFullSide.Honest.readyReturns_of_one
#print axioms AtFullSide.Honest.atEveryTiedRun
#print axioms AtFullSide.Honest.a_tied_run_exists
#print axioms AtFullSide.Honest.totalB_guard
