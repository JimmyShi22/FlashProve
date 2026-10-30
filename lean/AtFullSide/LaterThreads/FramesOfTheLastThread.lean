-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/LaterThreads/FramesOfTheLastThread.lean: CONDITIONAL: on the head at a return of the maker
and on TWO NAMED PREMISES, NOT PAID HERE: runReturns and door; on sizes: the run's own instance's
key has the plan's sizes; and on tied, which the threads' writers' own letter meets. THE FULL SIZE
ALONE.

NO THEOREM OF THIS LIBRARY THAT NAMES THE LAST CHAIN's THREAD SHOWS A STAND OF IT AT ANY BORDER
BEYOND 0 BUT FROM A PREMISE THAT HOLDS ONE. Had: the door (`doorAtTheTerm`,
AtFullSide/Honest/ThreadsAtTheTerm.lean): a stand at border 0 behind stands of the two earlier
threads at their ends and the start's yes, where both ends hold opened columns, under
`ThreadFieldsP` and ready's return; and the general rule `thread_in_second`
(Johnson/Desc/ProofFile/Honest/Law/InsideFile.lean): for three invariants that its premises have
carried by every member, at the two starts and through the door, at a run of runC that returns,
where ready returns, the plan is fit and served, the draws are due and no silent stop fires, a
called part of the second chain is reached from a state at which the third invariant holds. No
statement joins them into one that ends in a stand of this thread. Each statement here is an
implication from the thread's stand in front of a member. It says nothing of any run.

What is here. THE YES OF THE FRAME's TWO MEMBERS OF THE LAST CHAIN: "the taken trees' sources"
(number 1) and the chain's end (number 3), at the library's own thread of that chain (lastThread,
Honest/Thread/TheFirstThread.lean), at every value of its letters, BY THE RUN ON SHAPES
(Honest/Thread/Shape.lean) at the library's shape of a third chain (Z₃, E2E/KeyShapeChain.lean), laid
at the proof file's own four members.

  lastShape                      the shape, the guards and the tests on values at the four members
  last_members, last_length      the proof file's last chain's flat list, written out
  carries_at_the_last_chain      (B1) at every number of that list, under the head
  returns_at_the_taken_sources, returns_at_the_last_end   (B2) at 1 and 3: no test on values
  KeyHasTheSizes, DoorHasTheShape   the premises sizes and door: definitions
  shape_at_the_last_thread       at a stand at a border the state has the shape that the run gives
  tied_at_the_taken_sources      **at a stand in front of 1 the taken trees' sources are tied**: the
                                 premise of acceptedS_takenSources (Honest/Thread/FrameMembers.lean)
                                 to the letter
  accepted_at_the_taken_sources  **AcceptedS at 1**
  accepted_at_the_last_end       **AcceptedS at 3**

THE PREMISES.
  runReturns : (lastShape A.Z h.places).yes a₀ 4 = true: the guards' run over the four members
    returns from the shape a₀: a closed test on a₀. EVALUATED AT NO a₀ IN THIS FILE. Through
    `runReturns_of_closed` (LastRunClosed.lean) it is the closed Bool that the side library ShapeLines
    evaluates in Lean's kernel at its written value (`last_run_at_border358`,
    ShapeLines/LastChain/LastRunAtBorder358.lean), which this file does not import.
  door : DoorHasTheShape h a₀: at an instance that passes okStart and whose key has the plan's sizes
    (KeyHasTheSizes: okStart tests the key's words, not its sizes, and the shared chain's first
    shape hangs on the sizes), whatever start₃ returns of two states that the verifier's folds over the first and the shared chain return has the shape a₀. IT
    NAMES NO THREAD, NO PROVER AND NO COIN: a sentence on the description. It says which trees'
    numbers stand in the first chain's book at its end, and which groups have begun their tests.
    SHOWN AT NO a₀ IN THIS FILE. That one a₀ serves every such instance is `door_of_the_two_ends`
    (DoorOnShapes.lean) at `shared_end_at_the_head` and `first_end_shape_of_run`, given the whole run on
    shapes and one closed line at its end: if that run refused at one member, that law would be empty.
  sizes : KeyHasTheSizes h w.x: at the run's own instance. Not shown here of any run. Where the key is
    one that the committer makes of the run's index and coins (validAt), a clause of the library's
    fiveFields_at (Johnson/Bind/ForProver/FiveAt.lean) gives keyFits at the plan's index, under that
    law's two premises on the shape: by reading; not called here.
  tied : what is said of the run gives SaidField at BaseTied. The threads' writers' saidThree
    (AtFullSide/Honest/TheThreeThreads.lean) is that very letter: there tied is "fun _ _ _ a => a".
    The library's rule accepted_quiet_shape (E2E/ShapeQuiet.lean) asks the first state's shape at
    EVERY coins, input and challenges at which the thread lets the chain begin; at a letter ends that
    is made by choice (endsBy) that reaches states of which nothing is known. So the rule is not
    called: its steps are taken at a stand, where BaseTied says where the chain began.
WHY A PREMISE ON THE FIRST STATE CANNOT BE SPARED. Member 1 accepts just where Third.Law.Tied holds
(takenSources_exact), and that reads the numbers of four trees in the state's book, three of them the
first chain's. The thread's form (shapeAt, Johnson/Desc/Last/ShapeAt.lean) pins the state relative to
what was handed and says nothing of the handed book's numbers. By reading: no counter-example is
shown.

By what. Calls: second_carries (E2E/KeyShapeSecond.lean), sources_carries, sources_returns,
end_carries, end_returns (E2E/KeyShapeThird.lean), own_carries (E2E/KeyShapeOwn.lean), each at free
letters; carries_seat, returns_seat (Honest/Thread/ShapeJoin.lean); shape_reach, run_front
(Honest/Thread/Shape.lean); opened_of_saidField (Honest/Thread/SaidField.lean); acceptedS_quiet
(Honest/Law/NoHouse/Quiet.lean); acceptedS_takenSources, step_quiet (Honest/Thread/FrameMembers.lean);
last_blocks_in (Johnson/ToldDescR/LastBlocks.lean); reads_head_W
(Honest/K12/Sim/FirstAnyAtHeadW.lean).

Not shown here. The premises. PlaysS, BehindS, ExchangeS, RidesPastS at these members. (B2) at
the members 0 and 2. Nothing on soundness, on completeness, on hiding or on any other property.
No property is claimed.
-/
import E2E.KeyShapeOwn
import Johnson.ToldDescR.LastBlocks
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstAnyAtHeadW
import Johnson.Desc.ProofFile.Honest.Thread.FrameMembers
import Johnson.Desc.ProofFile.Honest.Thread.BaseTied
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.LaterThreads
open ProofFile.Honest
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders LastThreadParts lastThread)
open AtPublicFiles.AtFiles (Z₃ Sh₃ sh₃ gOwn)
open VerifiableInference.Desc (Block Chain noDigest)
open VerifiableInference.Desc.Third (S₃ batchLinearConstraintsSecondPart takenSources end₃)
open VerifiableInference.Desc.K12 (P12)
open ToldDesc (p14At ownAt)

/-- The place's numbers of the request's own proximity test. -/
abbrev ownPlace (places : H2U.Places4) : P12 := H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ places.W

/-- **The shape, the guards and the tests on values at the last chain's four members.** At the own
test no test on values is named: (B2) is not asked there. -/
def lastShape (publicPart : ProofFile.Pub) (places : H2U.Places4) : Shape S₃ :=
  Z₃ (p14At publicPart).S (ownAt places).rounds (gOwn (ownPlace places)) fun _ _ _ => true

section List
variable (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl) (ft : Nat)

/-- **The proof file's last chain's flat list.** -/
theorem last_members :
    (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder =
      [batchLinearConstraintsSecondPart (p14At Zp), takenSources (ownAt Np), ownAt Np,
        end₃ [batchLinearConstraintsSecondPart (p14At Zp), takenSources (ownAt Np), ownAt Np]].map Block.retype :=
  ToldDesc.last_blocks_in OnBytes.secondHashFunction ProofFile.pureRoad.links Zp (Desc.K14.Law.seatN Zp Np) Np cF

theorem last_length : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.length = 4 := by
  rw [last_members]
  rfl

/-- CONDITIONAL on early and answers. **(B1) at every number of the last chain's flat list.** -/
theorem carries_of_the_place (early : (ownPlace Np).early = true)
    (answers : (ownPlace Np).answers = 1) (j : Nat) :
    Carries (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder ft (lastShape Zp Np) j := by
  rw [last_members]
  match j with
  | 0 =>
    exact carries_seat (blk := (batchLinearConstraintsSecondPart (p14At Zp) : Block S₃ Unit).retype) rfl fun rs cols _ =>
      AtPublicFiles.AtFiles.second_carries (Cl := Unit) (p14At Zp) (rs.map noDigest)
        (((batchLinearConstraintsSecondPart (p14At Zp) : Block S₃ Unit).retype (Cl' := ProofFile.Cl)).shown ft rs cols)
  | 1 =>
    exact carries_seat (blk := (takenSources (ownAt Np)).retype) rfl fun rs cols _ =>
      AtPublicFiles.AtFiles.sources_carries (p14At Zp).S (ownAt Np) (rs.map noDigest)
        (((takenSources (ownAt Np)).retype (Cl' := ProofFile.Cl)).shown ft rs cols)
  | 2 =>
    exact carries_seat (blk := (ownAt Np).retype) rfl fun rs cols _ =>
      AtPublicFiles.AtFiles.own_carries (p14At Zp).S (ownPlace Np) early answers (rs.map noDigest)
        (((ownAt Np).retype (Cl' := ProofFile.Cl)).shown ft rs cols)
  | 3 =>
    exact carries_seat
      (blk := (end₃ [batchLinearConstraintsSecondPart (p14At Zp), takenSources (ownAt Np), ownAt Np]).retype) rfl
      fun rs cols _ => AtPublicFiles.AtFiles.end_carries (Cl := Unit) (p14At Zp).S
        [batchLinearConstraintsSecondPart (p14At Zp), takenSources (ownAt Np), ownAt Np] (rs.map noDigest)
        (((end₃ [batchLinearConstraintsSecondPart (p14At Zp), takenSources (ownAt Np), ownAt Np]).retype
          (Cl' := ProofFile.Cl)).shown ft rs cols)
  | n + 4 =>
    intro blk hb
    cases hb

/-- **(B2) at "the taken trees' sources".** -/
theorem returns_at_the_taken_sources :
    Returns (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder ft (lastShape Zp Np) 1 := by
  rw [last_members]
  exact returns_seat (blk := (takenSources (ownAt Np)).retype) rfl fun rs cols _ =>
    AtPublicFiles.AtFiles.sources_returns (p14At Zp).S (ownAt Np) (rs.map noDigest)
      (((takenSources (ownAt Np)).retype (Cl' := ProofFile.Cl)).shown ft rs cols)

/-- **(B2) at the chain's end.** -/
theorem returns_at_the_last_end :
    Returns (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder ft (lastShape Zp Np) 3 := by
  rw [last_members]
  exact returns_seat
    (blk := (end₃ [batchLinearConstraintsSecondPart (p14At Zp), takenSources (ownAt Np), ownAt Np]).retype) rfl
    fun rs cols _ => AtPublicFiles.AtFiles.end_returns (Cl := Unit) (p14At Zp).S
      [batchLinearConstraintsSecondPart (p14At Zp), takenSources (ownAt Np), ownAt Np] (rs.map noDigest)
      (((end₃ [batchLinearConstraintsSecondPart (p14At Zp), takenSources (ownAt Np), ownAt Np]).retype
        (Cl' := ProofFile.Cl)).shown ft rs cols)

end List

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- CONDITIONAL on h. **(B1) at every number of the last chain's flat list, under the head.** -/
theorem carries_at_the_last_chain (h : HeadAtReturn files A) (ft j : Nat) :
    Carries h.description.second.blocksInOrder ft (lastShape A.Z h.places) j :=
  carries_of_the_place A.Z h.places h.firstChain ft
    (H2K.JointK.early_of_planOk _ (K12.Light.reads_head_W h.head.toAtMg).2.2.2)
    (H2K.JointK.answers_of_planOk _ (K12.Light.reads_head_W h.head.toAtMg).2.2.2) j

/-- **The instance's key has the sizes of the plan's index**: so many words in the record, so many
seeds, each of so many coordinates (keyFits, Johnson/Desc/Own/KeyTests.lean). The description's test
okStart does not ask it: it tests the key's words and its item. -/
def KeyHasTheSizes (h : HeadAtReturn files A) (x : ProofFile.Inst) : Prop :=
  VerifiableInference.Desc.Own.keyFits x.pub.key
    (VerifiableInference.Desc.K1.qAt A.Z h.places).par.S.fold.index = true

/-- **THE DOOR ON SHAPES**: at an instance that passes the description's test okStart and whose key has
the plan's sizes, whatever the
description's start of the last chain returns of two states that the verifier's own folds over the
first and the shared chain return, from the description's own starts, has the shape a₀. A sentence on the verifier's description alone: no thread, no prover, no
coin. A definition, meant as a hypothesis. -/
def DoorHasTheShape (h : HeadAtReturn files A) (a₀ : Sh₃) : Prop :=
  ∀ (x : ProofFile.Inst) (r₁ r₂ : List Fmt.RoundView) (c₁ c₂ : List VerifiableInference.Desc.OpenedColumn)
    (e₁ : h.description.S₁) (e₂ : h.description.S₂) (s₀ : h.description.S₃),
    h.description.okStart x = true → KeyHasTheSizes h x →
    VerifiableInference.Desc.foldBlocks 0 h.description.first.blocksInOrder
      (h.description.start₁ (h.description.pub x)) r₁ c₁ = .ok (e₁, [], []) →
    VerifiableInference.Desc.foldBlocks 0 h.description.shared.blocksInOrder
      (h.description.start₂ (h.description.pub x)) r₂ c₂ = .ok (e₂, [], []) →
    h.description.start₃ (h.description.pub x) e₁ e₂ = .ok s₀ →
    sh₃ (p14At A.Z).S s₀ = a₀

variable (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
  (parts : LastThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
  (fall : Nat → S₃ → List Fmt.Drawn → Option String) {a₀ : Sh₃}

/-- CONDITIONAL on h, runReturns, door, sizes and tied. **AT A STAND OF THE LAST CHAIN's THREAD THE STATE HAS THE
SHAPE THAT THE GUARDS' RUN GIVES.** tied: what is said of the run gives the field letter at BaseTied
(Honest/Thread/BaseTied.lean): so the chain began at what start₃ returns of two folds' returns. -/
theorem shape_at_the_last_thread
    (runReturns : (lastShape A.Z h.places).yes a₀ 4 = true) (door : DoorHasTheShape h a₀)
    (sizes : KeyHasTheSizes h w.x)
    (tied : ∀ b k m, Said b k m → SaidField (lastThread h first reads parts w)
      (BaseTied h.description (lastThread h first reads parts w)) b k m)
    {b : Nat} (hb : b ≤ 4) {k : Coins A.B} {s : S₃} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (stand : ThrS (lastThread h first reads parts w) Said b k s m E) :
    (lastShape A.Z h.places).run b a₀ = .ok ((lastShape A.Z h.places).sh s) := by
  obtain ⟨_, _, ⟨r₁, r₂, _, c₁, c₂, e₁, e₂, -, -, -, -, -, -, fold₁, fold₂, -, begins⟩, -, -⟩ :=
    opened_of_saidField _ stand.1 (tied b k m stand.2)
  have thr := stand.1
  unfold Thr Thread.Made at thr
  obtain ⟨-, -, -, -, ⟨-, -, -, -, s₀, c₀, began, -, fold₃⟩, -, valid⟩ := thr
  have first₀ : (lastShape A.Z h.places).sh s₀ = a₀ :=
    door m.st.input.x r₁ r₂ c₁ c₂ e₁ e₂ s₀ valid.2.1 (valid.1 ▸ sizes) fold₁ fold₂
      (begins s₀ began)
  have reached : Johnson.Desc.First.Walk.Tied.Reach (lastThread h first reads parts w).ft
      (lastThread h first reads parts w).bs (fun _ : Unit => s₀) b ((), s) :=
    Johnson.Desc.First.Walk.Tied.reach_of_fold b
      (Nat.le_trans hb (Nat.le_of_eq (last_length A.Z h.places h.firstChain).symm)) s _ _ _ _ fold₃
  obtain ⟨e, runs⟩ := run_front (lastShape A.Z h.places) a₀ 4 b hb runReturns
  have is := shape_reach (lastShape A.Z h.places) (carries_at_the_last_chain h _) reached e
    (by rw [first₀]; exact runs)
  rw [runs, is]

/-- What the guards' run gives one member on. -/
theorem guard_returns_at_the_last_thread
    (runReturns : (lastShape A.Z h.places).yes a₀ 4 = true) (door : DoorHasTheShape h a₀)
    (sizes : KeyHasTheSizes h w.x)
    (tied : ∀ b k m, Said b k m → SaidField (lastThread h first reads parts w)
      (BaseTied h.description (lastThread h first reads parts w)) b k m)
    {b : Nat} (hb : b < 4) {k : Coins A.B} {s : S₃} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (stand : ThrS (lastThread h first reads parts w) Said b k s m E) :
    ∃ behind, (lastShape A.Z h.places).g b ((lastShape A.Z h.places).sh s) = .ok behind := by
  have here := shape_at_the_last_thread h first reads parts w Said runReturns door sizes tied
    (Nat.le_of_lt hb) stand
  obtain ⟨behind, next⟩ := run_front (lastShape A.Z h.places) a₀ 4 (b + 1) hb runReturns
  have step : ((lastShape A.Z h.places).run b a₀).bind ((lastShape A.Z h.places).g b) =
      .ok behind := next
  rw [here] at step
  exact ⟨behind, step⟩

/-- CONDITIONAL on h, runReturns, door, sizes and tied. **AT A STAND IN FRONT OF "THE TAKEN TREES' SOURCES" THE
SOURCES ARE TIED**: the premise of acceptedS_takenSources (Honest/Thread/FrameMembers.lean) to the
letter. -/
theorem tied_at_the_taken_sources
    (runReturns : (lastShape A.Z h.places).yes a₀ 4 = true) (door : DoorHasTheShape h a₀)
    (sizes : KeyHasTheSizes h w.x)
    (tied : ∀ b k m, Said b k m → SaidField (lastThread h first reads parts w)
      (BaseTied h.description (lastThread h first reads parts w)) b k m) :
    ∀ k s m E, ThrS (lastThread h first reads parts w) Said 1 k s m E →
      VerifiableInference.Desc.Third.Law.Tied (ownZ h.places) s := by
  intro k s m E stand
  obtain ⟨behind, guard⟩ := guard_returns_at_the_last_thread h first reads parts w Said runReturns
    door sizes tied (b := 1) (by omega) stand
  obtain ⟨s', yes⟩ := AtPublicFiles.AtFiles.sources_returns (p14At A.Z).S (ownAt h.places) [] [] s behind
    guard rfl
  exact ((VerifiableInference.Desc.Third.Law.takenSources_exact (ownAt h.places) s [] [] s').1
    yes).2

/-- CONDITIONAL on h, runReturns, door, sizes and tied. **"THE TAKEN TREES' SOURCES" SAYS YES AT
EVERY STAND IN FRONT OF IT.** An implication from the thread's stand; no theorem of this library
that names this thread shows a stand of it at any border beyond 0 but from a premise that holds one.
-/
theorem accepted_at_the_taken_sources
    (runReturns : (lastShape A.Z h.places).yes a₀ 4 = true) (door : DoorHasTheShape h a₀)
    (sizes : KeyHasTheSizes h w.x)
    (tied : ∀ b k m, Said b k m → SaidField (lastThread h first reads parts w)
      (BaseTied h.description (lastThread h first reads parts w)) b k m) :
    AcceptedS (lastThread h first reads parts w) Said fall 1 :=
  acceptedS_takenSources (Zp := A.Z) (Np := h.places) (cF := h.firstChain)
    (lastThread h first reads parts w) Said rfl
    (tied_at_the_taken_sources h first reads parts w Said runReturns door sizes tied)

/-- CONDITIONAL on h, runReturns, door, sizes and tied. **THE LAST CHAIN's END SAYS YES AT EVERY
STAND IN FRONT OF IT.** An implication from the thread's stand; no theorem of this library that
names this thread shows a stand of it at any border beyond 0 but from a premise that holds one. -/
theorem accepted_at_the_last_end
    (runReturns : (lastShape A.Z h.places).yes a₀ 4 = true) (door : DoorHasTheShape h a₀)
    (sizes : KeyHasTheSizes h w.x)
    (tied : ∀ b k m, Said b k m → SaidField (lastThread h first reads parts w)
      (BaseTied h.description (lastThread h first reads parts w)) b k m) :
    AcceptedS (lastThread h first reads parts w) Said fall 3 := by
  have member : (lastThread h first reads parts w).bs[3]? = some
      ((end₃ [batchLinearConstraintsSecondPart (p14At A.Z), takenSources (ownAt h.places), ownAt h.places]).retype) := by
    show h.description.second.blocksInOrder[3]? = _
    rw [last_members]
    rfl
  refine acceptedS_quiet _ Said member rfl fun k s m E stand _ => ?_
  obtain ⟨behind, guard⟩ := guard_returns_at_the_last_thread h first reads parts w Said runReturns
    door sizes tied (b := 3) (by omega) stand
  obtain ⟨s', yes⟩ := AtPublicFiles.AtFiles.end_returns (Cl := Unit) (p14At A.Z).S
    [batchLinearConstraintsSecondPart (p14At A.Z), takenSources (ownAt h.places), ownAt h.places] [] [] s behind guard rfl
  exact ⟨s', step_quiet rfl yes⟩

end AtFullSide.LaterThreads

#print axioms AtFullSide.LaterThreads.carries_at_the_last_chain
#print axioms AtFullSide.LaterThreads.returns_at_the_taken_sources
#print axioms AtFullSide.LaterThreads.returns_at_the_last_end
#print axioms AtFullSide.LaterThreads.shape_at_the_last_thread
#print axioms AtFullSide.LaterThreads.accepted_at_the_taken_sources
#print axioms AtFullSide.LaterThreads.accepted_at_the_last_end
#print axioms AtFullSide.LaterThreads.tied_at_the_taken_sources
