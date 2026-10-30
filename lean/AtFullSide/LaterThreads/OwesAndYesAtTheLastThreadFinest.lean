-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/LaterThreads/OwesAndYesAtTheLastThreadFinest.lean: CONDITIONAL. THE FULL SIZE ALONE.

THE YES AT MEMBERS 0 AND 1 IS TAKEN OUT OF THE INVARIANT IN FRONT, NOT SHOWN OF THE RUN: the stand at
border 0 holds `doorRider`'s eleven tests and the test `tiedAheadB` at the start's record, the stand at
border 1 holds what `tiedRider` says, and the yes is read off these. So THIS YES IS HALF A SENTENCE
WITHOUT THE ONE OBJECT's THREE FIELDS `doorRides`, `doorFive` AND `doorTrees`, which speak of what the door
lays into that stand. Nothing here says that the last chain accepts.

What is here. `OwesS` AND `YesS` AT THE SECOND CHAIN's THREAD, GENERAL IN THE INPUT, THE COMPANION SENTENCE
AND THE LETTERS NAMED (five debts fix L.riders, L.keeps, L.taken, L.table and L.fixed): at `lastThread h first reads (lastParts h first L) w` and at any Said that
gives the field letter at `BaseTied`: EVERY MEMBER BY A CALL. Whoever names a value of the letters,
an input and a companion sentence has one instance of it; so it does not turn when these names turn;
no file beneath it names the three threads at a run.

  `nothing_rides_from_border_two_on` at the two tied riders and no other. `LastThreadDebtsFinest`
  WHAT IS STILL OWED BY OTHERS: one field a debt.

  `owes_and_yes_at_the_last_thread_finest`   **the two.**

WHO PAYS WHICH MEMBER. 0: `five_at_lastParts_tied` · 1: `five_at_last_one_late`, the rider's road, which is the road
that the sockets' law takes to the yes at 1 · 2:
`five_at_the_proximity_test_rest` (AtFullSide/LaterThreads/ProximityRestAtTheLastThread.lean) · 3:
`five_at_the_last_end` (AtFullSide/LaterThreads/LastThreadAtTheValues.lean), its yes by
`last_end_accepts_of_the_run` (AtFullSide/LaterThreads/FramesOfTheLastThreadOfTheRun.lean).

Not shown here. EVERY FIELD OF `LastThreadDebtsFinest` IS A HYPOTHESIS HERE; at the Letters' values
what is left of them is `LastChainDebtsAtTheNames`, met together at every tied run by
`lastDebts_at_a_tied_run` (AtFullSide/Honest/LastSocketsOfTheClosedFacts.lean, with that file's limit on the
coins), given wholeRun and line. standRest HOLDS THREE CLAUSES ON A STAND IN FRONT OF THE LAST PROXIMITY TEST:
paid at the letters by `standRest_at_letters` (AtFullSide/K12/Part4/StandRestAtTheLetters.lean). wholeRun AND
line ARE TWO CLOSED FACTS THAT STAND IN NO LIBRARY THAT THIS FILE IMPORTS. THE RIDER AT BORDER 0 MOVES A DEBT TO
THE DOOR. NO THEOREM OF THIS LIBRARY THAT NAMES THIS THREAD SHOWS A STAND OF IT AT ANY BORDER BEYOND
0 BUT FROM A PREMISE THAT HOLDS ONE. Had: the door (`doorAtTheTerm`,
AtFullSide/Honest/ThreadsAtTheTerm.lean): a stand at border 0 behind stands of the two earlier
threads at their ends and the start's yes, where both ends hold opened columns, under
`ThreadFieldsP` and ready's return; and the general rule `thread_in_second`
(Johnson/Desc/ProofFile/Honest/Law/InsideFile.lean): for three invariants that its premises have
carried by every member, at the two starts and through the door, at a run of runC that returns,
where ready returns, the plan is fit and served, the draws are due and no silent stop fires, a
called part of the second chain is reached from a state at which the third invariant holds. No
statement joins them into one that ends in a stand of this thread. Each of the five is an
implication from the thread's stand in front of the member. AT THE BASE MAKER's TYPES (`IndexCommitterCoins`).
Nothing on hiding. Nothing on soundness, on
completeness or on any other property.

No property is claimed.
-/
import AtFullSide.LaterThreads.LastThreadAtTheValues
import AtFullSide.LaterThreads.ProximityRestAtTheLastThread
import AtFullSide.LaterThreads.FramesOfTheLastThreadOfTheRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.LaterThreads
open ProofFile ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.K12 (seedRound)
open ProofFile.Honest.K12.AtFile (StandRest WidthsAt takenLast lastTable lastFixed ownLast)
open ProofFile.Honest.K12.Light (ManyJob)
open AtFullSide.K12 (jobAtFill)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Third (S₃)
open ToldDesc (ownAt)
open Johnson.AtFull.Shape (ShA RunsAll startShA)

variable {W₀ W₂ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **At the two tied riders and the door's, nothing rides at a border from 2 on.** -/
theorem nothing_rides_from_border_two_on (h : HeadAtReturn files A) (first : FirstThreadParts A)
    {L : LastLetters A} (riders : L.riders = lastRiders h.places []) {b : Nat} (hb : 2 ≤ b)
    (v : Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (s : S₃) : (lastParts h first L).rides b v s := by
  show ridersOf (ProofFile.Honest.K14.doorRider _ (ToldDesc.p14At A.Z) :: L.riders) b v s
  rw [riders]
  intro c hc _ hhi
  simp only [lastRiders, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact absurd hhi (by show ¬ b ≤ 0; omega)
  · exact absurd hhi (by show ¬ b ≤ 0; omega)
  · exact absurd hhi (by show ¬ b ≤ 1; omega)

/-- **WHAT `OwesS` AND `YesS` AT THE SECOND CHAIN's THREAD STILL TAKE FROM OTHERS.** A definition,
meant as a hypothesis: one field a debt. job: the filling's job of the last proximity test. own:
what a step keeps beside "the state stays at the frame's two". firstEnd: the shape that the run on
shapes gives at the first chain's end. The seven letters behind it: those of the proximity test's
writers' value of the tables and the counts. -/
structure LastThreadDebtsFinest (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ IndexCommitterCoins) (L : LastLetters A) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (Said : ℕ → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (job : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit) (own : Place → S₃ → S₃ → Prop)
    (firstEnd : ShA) (r₁ n₀ : ℕ) (toCommon : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → W₂)
    (tb₁ : Fmt.TreeSource → Coins A.B → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → List Fmt.Drawn →
      Place × Table)
    (tb₂ : Fmt.TreeSource → Coins A.B → W₂ → List Fmt.Drawn → Place × Table)
    (fx₁ fx₂ : Fmt.TreeSource → ℕ) : Prop where
  /-- the letters' riders are the two tied ones and no other: by
  unfolding at `lastRiders h.places []` -/
  ridersAreTheTiedOnes : L.riders = lastRiders h.places []
  /-- the letters' keeps is `lastKeeps`: by unfolding at their value
  -/
  keepsAreTheLastKeeps : L.keeps = lastKeeps own
  /-- the trees taken over are the written ones: by unfolding
  at `lastLettersOf` (Honest/K12/AtFile/WLaidDefs.lean) -/
  takenAreTheWritten : L.taken = takenLast
  /-- the trees' tables are the two earlier chains' and the job's own: likewise -/
  tablesAreLaid : L.table = lastTable r₁ toCommon tb₁ tb₂ (ownLast job.toRun.toTest () n₀)
  /-- the numbers at which the trees are fixed: likewise -/
  fixedAreLaid : L.fixed =
    lastFixed r₁ fx₁ fx₂ fun τ => n₀ + seedRound job.toRun.toTest.p.nums.stages τ
  /-- n₀ counts the rounds in front of the chain -/
  roundsInFront : n₀ = (lastThreadAt h first reads L w).front
  /-- the widths of the three trees taken over, at the two earlier chains' tables
  -/
  widths : WidthsAt r₁ toCommon tb₁ tb₂
  /-- what a stand in front of the last proximity test still owes: three clauses: the field and the
  ends, the trees taken over, what the test's rows say -/
  standRest : StandRest (Zp := A.Z) (Np := h.places) (cF := h.firstChain)
    (lastThreadAt h first reads L w) Said job
  /-- the own clause allows the state as it stands at the taken trees' sources: whoever lays
  it shows this; at "True" it holds for nothing -/
  ownAllowsTheSources : ∀ s, own ⟨3, none, 1, .frame⟩ s s
  /-- the same at the chain's end -/
  ownAllowsTheEnd : ∀ s, own ⟨3, none, 3, .frame⟩ s s
  /-- behind the last proximity test's accepting step the own clause holds at its place
  -/
  ownHoldsBehindTheTest : ∀ k s m E ds y cols s',
    ThrS (lastThreadAt h first reads L w) Said 2 k s m E →
    drawsFit ((ownAt h.places).retype : Block S₃ ProofFile.Cl).rounds ds = true →
    (lastThreadAt h first reads L w).Stepped ((ownAt h.places).retype : Block S₃ ProofFile.Cl) k s m E ds
      y cols s' →
    own ⟨3, none, 2, .K12⟩ s s'
  /-- the run on shapes over the first chain's 358 members returns firstEnd: a closed fact
  -/
  wholeRun : RunsAll 0 358 startShA firstEnd
  /-- the guards' run over the last chain's four members returns from the door's shape at firstEnd:
  one closed Bool: `lastRunAt_border358` (ShapeLines/LastChain/SocketsThreeAt358.lean), at the shape `border358` -/
  line : lastRunAt firstEnd = true
  /-- the key of the input's instance has the plan's sizes: whoever states the relation on
  the run's instance shows it; at a run it follows from three facts on the run
  (AtFullSide/LaterThreads/OwesAndYesThreeAtTheLetters.lean) -/
  keyHasTheSizes : KeyHasTheSizes h w.x
  /-- the companion sentence gives the field letter at the columns of the two earlier chains.
  Whoever names the sentence shows this, by a projection -/
  saidGivesTheField : ∀ n k m, Said n k m → SaidField (lastThreadAt h first reads L w)
    (BaseTied h.description (lastThreadAt h first reads L w)) n k m

/-- CONDITIONAL: on h, hA and the debts. **`OwesS` AND `YesS` AT THE SECOND CHAIN's THREAD, AT ANY
LETTERS, INPUT AND COMPANION SENTENCE THAT MEET THE DEBTS.** The last four binders are a thread of
the shared chain of which nothing is read. Implications from the thread's stand in front of each
member; no theorem of this library that names this thread shows a stand of it at any border beyond 0
but from a premise that holds one. -/
theorem owes_and_yes_at_the_last_thread_finest (h : HeadAtReturn files A) (I : WiderIn W₀)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    ∃ job, jobAtFill A.Z h.places h.firstChain I S O A.G = some job ∧
      ∀ (first : FirstThreadParts A) (reads : IndexReaders W₀ IndexCommitterCoins) (L : LastLetters A)
        (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
        (Said : ℕ → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
        (own : Place → S₃ → S₃ → Prop) (firstEnd : ShA) (r₁ n₀ : ℕ)
        (toCommon : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → W₂)
        (tb₁ : Fmt.TreeSource → Coins A.B → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → List Fmt.Drawn →
          Place × Table)
        (tb₂ : Fmt.TreeSource → Coins A.B → W₂ → List Fmt.Drawn → Place × Table)
        (fx₁ fx₂ : Fmt.TreeSource → ℕ) (fall : ℕ → S₃ → List Fmt.Drawn → Option String)
        (sharedReads : IndexReaders W₀ IndexCommitterCoins) (Wt : Type) (sharedParts : SharedThreadParts A Wt)
        (sharedInput : Common W₀ IndexCommitterCoins OnBytes.TableKey),
        LastThreadDebtsFinest h first reads L w Said job own firstEnd r₁ n₀ toCommon tb₁ tb₂ fx₁
          fx₂ →
        OwesS (lastThreadAt h first reads L w) Said ∧
          YesS (lastThreadAt h first reads L w) Said fall := by
  obtain ⟨job, isTheJob, atTheTest⟩ := five_at_the_proximity_test_rest (W₂ := W₂) h I S O hA
  refine ⟨job, isTheJob, fun first reads L w Said own firstEnd r₁ n₀ toCommon tb₁ tb₂ fx₁ fx₂ fall
    sharedReads Wt sharedParts sharedInput D => ?_⟩
  exact owes_and_yes_at_the_last_thread_at_the_values (later := []) (own := own)
    { ridersAreTheLastRiders := D.ridersAreTheTiedOnes
      laterRidersBeginLate := fun _ hc => absurd hc List.not_mem_nil
      keepsAreTheLastKeeps := D.keepsAreTheLastKeeps
      ownAllowsTheSources := D.ownAllowsTheSources
      ownAllowsTheEnd := D.ownAllowsTheEnd
      ridersBehindTheEnd := fun _ s m _ _ =>
        nothing_rides_from_border_two_on h first D.ridersAreTheTiedOnes (by omega) m.st.input s
      atTheProximityTest := atTheTest first reads L w Said r₁ n₀ toCommon tb₁ tb₂ fx₁ fx₂
        { takenAreTheWritten := D.takenAreTheWritten
          tablesAreLaid := D.tablesAreLaid
          fixedAreLaid := D.fixedAreLaid
          roundsInFront := D.roundsInFront
          widths := D.widths
          standRest := D.standRest
          next := fun k s m E ds y cols s' hT hd hS =>
            ⟨nothing_rides_from_border_two_on h first D.ridersAreTheTiedOnes (by omega)
              y.2.st.input s',
              by
              show L.keeps ⟨3, none, 2, .K12⟩ s s'
              rw [D.keepsAreTheLastKeeps]
              exact ⟨fun hq => by rcases hq with hq | hq <;> exact absurd hq (by decide),
                D.ownHoldsBehindTheTest k s m E ds y cols s' hT hd hS⟩⟩ } fall
      theEndAccepts := last_end_accepts_of_the_run h first reads (lastParts h first L) w Said fall
        D.wholeRun D.line D.keyHasTheSizes D.saidGivesTheField sharedReads sharedParts
        sharedInput }

end AtFullSide.LaterThreads

#print axioms AtFullSide.LaterThreads.nothing_rides_from_border_two_on
#print axioms AtFullSide.LaterThreads.owes_and_yes_at_the_last_thread_finest
