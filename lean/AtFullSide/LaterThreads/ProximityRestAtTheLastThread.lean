-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/LaterThreads/ProximityRestAtTheLastThread.lean: CONDITIONAL. THE FULL SIZE ALONE. AT THE BASE MAKER's RETURN, AT `IndexCommitterCoins`.

What is here. THE FIELD atTheProximityTest OF THE SECOND CHAIN's GATHER (`LastThreadDebts`, `LastThreadDebtsTied`; AtFullSide/LaterThreads/): the five statements at member 2 of the second chain's thread (the last chain's proximity test, kind K12) in the threads' writers' structure `FiveAtBorder`, FROM WHAT THE PROXIMITY
TEST's WRITERS LEAVE OPEN IN THEIR FINER LAW `five_at_base_rest` (Honest/K12/AtFile/WBase.lean): that law, which ends in a structure of their own with the same five fields (`FiveAt`), carried over by five projections, with each of its premises a named field. Nothing new is shown.

  `ProximityDebts`   WHAT IS STILL OWED BY OTHERS, one field a debt
  **`five_at_the_proximity_test_rest`**   there is the filling's job M, and from `ProximityDebts` at M the five at 2, at every fall

Not shown here. EVERY FIELD IS A HYPOTHESIS; that they can be met together at one value of the
letters is not shown here (AtFullSide/LaterThreads/OwesAndYesThreeAtTheLetters.lean's head says who
meets what the letters leave). NO THEOREM OF THIS LIBRARY THAT NAMES THIS THREAD SHOWS A STAND OF IT
AT ANY BORDER BEYOND 0 BUT FROM A PREMISE THAT HOLDS ONE. Had: the door (`doorAtTheTerm`,
AtFullSide/Honest/ThreadsAtTheTerm.lean): a stand at border 0 behind stands of the two earlier
threads at their ends and the start's yes, where both ends hold opened columns, under
`ThreadFieldsP` and ready's return; and the general rule `thread_in_second`
(Johnson/Desc/ProofFile/Honest/Law/InsideFile.lean): for three invariants that its premises have
carried by every member, at the two starts and through the door, at a run of runC that returns,
where ready returns, the plan is fit and served, the draws are due and no silent stop fires, a
called part of the second chain is reached from a state at which the third invariant holds. No
statement joins them into one that ends in a stand of this thread. Their file's own words stand: the
job's readers are the filling's, and one of `StandRest`'s clauses has a payer only where `reads` and
`first` are the same
terms; NOT IN FRONT OF A LAW OVER COINS. Nothing on hiding, soundness, completeness or any other property.

No property is claimed.
-/
import AtFullSide.LaterThreads.OwesAtTheLastThread
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.LaterThreads
open ProofFile ProofFile.Honest
open ProofFile.Honest.K12 ProofFile.Honest.K12.AtFile
open ProofFile.Honest.K12.Light (ManyJob)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders LastLetters lastThread lastParts)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Third (S₃)
open ToldDesc (ownAt)
open AtFullSide.K12 (jobAtFill)

variable {W₀ W₂ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **WHAT THE FIVE AT THE LAST CHAIN's PROXIMITY TEST STILL TAKE FROM OTHERS.** A definition, meant as a hypothesis: one field a debt. -/
structure ProximityDebts (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ IndexCommitterCoins) (L : LastLetters A) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (Said : ℕ → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (M : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit) (r₁ n₀ : ℕ)
    (toCommon : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → W₂)
    (tb₁ : Fmt.TreeSource → Coins A.B → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → List Fmt.Drawn → Place × Table)
    (tb₂ : Fmt.TreeSource → Coins A.B → W₂ → List Fmt.Drawn → Place × Table)
    (fx₁ fx₂ : Fmt.TreeSource → ℕ) : Prop where
  /-- the letters' list of taken trees is the written one: whoever lays `LastLetters` shows it -/
  takenAreTheWritten : L.taken = takenLast
  /-- the trees' tables are the two earlier chains' and the job's own: likewise -/
  tablesAreLaid : L.table = lastTable r₁ toCommon tb₁ tb₂ (ownLast M.toRun.toTest () n₀)
  /-- the numbers at which the trees are fixed are the two earlier chains' and the job's own: likewise -/
  fixedAreLaid : L.fixed = lastFixed r₁ fx₁ fx₂ fun τ => n₀ + seedRound M.toRun.toTest.p.nums.stages τ
  /-- n₀ counts the rounds in front of the chain: likewise -/
  roundsInFront : n₀ = (lastThreadAt h first reads L w).front
  /-- the widths of the two earlier chains' tables -/
  widths : WidthsAt r₁ toCommon tb₁ tb₂
  /-- what a stand at the member still owes -/
  standRest : StandRest (Zp := A.Z) (Np := h.places) (cF := h.firstChain)
    (lastThreadAt h first reads L w) Said M
  /-- behind the member's step from a stand the riders at 3 hold and the step keeps what `keeps` says at the member's place: whoever lays the riders and keeps shows it -/
  next : ∀ k s m E ds y cols s', ThrS (lastThreadAt h first reads L w) Said 2 k s m E →
    drawsFit ((ownAt h.places).retype : Block S₃ ProofFile.Cl).rounds ds = true →
    (lastThreadAt h first reads L w).Stepped ((ownAt h.places).retype : Block S₃ ProofFile.Cl) k s m E ds y
      cols s' →
    (lastParts h first L).rides 3 y.2.st.input s' ∧ (lastParts h first L).keeps ⟨3, none, 2, .K12⟩ s s'

/-- CONDITIONAL: on h, hA and D. **THE FIVE AT THE LAST CHAIN's PROXIMITY TEST, FROM WHAT ITS WRITERS LEAVE OPEN.** -/
theorem five_at_the_proximity_test_rest (h : HeadAtReturn files A) (I : WiderIn W₀)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    ∃ M, jobAtFill A.Z h.places h.firstChain I S O A.G = some M ∧
      ∀ (first : FirstThreadParts A) (reads : IndexReaders W₀ IndexCommitterCoins) (L : LastLetters A)
        (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
        (Said : ℕ → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) (r₁ n₀ : ℕ)
        (toCommon : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → W₂)
        (tb₁ : Fmt.TreeSource → Coins A.B → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → List Fmt.Drawn →
          Place × Table)
        (tb₂ : Fmt.TreeSource → Coins A.B → W₂ → List Fmt.Drawn → Place × Table)
        (fx₁ fx₂ : Fmt.TreeSource → ℕ),
        ProximityDebts h first reads L w Said M r₁ n₀ toCommon tb₁ tb₂ fx₁ fx₂ →
        ∀ fall : ℕ → S₃ → List Fmt.Drawn → Option String,
          FiveAtBorder (lastThreadAt h first reads L w) Said fall 2 := by
  obtain ⟨M, hM, H⟩ := five_at_base_rest (W₂ := W₂) h I S O hA
  refine ⟨M, hM, fun first reads L w Said r₁ n₀ toCommon tb₁ tb₂ fx₁ fx₂ D fall => ?_⟩
  have F := H first reads (lastParts h first L) w Said r₁ n₀ toCommon tb₁ tb₂ fx₁ fx₂ ()
    D.takenAreTheWritten D.tablesAreLaid D.fixedAreLaid D.roundsInFront D.widths D.standRest D.next fall
  exact ⟨F.plays, F.behind, F.exchange, F.rides, F.accepted⟩

end AtFullSide.LaterThreads

#print axioms AtFullSide.LaterThreads.five_at_the_proximity_test_rest
