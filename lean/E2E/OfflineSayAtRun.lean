-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineSayAtRun.lean: THE ONE CLAUSE OF TRUTH in the condition at a proximity test's second part, as a named
sentence, general in the job: in front of the test, and at one run. Definitions alone.

  `SaysInFront J w fr R`   the rows that the test takes in hold at the words of the plain rows R: the clause `allSay` of
                         `DataFront` (Johnson/Desc/ProofFile/Honest/K12/ShapeAll.lean), to the letter
  `SayAtRun`               that sentence at one run: where the test's second part was called, at the state that the walk
                         has there and the blocks that the book carries to it: at the state's input, the front as the
                         second part lays it (`restFront`) and the carried coins (`carriedCoins`, K12/Sim/Row.lean).
                         `rows`: the job's plain rows, of the input, the front and the coins. `called`: the run's test that a
                         part was called. `mid`: the walk's state in front of a part

Nothing is shown here. The sentence reads the input and the carried coins: no later law may take it as a hypothesis on
a run and then speak of the coins as sampled anew. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.ShapeAll
import Johnson.Desc.ProofFile.Honest.K12.Sim.Row

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open ProofFile.Honest ProofFile.Honest.K12

variable {W X : Type}

/-- **The rows that the test takes in hold at the words of R.** -/
def SaysInFront (J : TestJob W X) (w : W) (fr : Front X) (R : PlainRows) : Prop :=
  ∀ G, (J.rec₀ w fr).st.groups[(J.rec₀ w fr).g]? = some G →
    AllSay rdE (begun (J.rec₀ w fr).st (J.rec₀ w fr).g G) (runRows (J.rec₀ w fr).st G).toList
      (wordsAt (begun (J.rec₀ w fr).st (J.rec₀ w fr).g G) (layoutOf (J.rec₀ w fr).st G) R)

/-- **The same at one run, at the called second part.** V: the type of what a second stop may read, which the
carried blocks do not see. -/
def SayAtRun (V : Type) (J : TestJob W X) (rows : W → Front X → TestCoins → PlainRows) {Bk : ProverCoinCounts}
    (k : Coins Bk) (chain : ℕ) (a : VerifiableInference.Desc.Place) (called : Addr → Bool)
    (mid : Addr → Except ProofFile.Honest.Refusal (Option (Mid W X))) : Prop :=
  called ⟨a, 1⟩ = true → ∀ (m : Mid W X) (ca : CsAll (restPart J : Part V W X).carries),
    mid ⟨a, 1⟩ = .ok (some m) → carriedAt Bk k chain ⟨a, 1⟩ (restPart J : Part V W X) = .ok ca →
    SaysInFront J m.st.input (restFront J m)
      (rows m.st.input (restFront J m) (carriedCoins J (stretches _ ca)))

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.SaysInFront
#print axioms AtPublicFiles.OfflineRows.SayAtRun
