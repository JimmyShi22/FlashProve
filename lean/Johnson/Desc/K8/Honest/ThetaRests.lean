-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/ThetaRests.lean: THE SENTENCE "A LEDGER IS OPEN AND ITS BATCHING ELEMENT IS
θ" PASSES AN ACCEPTING CALL OF EACH RUN OF A SEGMENT THAT THE LIBRARY's `RunRests` NAMES
(Johnson/Desc/First/Link/Law/RunRel.lean: its eight fields on runs: front · back · free · merge ·
join · eq · ls · tests): the library's five closure rules for a property of a ledger
(`LinkJoin.ForkRests`, Johnson/Desc/First/Link/Law/SizedRides.lean) at that property. The sister of
Johnson/Desc/K8/Honest/LaterRests.lean: the library's "later" names no batching element. For the
smallness test's tests behind the adding: its run "K8.equations" lays vectors of powers of its own
ledger's element; the tests compare them with the powers of the element of the ledger at which they
are called. Lemmas on the library's own text; none of its goals.

  **`theta_rests`**   ForkRests fun G => G.theta = θ: each rule by the library's own law that the
                   step in question leaves the ledger's core
  **`rests_theta`**   so: RunRests fun e e₁ => HasFork (·.theta = θ) e → HasFork (·.theta = θ) e₁
                   (by the library's `rests_fork`)
Limits. THE RUNS THAT `RunRests` NAMES ALONE: a lookup's runs are not among them. NOTHING ON THE
ADDING OF THE CLAIMS, which stands between the gatherer's runs and the tests; nothing on the draw,
which lays the element. That no run between writes the data's vectors of powers is not said here.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.First.Link.Law.SizedRides
import Johnson.Desc.First.Batch.Law.Coef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (hideRun_core paid_core)
open VerifiableInference.Desc.First.TailClaims.Law (eq_side)
open VerifiableInference.Desc.K9L (core_coefBody)
open VerifiableInference.Desc.LinkJoin (ForkRests HasFork RunRests rests_fork)

/-- **The five rules at "the batching element is θ".** -/
theorem theta_rests (θ : E) : ForkRests fun G => G.theta = θ where
  later _ _ hc _ h := hc.theta.trans h
  hide _ _ _ _ _ hr h := (hideRun_core hr).theta.trans h
  paid F i h := (paid_core F i).theta.trans h
  eq _ _ _ _ _ _ _ he h := (eq_side he).theta.trans h
  coef tl g F h := (congrArg (·.2.1) (core_coefBody tl g F)).trans h

/-- **So the sentence passes each run that `RunRests` names.** -/
theorem rests_theta (θ : E) :
    RunRests fun e e₁ => HasFork (fun G => G.theta = θ) e → HasFork (fun G => G.theta = θ) e₁ :=
  rests_fork (theta_rests θ)

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.theta_rests
#print axioms VerifiableInference.Desc.First.K8.Honest.rests_theta
