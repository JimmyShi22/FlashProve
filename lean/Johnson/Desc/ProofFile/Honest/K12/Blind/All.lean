-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Blind/All.lean: What the two parts of the prover's side of a
proximity test send does not hang on the targets of the rows in the state on entry. The five
equations of Top.lean (`Steps`) hold, each by a theorem of this folder; so the statements of
Top.lean stand here without that premise.

  `theSteps`     the five: `front_agree` (Front.lean), `bat_agree` and `batBehind_agree` (Bat.lean),
                 `fold_agree` (Fold.lean), `switch_agree` (Switch.lean)
  `stagesAll_one`   all that is shown in the stages is one at two records that agree but for targets
  `testAll_one`, `testAll_one₂`   the test's text is one at two states on entry that agree but for
                 targets: at one input and front
  `testHalf_one`   the pair of parts is one, counts, names, stops, shares and moves, at two jobs
                 whose states on entry agree so at every input and front

What it is for. A job whose state on entry is made by the description's own fold at made-up columns,
its targets wiped, sends what a job sends whose state on entry agrees with it but for the rows'
targets. Whether a given state on entry agrees so with the verifier's is another law's; nothing here
says it.

Over what it stands. Files of the kind K10's authors that are not in the library yet
(Johnson/Desc/ProofFile/Honest/K10/: StAtZero, WipeFold, BatWipe, WipeS, Wipe/).

Limits. AT ONE LIST OF GROUPS: THIS IS NO LAW ON A FOLD AT MADE-UP COLUMNS THROUGH THE TEST'S BLOCK:
the columns are the same words on both sides. `Agree` holds coefficients, kinds, marks, the book of
trees, the count of roots, the group's number and the mask's equal: it is no agreement in shape
alone. The verifier runs a sixth part, the base case, which by reading tests a target's value; the
prover's text of the test never runs it; it is not treated here. Nothing on completeness, soundness
or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Blind.Top
import Johnson.Desc.ProofFile.Honest.K12.Blind.Front
import Johnson.Desc.ProofFile.Honest.K12.Blind.Bat
import Johnson.Desc.ProofFile.Honest.K12.Blind.Switch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Blind
open VerifiableInference.Desc.K12 (T12 P12 Laid)
open Johnson.Prover.Link (PS BCoins)

/-- **The five equations hold.** -/
theorem theSteps : Steps :=
  ⟨front_agree, bat_agree, fold_agree, switch_agree, batBehind_agree⟩

/-- **All that is shown in the stages is one at two records that agree but for targets.** -/
theorem stagesAll_one (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) {t t' : T12} (h : Agree t t') (P : PS)
    (trees : List Tree) (D : ℕ → Fmt.Drawn) :
    stagesAll p K rest j cur l o t P trees D = stagesAll p K rest j cur l o t' P trees D :=
  stagesAll_agree theSteps p K rest j cur l o t t' P trees D h

variable {V W X : Type}

/-- **The test's text is one at two states on entry that agree but for targets.** -/
theorem testAll_one (J : TestJob W X) (r' : W → Front X → T12) (w : W) (fr : Front X)
    (h : Agree (J.rec₀ w fr) (r' w fr)) (K : TestCoins) (D : ℕ → Fmt.Drawn) :
    testAll { J with rec₀ := r' } w fr K D = testAll J w fr K D :=
  testAll_agree theSteps J r' w fr h K D

/-- The same at two jobs. -/
theorem testAll_one₂ (J J' : TestJob W X) (hp : J.p = J'.p) (hm : J.members = J'.members)
    (hf : J.fresh = J'.fresh) (hr : J.rows₀ = J'.rows₀) (ht : J.trees₀ = J'.trees₀) (w : W)
    (fr : Front X) (h : Agree (J.rec₀ w fr) (J'.rec₀ w fr)) (K : TestCoins) (D : ℕ → Fmt.Drawn) :
    testAll J w fr K D = testAll J' w fr K D :=
  testAll_agree₂ theSteps J J' hp hm hf hr ht w fr h K D

/-- **The pair of parts is one.** -/
theorem testHalf_one (J : TestJob W X) (r' : W → Front X → T12)
    (h : ∀ w fr, Agree (J.rec₀ w fr) (r' w fr)) :
    (proverSideOfProximityTest { J with rec₀ := r' } : Placed V W X) = proverSideOfProximityTest J :=
  testHalf_agree theSteps J r' h

end ProofFile.Honest.K12.Blind

#print axioms ProofFile.Honest.K12.Blind.theSteps
#print axioms ProofFile.Honest.K12.Blind.stagesAll_one
#print axioms ProofFile.Honest.K12.Blind.testAll_one
#print axioms ProofFile.Honest.K12.Blind.testAll_one₂
#print axioms ProofFile.Honest.K12.Blind.testHalf_one
