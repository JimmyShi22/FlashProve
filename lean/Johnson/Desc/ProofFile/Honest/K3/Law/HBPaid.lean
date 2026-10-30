-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/HBPaid.lean: the honest side of the kind "lookup" (K3). The
hypothesis `HB` (Honest/K3/Law/SumWhole.lean: five statements of the law of the masked sumcheck's
honest part), shown by the theorems of Honest/SumLaw/Law.lean and Honest/SumLaw/LawEnds.lean, and
the lookup's theorems without that hypothesis. Theorems.

Terms. Honest/K3/GLOSSARY.md.

What is shown.
  `hb : HB`.
  `stageStepP`, `leavesStepP`, `lookOneP`, `lookLeftOneP`, `heardInnerP`, `leftInnerP`: the
    counterparts, without `HB`, of `stageStep`, `leavesStep` (Honest/K3/Law/StageStep.lean),
    `look_one`, `lookLeft_one` (Honest/K3/Law/LookOne.lean), `heardInner` and `leftInner`
    (Honest/K3/Law/Top.lean).
The forms that assume `HB` stay.

Hypotheses that remain. One part of keys (`hp`); `Lawful` (`hLaw`). In `lookOneP` and `lookLeftOneP`
besides, as in their counterparts: `hF`: `Fit R`; `I0`: the invariant in front of the first stage;
`hx`: the course's stages answer; `hh`: (in `lookLeftOneP`) `hearV` returns.

Imported. The files under Honest/SumLaw/. Whatever rests on this file
rests on them.

Users. This file is imported by Honest/K3/Law/AtSite.lean and Honest/K3/Law/Joined.lean.

Limits. Those of the files whose theorems are called.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Top
import Johnson.Desc.ProofFile.Honest.SumLaw.Law
import Johnson.Desc.ProofFile.Honest.SumLaw.LawEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E)
open OnBytes.Model (Fork)
open OnBytes.Slice (GE)
open OnBytes.PscRun (Filled)
open VerifiableInference.Desc.K3 (HeardV hearV)

/-- **The hypothesis `HB`, shown** by five theorems of Honest/SumLaw/. -/
theorem hb : HB :=
  ⟨SumLaw.sumSays, SumLaw.sumHeard, SumLaw.sumClaim, SumLaw.sumLeft, SumLaw.sumEnds⟩

/-- The step at a stage with end values. It rests on the theorems of Honest/SumLaw/. What it says of
the row's worth is conditional on the stage's summand summing as it should. -/
theorem stageStepP : StageStep := stageStep hb

/-- The step at the leaves. It rests on the theorems of Honest/SumLaw/. What it says of the late
row's worth is conditional on the leaves' summand summing to cf. -/
theorem leavesStepP : LeavesStep := leavesStep hb

/-- Conditional on `Lawful` and on one part of keys: the hearing returns on the course's rounds, and
what it leaves has its values. It rests on the theorems of Honest/SumLaw/. -/
theorem lookOneP (W : Type) (R : Course W) (planes : List (E × E) → GE)
    (keys : Nat → Array E → GE) (F : Fork) (x : List Fmt.RoundView) (v : Nat) (hp : R.f.parts = [v])
    (hF : Fit R) (I0 : Inv R 0 F) (hx : R.rounds = some x) (hLaw : Lawful R planes keys) :
    ∃ g G, hearV R.f F x = some (g, G) ∧ HeardIs R g ∧ Inv R (stages R.f).length G ∧
      (∀ j, R.first + firstSlot R.f .leaves ≤ j →
        j < R.first + firstSlot R.f .leaves + Stage.own R.f .leaves → ¬ Filled G j) ∧
      Left R planes keys g G :=
  look_one hb W R planes keys F x v hp hF I0 hx hLaw

/-- Conditional on `Lawful` and on one part of keys: the sentence of `LookLeft`. It rests on the
theorems of Honest/SumLaw/. -/
theorem lookLeftOneP (W : Type) (R : Course W) (planes : List (E × E) → GE)
    (keys : Nat → Array E → GE) (F G : Fork) (x : List Fmt.RoundView) (g : HeardV) (v : Nat)
    (hp : R.f.parts = [v]) (hF : Fit R) (I0 : Inv R 0 F) (hx : R.rounds = some x)
    (hh : hearV R.f F x = some (g, G)) (hLaw : Lawful R planes keys) : Left R planes keys g G :=
  lookLeft_one hb W R planes keys F G x g v hp hF I0 hx hh hLaw

/-- One part of keys (in the statement): the hearing returns on what the seated row's play yields.
It rests on the theorems of Honest/SumLaw/. -/
theorem heardInnerP : HeardInner := heardInner hb

/-- One part of keys, and `Lawful` for its last clause (both in the statement): what holds behind
the hearing's return. It rests on the theorems of Honest/SumLaw/. -/
theorem leftInnerP : LeftInner := leftInner hb

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.hb
#print axioms ProofFile.Honest.K3.Law.stageStepP
#print axioms ProofFile.Honest.K3.Law.leavesStepP
#print axioms ProofFile.Honest.K3.Law.lookOneP
#print axioms ProofFile.Honest.K3.Law.lookLeftOneP
#print axioms ProofFile.Honest.K3.Law.heardInnerP
#print axioms ProofFile.Honest.K3.Law.leftInnerP
