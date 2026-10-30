-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/LookOne.lean: the honest side of the kind "lookup" (K3). A
composition: on the rounds that a lookup's stages play, the verifier's hearing returns, and what it
leaves has its values. Conditional on `HB`, on `Lawful` and on one part of keys. Two theorems.

Terms. Honest/K3/GLOSSARY.md ("course", "hearing", "lawful", "world, worth"). `Left` is defined in
Honest/K3/Law/LookLeftOf.lean.

What is shown.
  `look_one`: conditional on `HB`, on `Lawful` and on one part of keys: `hearV` returns on the
    course's rounds; what it heard is the run's; the invariant holds behind the last stage; the
    leaves' own slots are free; and `Left`: all rows are worth 0, the key tree's last form is worth
    alpha less the keys' value, the three claims on the planes hold.
  `lookLeft_one`: the same as `LookLeft` has it: at whatever the hearing returned.

Hypotheses that remain.
  `HB`: five statements of the law of the masked sumcheck's honest part
    (Honest/K3/Law/SumWhole.lean), which are proved in Honest/SumLaw/Law.lean and
    Honest/SumLaw/LawEnds.lean, not here.
  `Lawful`: the summands sum as they should (Honest/K3/Law/Statements.lean); that any summands do is
    other files' to show.
  One part of keys (every lookup of a proof file has one).
  By name: `B`, `hLaw`, `hp`. Besides: `hF`: `Fit R`; `I0`: the invariant in front of the first
    stage; `hx`: the course's stages answer; `hh`: (in `lookLeft_one`) `hearV` returns.

Users. This file is imported by Honest/K3/Law/Top.lean.

Limits. The stages are played alone. The text `planesV` is the kind's own; which text a seated
sub-protocol runs for the claims on the planes is not said here.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.LookLeftOf
import Johnson.Desc.ProofFile.Honest.K3.Law.LookHeardOne
import Johnson.Desc.ProofFile.Honest.K3.Law.StageStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E)
open OnBytes.Model (Fork)
open OnBytes.Slice (GE)
open OnBytes.PscRun (Filled)
open VerifiableInference.Desc.K3 (HeardV hearV)

/-- **Conditional on `HB`, on `Lawful` and on one part of keys: the hearing returns, and what it
leaves has its values.** -/
theorem look_one (B : HB) (W : Type) (R : Course W) (planes : List (E × E) → GE)
    (keys : Nat → Array E → GE) (F : Fork) (x : List Fmt.RoundView) (v : Nat) (hp : R.f.parts = [v])
    (hF : Fit R) (I0 : Inv R 0 F) (hx : R.rounds = some x) (hLaw : Lawful R planes keys) :
    ∃ g G, hearV R.f F x = some (g, G) ∧ HeardIs R g ∧ Inv R (stages R.f).length G ∧
      (∀ j, R.first + firstSlot R.f .leaves ≤ j →
        j < R.first + firstSlot R.f .leaves + Stage.own R.f .leaves → ¬ Filled G j) ∧
      Left R planes keys g G := by
  obtain ⟨g, G, hh, hH, hI, hfree, h1, h2⟩ :=
    lookHeard_one (stageStep B) (leavesStep B) W R F x v hp hF I0 hx
  exact ⟨g, G, hh, hH, hI, hfree,
    lookLeft_of R planes keys F G x g v hp hF (cut_of_rounds R x hF hx) hh hH hI h1 h2 hLaw⟩

/-- **Conditional on `HB` and on one part of keys: the sentence of `LookLeft`.** -/
theorem lookLeft_one (B : HB) (W : Type) (R : Course W) (planes : List (E × E) → GE)
    (keys : Nat → Array E → GE) (F G : Fork) (x : List Fmt.RoundView) (g : HeardV) (v : Nat)
    (hp : R.f.parts = [v]) (hF : Fit R) (I0 : Inv R 0 F) (hx : R.rounds = some x)
    (hh : hearV R.f F x = some (g, G)) (hLaw : Lawful R planes keys) : Left R planes keys g G := by
  obtain ⟨g', G', hh', _, _, _, hL⟩ := look_one B W R planes keys F x v hp hF I0 hx hLaw
  rw [hh] at hh'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh')
  exact hL

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.look_one
#print axioms ProofFile.Honest.K3.Law.lookLeft_one
