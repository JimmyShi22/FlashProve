-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Shape/ClaimShape.lean: WHAT A RUN OF CLAIMS OWES ON SHAPES: ONE TYPE FOR
ALL KINDS. Types, one small law and one maker of a RunLaw; nothing is evaluated.

Why. The batching of a link (K9.batch, Johnson/Desc/First/Batch/Kind.lean) draws its element, lets
the link's hearing sub-protocols make their claims, run by run in the link's order
(claimsInBy, Johnson/Desc/Block.lean), and adds each claim under its weight
(K9.addList, Johnson/Desc/First/Batch/Add.lean). The adding tests marks, indices and sizes alone: of
a claim it reads which entries, slots and runs the claim names, not one coefficient. So, to follow
the batching on the shape of the chain's state (chainSh, Johnson/Desc/First/Shape/Chain.lean), a run
must say on shapes two things: the shape of the state behind it, AND THE SHAPES OF ITS CLAIMS
(ClaimSh, claimSh: Johnson/Desc/First/Shape/Parts.lean).

  `Run`: the type of a run of claims, as a sub-protocol states it: from the number of claims
    gathered so far and the state to its claims and the state behind.
  **`RunLaw run`**: what is owed of a run:
    `runG`     THE RUN ON SHAPES: from that number and the state's shape to the claims' shapes and
              the shape behind; or a refusal.
    `pre`      the run's own premises on the state, by name: tests on values, and whatever its shape
              does not hold. Where there is none: fun _ _ => True.
    `carries`  pre n s holds, the run returns (cs, s') at (n, s), and runG returns y at
              (n, chainSh s): then y is (the shapes of cs, chainSh s'). UNDER pre: where a shape
              behind hangs on a value's not being 0, no such law can hold from a bare return of the
              run. Whoever has it without pre gives it for nothing.
    `returns`  runG returns at (n, chainSh s), and pre n s holds: then the run returns at (n, s).
  `RunLaw.follows`: so, where runG returns y and pre holds: the run returns some (cs, s') whose
    shapes are y.
  `RunLaw.ofStrong`: a law in the stronger form "the run returns (cs, s'): then runG returns their
    shapes" gives `carries`.

Limits. Types. A RunLaw CAN BE IDLE IN TWO WAYS, and one of each sort exists for every run: its runG
always refuses; or its pre never holds (with pre := fun _ _ => False BOTH fields, carries and
returns, are met by any runG). SO A RunLaw IS WORTH WHAT ITS runG RETURNS AND WHAT ITS pre ASKS:
whoever counts one names its runG and its pre, says at which shapes the runG has been seen to
return, and who pays the pre. A DEBT BY NAME: "a return of the run gives its pre", run by run: with
it carries would speak at every return. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Shape.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9.Shape
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh ClaimSh claimSh)

/-- A run of claims, as a sub-protocol states it. -/
abbrev Run : Type := Nat → S → Except String (List Claim × S)

/-- **What a run of claims owes on shapes.** -/
structure RunLaw (run : Run) where
  /-- the run on shapes -/
  runG : Nat → ChainSh → Except String (List ClaimSh × ChainSh)
  /-- the run's own premises on the state, by name -/
  pre : Nat → S → Prop
  carries : ∀ (n : Nat) (s s' : S) (cs : List Claim) (y : List ClaimSh × ChainSh), pre n s →
    run n s = .ok (cs, s') → runG n (chainSh s) = .ok y → y = (cs.map claimSh, chainSh s')
  returns : ∀ (n : Nat) (s : S) (y : List ClaimSh × ChainSh),
    runG n (chainSh s) = .ok y → pre n s → ∃ z, run n s = .ok z

/-- Where the run on shapes returns and the premises hold, the run returns, with these shapes. -/
theorem RunLaw.follows {run : Run} (R : RunLaw run) (n : Nat) (s : S)
    (y : List ClaimSh × ChainSh) (hg : R.runG n (chainSh s) = .ok y) (hp : R.pre n s) :
    ∃ cs s', run n s = .ok (cs, s') ∧ y = (cs.map claimSh, chainSh s') := by
  obtain ⟨⟨cs, s'⟩, hz⟩ := R.returns n s y hg hp
  exact ⟨cs, s', hz, R.carries n s s' cs y hp hz hg⟩

/-- From the stronger form of "carries". -/
def RunLaw.ofStrong {run : Run} (runG : Nat → ChainSh → Except String (List ClaimSh × ChainSh))
    (pre : Nat → S → Prop)
    (strong : ∀ (n : Nat) (s s' : S) (cs : List Claim), run n s = .ok (cs, s') →
      runG n (chainSh s) = .ok (cs.map claimSh, chainSh s'))
    (returns : ∀ (n : Nat) (s : S) (y : List ClaimSh × ChainSh),
      runG n (chainSh s) = .ok y → pre n s → ∃ z, run n s = .ok z) : RunLaw run where
  runG := runG
  pre := pre
  carries := fun n s s' cs _ _ h hg => Except.ok.inj (hg.symm.trans (strong n s s' cs h))
  returns := returns

end VerifiableInference.Desc.K9.Shape

#print axioms VerifiableInference.Desc.K9.Shape.RunLaw.follows
#print axioms VerifiableInference.Desc.K9.Shape.RunLaw.ofStrong
