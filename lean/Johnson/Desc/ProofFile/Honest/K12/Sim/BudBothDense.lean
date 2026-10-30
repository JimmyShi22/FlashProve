-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/BudBothDense.lean: the "dense" twins of `exact_rest_both`,
`exact_both_own`, `exact_both_earlier` (BudBoth.lean in this folder).

What it is. BudBoth.lean states both members' sentences of a proximity test at one condition,
`onFreeT` (TreesExact.lean), and one bound, `budBoth`. The twins state them at the condition
`onFreeTD` (TreesExactDense.lean), whose `ShapeAsksD` (PlanBDense.lean in the folder above) asks
`DenseRow` of the rows taken in at the group under test, where `onFreeT` asks that no open row and
no sample row of the whole statement on entry has a written-out variable. Apart from that name and
the twins' names, each statement is the old one, letter for letter.

Why. A list of the frame has one condition for all members. At a state on entry in which an open row
or a sample row has a written-out variable `onFreeT` does not hold at the second member.

Main names. `exact_rest_both_dense`, `exact_both_own_dense`, `exact_both_earlier_dense`.

By what. Each proof is the old proof with the twins' names in it. The first member's sentences,
`exact_first_job` (ExactFirstOwn.lean) and `exact_first` (ExactFirst.lean), hold at every condition
and are called as they stand.

Limits.
- `exact_both_own_dense` has content for the first member alone, like `exact_both_own`: at a place
  whose `ownMask` is true no `PubTiesT` exists (`reach_gives_trees`, TreesReach.lean), and
  `ShapeAsksD.came` asks a mask on entry. So both members' sentences stand at one condition and one
  bound, with content, only where the fresh table has come earlier.
- These statements stand over Johnson/Prover/Link/FormFirst.lean, whose structure
  `TestFront` has the field `dense`, as all the twins do
  (Johnson/Desc/K12/Honest/Shape/TestDoorDense.lean says why).
- They do not reach the first chain's proximity test yet: these files do not show `onFreeTD` at a
  run there.
- The state on entry is the job's own `rec₀`. It is not shown to be the verifier's.
- The first member's sentences are had under the public hypotheses T₀ (`FirstPub`, ExactFirst.lean;
  `FirstPubOwn`, ExactFirstOwn.lean). Among these are `formPubB J.p = true`, whose first clause is h
  ≤ k, and `Js.p = J.p`: the simulators' job and the prover's job stand at one place.
- The limits of BudBoth.lean hold here too.
- Nothing here is a statement on completeness, on soundness or on what a proof hides.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.BudBoth
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesExactDense

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ProofFile.Honest.K12.Light
open OnBytes.Slice.ProxRun (DenseRow denseRow_of_plain)
open VerifiableInference.Desc (FileDescription Block Place)
open VerifiableInference.Desc.K12 (P12)
open Desc.K14 (St)
open ProofFile.Honest.Small (ExactMember)
open ProofFile.Honest.K12.AtProof (fourOf)
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {pO : P12}
variable {S Cl V W X Pb : Type}

/-- The twin of `exact_rest_both` (BudBoth.lean): the second member's sentence at `onFreeTD` and
`budBoth`, from `exact_free_trees_dense` through `exact_bud`. -/
theorem exact_rest_both_dense (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X)
    (Js : SimJob Pb) (K : OnBytes.Codes) (chain firstTree : ℕ)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (T : PubTiesT J Js K os.length)
    (To : OpenTies J Js chain os) :
    ExactMember φ σ chain firstTree (onFreeTD φ J Js K chain os) (budBoth Js)
      (restMember J Js) := by
  refine exact_bud (fun ds asks hb => ?_)
    (exact_free_trees_dense φ σ J Js K chain firstTree os T To)
  have h1 := (both_rest Js ds asks).1 hb
  rw [T.place] at h1
  exact h1

/-- The twin of `exact_both_own` (BudBoth.lean): both members' sentences at `onFreeTD` and
`budBoth`, stated where the first fold sends its own table. The second member's half says nothing at
a place whose `ownMask` is true: the hypothesis T has the field `reach`, and `reach_gives_trees`
(TreesReach.lean) draws `ownMask = false` from it, so no such T exists there. The first member's
half is `exact_first_job`, which needs no T. -/
theorem exact_both_own_dense (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X)
    (Js : SimJob Pb) (K : OnBytes.Codes) (chain firstTree : ℕ)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (hfr : J.fresh.isNone = true) (T₀ : FirstPubOwn J Js)
    (T : PubTiesT J Js K os.length) (To : OpenTies J Js chain os) :
    ∀ u ∈ [firstMember J Js, restMember J Js],
      ExactMember φ σ chain firstTree (onFreeTD φ J Js K chain os) (budBoth Js) u := by
  intro u hu
  rcases List.mem_cons.1 hu with rfl | hu'
  · exact exact_first_job φ σ J Js chain firstTree _ hfr T₀
  · rcases List.mem_cons.1 hu' with rfl | hu''
    · exact exact_rest_both_dense φ σ J Js K chain firstTree os T To
    · cases hu''

/-- The twin of `exact_both_earlier` (BudBoth.lean): both members' sentences at `onFreeTD` and
`budBoth`, where the fresh table has come earlier. -/
theorem exact_both_earlier_dense (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X)
    (Js : SimJob Pb) (K : OnBytes.Codes) (chain firstTree : ℕ)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (hfr : J.fresh.isNone = false) (T₀ : FirstPub J Js)
    (T : PubTiesT J Js K os.length) (To : OpenTies J Js chain os) :
    ∀ u ∈ [firstMember J Js, restMember J Js],
      ExactMember φ σ chain firstTree (onFreeTD φ J Js K chain os) (budBoth Js) u := by
  intro u hu
  rcases List.mem_cons.1 hu with rfl | hu'
  · exact exact_first φ σ J Js chain firstTree _ _ hfr T₀
  · rcases List.mem_cons.1 hu' with rfl | hu''
    · exact exact_rest_both_dense φ σ J Js K chain firstTree os T To
    · cases hu''

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.exact_rest_both_dense
#print axioms ProofFile.Honest.K12.Light.exact_both_own_dense
#print axioms ProofFile.Honest.K12.Light.exact_both_earlier_dense
