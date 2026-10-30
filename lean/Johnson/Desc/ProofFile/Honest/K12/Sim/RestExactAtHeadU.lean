-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/RestExactAtHeadU.lean: an instance of a theorem, no member: it
counts nothing. The frame's sentence `ExactMember` (Johnson/Desc/ProofFile/Honest/Small/Field.lean),
UNDER A CONDITION THAT NOTHING HERE SHOWS TO HOLD AT ANY STATE OF A RUN (`onFreeT`,
Sim/TreesExact.lean, at the place's own two first trees), at the bound `budOpened`
(Sim/ExactPlan.lean): under the library's head (`P5J.AtMg`), at both members of the side that
`testSide` (Sim/Row.lean) takes off the description's own shared list at the place of the test on
G_u. At every job at that place which says that the first fold's fresh table has come earlier, and
every simulators' job with three public letters. What is new is that the sentence's public premises
are concluded; at the second member the sentence is as empty as its condition.

  `rest_exact_head_U`   the two public premises; a side is returned, at all falls; it passes
                 `Side.fits`; its two members; the sentence at each

By what. `pubTiesT_head_U`, `openTies_head_U`, `first_head_U` (Sim/RestTiesAtHeadU.lean);
`exact_free_trees` (Sim/TreesExact.lean) at the second member; `exact_first` (Sim/ExactFirst.lean)
at the first: under its public premises `FirstPub`, among them `formPubB J.p = true` (h ≤ k), it
holds at every condition and bound; `first_any_head_U` (Sim/FirstAnyAtHeadU.lean) for these and
for the side.

Limits.
- The sentence stands under its condition On (`onFreeT`: eight clauses on the run). Nothing here
  shows that the condition holds at any state of a run: so this is an instance of a theorem, no
  member; it counts nothing. At the second member the sentence is as empty as its condition.
- It is the text of one field of the frame's record, at a condition and a bound of this folder's
  own.
  `onFreeT` is another condition than `testOn` (Sim/Row.lean), and `budOpened` another bound than
  `testBud` (Sim/Row.lean), at which Sim/FirstAnyAtPlace.lean states the first member's sentence. By
  reading, no theorem (Sim/ExactPlan.lean's head), `budOpened` is the narrower; a sentence at a
  narrower bound says less.
- Nothing joins the two members' sentences: the first samples the spent run anew, the second holds
  the same values fixed. The owner's sentence (the frame's field `fresh`) is not touched.
- Three of the condition's clauses (`door`, `asks`, `trees`) read the input, the rows and other
  parts' random values. No later statement may take the condition as a hypothesis on a run and then
  speak of these random values as sampled anew.
- At the one state function that is typed for this place (`doorUF`, DoorsByShape.lean) the
  condition's clause `asks` follows from its clause `heardFit` and one sentence on values (`SaysAt`;
  `asks_heard`, AsksWhole.lean). At an input and a front at which the fold over the blocks in front
  of the test fails, that sentence holds at all random values, whatever the job's rows are
  (`saysAt_fails`, SaysAtFall.lean). So a statement that rests on it there says nothing on a run.
  Where the fold returns, nothing says that the columns it was handed are the run's own. Neither
  file lies beneath this one.
- "At every job at the place" says nothing on whether any job there is the prover's. Who owns the
  fresh table that came earlier is not named. Among "every job" are jobs of which the sentence says
  nothing of any run, and no book is asked (Sim/FirstAnyAtPlace.lean, Limits).
- The chain's number is a variable, tied to the simulators' job by the equation on the trees that it
  names. Which number the shared chain bears is said by nothing here.
- The state on entry is any function: nothing says that it is the verifier's state. It is shown at
  no job that is played. It speaks of the parts of `proverSideOfProximityTest` (Parts.lean), not of the guarded
  halves.
- How far the text that the parts send (`testAll`, Test.lean) is tied to the library's `bodyAll` is
  said in Test.lean's limits; at this member, which opens the first trees, that is the matter
  itself.
- The full size alone. No example of the head is shown here. No file of this folder states a
  security property by itself. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.RestTiesAtHeadU

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Light
open Johnson.G (codesFull2)
open ProofFile.Honest.Small (ExactMember)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12 (PubTiesT OpenTies onFreeT budOpened exact_free_trees)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **Under the head, at every job at the place of the test on G_u: the public premises; the seated
side; and the sentence at both its members, under one condition and at one bound.** That the
condition holds at a state of a run is had under premises alone (`onFreeT_head_U_paid`,
AtFullSide/K12/OnFreeTAtHeadUPaid.lean): an instance, no member; it counts nothing. -/
theorem rest_exact_head_U {V W X Pb : Type} (h : P5J.AtMg o Z D r Zp Np cF) (J : TestJob W X)
    (Js : SimJob Pb) (chain : ℕ) (hJ : J.p = (fourOf Np).U) (hfr : J.fresh.isNone = false)
    (hs : Js.p = (fourOf Np).U) (ho : Js.own = false)
    (hop : Js.opens = (fourOf Np).U.nums.first.map fun x =>
      ((srcOf chain x.2).1, (srcOf chain x.2).2, x.1.a)) :
    PubTiesT J Js codesFull2 2 ∧
    OpenTies J Js chain (fourOf Np).U.nums.first ∧
    (∀ fs : List (Fall (P5J.F0T o Zp Np cF).S₂),
      ∃ σ : Side (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl
          V W X Pb,
        testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder J Js fs = some σ) ∧
    ∀ (fs : List (Fall (P5J.F0T o Zp Np cF).S₂))
      (σ : Side (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl
        V W X Pb),
      testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder J Js fs = some σ →
      σ.fits = true ∧
      σ.members = [firstMember J Js, restMember J Js] ∧
      ∀ (φ : Face V W Pb) (firstTree : ℕ), ∀ u ∈ σ.members,
        ExactMember φ σ chain firstTree
          (onFreeT φ J Js codesFull2 chain (fourOf Np).U.nums.first)
          (budOpened J.p.nums.stages) u := by
  have T := pubTiesT_head_U h J Js hJ hfr hs ho
  have To := openTies_head_U h J Js hJ chain hop
  have hl : (fourOf Np).U.nums.first.length = 2 := congrArg List.length (first_head_U h)
  obtain ⟨a1, a2, a3⟩ := first_any_head_U (V := V) h J Js hJ hfr hs ho
  refine ⟨T, To, a2, fun fs σ hσ => ?_⟩
  obtain ⟨b1, b2, _⟩ := a3 fs σ hσ
  refine ⟨b1, b2, fun φ firstTree u hu => ?_⟩
  rw [b2] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact exact_first φ σ J Js chain firstTree _ _ hfr a1
  · exact exact_free_trees φ σ J Js codesFull2 chain firstTree _ (by rw [hl]; exact T) To

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.rest_exact_head_U
