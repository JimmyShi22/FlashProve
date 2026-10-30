-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/DrawsAtHead.lean: under the library's head (`P5J.AtMg`,
Johnson/P5J/AtMg.lean) there is a list of challenges that the declared rounds of the first member of
the proximity test on G_u can draw: the frame's test `drawsFit`
(Johnson/Desc/ProofFile/Honest/Frame.lean) is true at a written list. The member is `firstMember`
(Sim/Row.lean) at the job `jobAtU` (JobShared.lean) at the proof file's own plan and the seated
place. It imports Mathlib.

  `dsFull`       the written list: nine challenges, each of one field element, (1, 0, 0); no
                 position
  `draws_UFull`  `drawsFit` is true at it, at the first rounds of the written place `piUFull`
                 (Johnson/Desc/K12/Law/PlacesFull.lean): evaluated by Lean's kernel
  `draws_head_U`   the same at the member's own rounds, under the head

What it is for. Of the hypotheses of the sentence `ExactMember`
(Johnson/Desc/ProofFile/Honest/Small/Field.lean), this is the one that the proof of `exact_first`
(Sim/ExactFirst.lean) spends. It shows that the hypothesis can be met at the full size.

By what. `decls_thin`, `thin_head_U` and `nums_head_U` (Sim/FirstPubAtHead.lean): under the head the
seated place declares the rounds of the written place.

Limits. One list, written by hand: it is no list that a run has drawn. One hypothesis of the
sentence: no stand and no front is written at the full size. The full size alone. No example of the
head is shown here. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstPubAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (T12)
open H2K.Member (piUFull)
open H2K.JointK (laidOf)
open ProofFile.Honest.K12.AtProof (fourOf)

/-- Nine challenges, each of one field element. -/
def dsFull : List Fmt.Drawn := List.replicate 9 ⟨[(1, 0, 0)], [], [], none⟩

theorem draws_UFull :
    drawsFit (((laidOf piUFull).take (firstLen piUFull.nums.stages)).map (·.1)) dsFull = true := by
  decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {V W X Pb : Type}

/-- **Under the head the first member's declared rounds can draw the written list.** -/
theorem draws_head_U (h : P5J.AtMg o Z D r Zp Np cF) (door : W → Front X → T12)
    (weights : W → Weights) (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E))
    (Js : SimJob Pb) :
    drawsFit (((firstMember (V := V)
      (jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U door weights rand u?).toRun.toTest Js).rounds).map
        (·.1)) dsFull = true := by
  show drawsFit (((laidOf (fourOf Np).U).take (firstLen (fourOf Np).U.nums.stages)).map (·.1))
    dsFull = true
  rw [List.map_take, decls_thin, thin_head_U h, ← decls_thin, ← List.map_take, nums_head_U h]
  exact draws_UFull

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.dsFull
#print axioms ProofFile.Honest.K12.Light.draws_UFull
#print axioms ProofFile.Honest.K12.Light.draws_head_U
