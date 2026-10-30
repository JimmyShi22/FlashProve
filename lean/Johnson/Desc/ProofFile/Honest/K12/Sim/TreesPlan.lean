-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/TreesPlan.lean: the law `core_inv_trees` (Sim/TreesLaw.lean)
with its heaviest premise sorted by what it reads, as Sim/PlanLaw.lean sorts `core_inv`'s: the
plan's half as a test with code on the place and the table of codes, at the number of trees that the
first switch opens (`planB J.p K Dp.ts.length`) · the verifier's state's shape · the challenges'
form · the prover's data. The same equation of two texts' laws. No property is claimed, and it is no
sentence on a simulator.

  `behind_of_plan_trees`   the four sorts give the invariant of the later stages behind the first
                 switch, at the job's own trees, at every family of the switches' random values
  `law_of_plan_trees`   the law

By what. `wanted_of_plan` (Sim/PlanLaw.lean) is general in the number of trees and is called; the
job's trees are the group's by `DataAsks.trees`: no clause "one tree" is wanted.

Limits. The arm where the first fold's fresh table came earlier alone: `ShapeAsks.came` asks it of
the state, `planB` of the place (its clauses on the first fold's rounds and on the later stages,
whose `PlanFrom`, Johnson/Prover/Link/FormStepPlan.lean, asks `ownMask = false`): where the first
fold sends its own table both statements hold emptily. No row that the test takes in has a
written-out factor (`ShapeAsks.plainRows`, PlanB.lean): by the library's own heads the key file's
and the proof file's tests take in such rows (Johnson/Prover/Link/FormRow.lean, BodyInv.lean,
Limits), and it is at these files' places that Sim/TreesReach.lean and Sim/TreesPlanAt.lean show the
public clauses. `ShapeAsks`, `FormAsks` and `DataAsks` are asked, at one value of the input, the
front, the carried random values and the challenges. `DataAsks` reads the input and another part's
random values. `ShapeAsks`' clauses behind the first fold hang, by type, on the text's own rounds.
That the two lists of trees give the first opening the same groups is asked; so are, in
`law_of_plan_trees`, `FitsBody`, h ≤ k behind the first stage, and that the positions asked are
among those that the next reading round samples. At the level of oracle messages: no root, salt or
hash. On the right side the rows and the first fold's coefficients still stand, through the
verifier's state behind the first fold alone; and tB is `J.recB w fr (D 0)`: the job's field `rec₀`
takes the input by type. Nothing on completeness, soundness or hiding.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesLaw
import Johnson.Desc.ProofFile.Honest.K12.Sim.PlanLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open OnBytes.LinkSim.AtText (FitsBody)

attribute [local instance] csNonempty

variable {W X : Type}

/-- The invariant behind the first switch, in Sim/TreesLaw.lean's form, at the job's own trees, at
every family of the switches' random values. -/
theorem behind_of_plan_trees (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (K : Codes) (Dp : Plain) (cc : ℕ → ℕ → List UInt64) (R : PlainRows)
    (hP : planB J.p K Dp.ts.length = true) (S : ShapeAsks J w fr C D K Dp)
    (F : FormAsks J w fr C D) (Dt : DataAsks J w fr C D Dp cc R)
    (a next nx' : Fmt.M1.Stage) (rest' : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = a :: next :: nx' :: rest') (c : ℕ → GE) :
    BehindFirstT J.p a next (nx' :: rest') (laidS J.p) (J.recB w fr (D 0)) (J.first w fr C) C.hide
      (J.trees₀ w fr C.mem (J.first w fr C)) D c := by
  obtain ⟨a', n', x', r', hst', hW⟩ := wanted_of_plan J w fr C D K Dp cc R hP S F Dt c
  rw [hst] at hst'
  injection hst' with e1 e2
  injection e2 with e2 e3
  injection e3 with e3 e4
  subst e1 e2 e3 e4
  unfold Wanted at hW
  unfold BehindFirstT
  rw [← hst, Dt.trees]
  exact hW

/-- **The law, from the four sorts**, at the job's own trees and at any trees that give the first
opening the same groups. -/
theorem law_of_plan_trees (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (K : Codes) (Dp : Plain) (cc : ℕ → ℕ → List UInt64) (R : PlainRows)
    (hP : planB J.p K Dp.ts.length = true) (S : ShapeAsks J w fr C D K Dp)
    (F : FormAsks J w fr C D) (Dt : DataAsks J w fr C D Dp cc R)
    (a next nx' : Fmt.M1.Stage) (rest' : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = a :: next :: nx' :: rest') (treesF : List Tree)
    (hF : FitsBody D (next :: nx' :: rest') a 1) (hlow : ∀ st ∈ next :: nx' :: rest', st.h ≤ st.k)
    (hG : aGroups a 1 (J.trees₀ w fr C.mem (J.first w fr C)) D = aGroups a 1 treesF D)
    (dep : ℕ → Option ℕ) (n : ℕ) (asks : List (List (List ℕ)))
    (hasks : ∀ i, ∀ q ∈ (((asks[i]?).getD [])[0]?).getD [],
      q ∈ openedTr D (next :: nx' :: rest') a 1 (1 + ((sgOf a).h + (sgOf a).g) + i)) :
    PMF.map (fun c : OwnCs a (next :: nx' :: rest') =>
        realOwnT J.p a next (nx' :: rest') (laidS J.p) (J.recB w fr (D 0)) (J.first w fr C) C.hide
          (J.trees₀ w fr C.mem (J.first w fr C)) D dep n asks (stretchOf c).e)
        (Prob.unif (OwnCs a (next :: nx' :: rest'))) =
      PMF.map (fun c : OwnCs a (next :: nx' :: rest') =>
        zeroOwnT J.p a next (nx' :: rest') (laidS J.p) (J.recB w fr (D 0)) (J.first w fr C) C.hide
          treesF D dep n asks (stretchOf c).e)
        (Prob.unif (OwnCs a (next :: nx' :: rest'))) :=
  core_inv_trees J.p a next nx' rest' (laidS J.p) (J.recB w fr (D 0)) (J.first w fr C) C.hide _
    treesF D dep n asks hF hlow hG
    (fun c => behind_of_plan_trees J w fr C D K Dp cc R hP S F Dt a next nx' rest' hst
      (stretchOf c).e) hasks

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.behind_of_plan_trees
#print axioms ProofFile.Honest.K12.law_of_plan_trees
