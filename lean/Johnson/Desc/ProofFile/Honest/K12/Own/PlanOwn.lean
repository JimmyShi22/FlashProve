-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Own/PlanOwn.lean: THE PLAN's TEST WHERE THE FIRST FOLD SENDS ITS
OWN MASK. Five definitions (two for the controls alone); statements and proofs; twelve closed facts
by an evaluation in Lean's kernel.

What. `planB` (PlanB.lean in the folder above) fails at the library's written places of such a test
in just two of its 22 clauses (`planNo_O_full` and its like, Sim/TreesPlanAt.lean): the first fold's
cut, and the later stages' plan. `planOL` is `planL` with these two turned: the cut is `foldCutOwn`
(Johnson/Desc/K12/Honest/OwnFold.lean); the later stages' plan is asked at the renumbered place
(`renumP`, Renumber.lean in this folder), at the rounds of p. Its text was made of `planL`'s own by
a program that turns these two clauses.

  `planOL`, `planOB`, `planONo`   the clauses under their names; all hold; the names of those that
                 do not
  `renumByP`, `laterNo`, `renumByP_one`   for the controls alone
  `planAll_of_OB`   the library's public facts on the later stages (`PlanAll`,
                 Johnson/Prover/Link/BodyCloseB.lean) at the renumbered place, at the rounds of p
  `switchPlan_renum`, `firstSwitchPlan_renum`   what is public at the first switch goes over
  `planOB_O_full`, `planOB_O_small`, `planOB_KO_full`   the test says yes at the three written
                 places
  `planONo_O_two`, `planONo_O_four`   the number of trees that the first switch opens, 3, is pinned
                 from both sides
  `planONo_U_full`, `planONo_W_full`, `planONo_L_full`   where the mask has come earlier just the
                 two turned clauses refuse
  `laterNo_O_zero`, `laterNo_O_one`, `laterNo_O_two`, `laterNo_O_self`   at the written place of the
                 test on G_omega: of the counts `free + 0`, `free + 1`, `free + 2` the second alone
                 fits; at the place itself the flag refuses at every stage, and the label at the
                 last switch

Limits.
- AT `renumP p` THE FIRST FOLD's OWN MASK TREE IS LEFT OUT OF THE LISTS (`lists_own`,
  Renumber.lean). SO NOTHING THAT IS DRAWN AT `renumP p` MAY BE QUOTED OF STAGE 0, OF "ALL THE
  TEST's TREES", OR OF ANY COUNT OR BUDGET OVER THEM. THREE STATEMENTS HERE ARE HELPERS THAT
  CONCLUDE AT THE RENUMBERED PLACE (`planAll_of_OB`, `switchPlan_renum`, `firstSwitchPlan_renum`):
  each is a premise of the library's `bodyInv_first_all` (Johnson/Prover/Link/BodyBehindAll.lean) at
  that place; none is a bridge or a top. A fourth names it: `renumByP_one`, an equation for the
  controls alone. `planAll_of_OB` speaks from the second stage on, at the rounds behind the first
  switch. Twenty-one of the test's 22 clauses are asked at p itself.
- A "true" counts nothing by itself: a public test on the plan. The written places and the tables of
  codes are closed terms that a program made off the print of a run (Sim/TreesPlanAt.lean's limit).
- `firstSwitchPlan_renum`: where a further stage follows the next one; the other case is not stated.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean in the folder above.
-/
import Johnson.Desc.ProofFile.Honest.K12.Own.Renumber
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesPlanAt
import Johnson.Desc.K12.Honest.OwnFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Own
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Sh (TermAsks SwitchPub claimsB testSh readPubB singleSh switchPub_of runRows_plain
  switchPubB)
open H2K.Member

/-- The plan's half where the first fold sends its own mask: `planL` with two clauses turned: the
first fold's cut is `foldCutOwn`; the later stages' plan is asked at the renumbered place, at the
rounds of p. -/
def planOL (p : P12) (K : Codes) (nT : ℕ) : List (String × Bool) :=
  match p.nums.stages with
  | a :: next :: nx' :: rest' =>
    let Z := lettersOf p a next
    [("rounds", (H2U.roundsOfNums p.nums).isSome),
     ("oracle messages", (H2U.testOracles p.nums).isSome),
     ("switchPubB", switchPubB p K 0 a next (nx' :: rest').isEmpty ⟨Z.i.1, Z.i.2, a.k, a.h⟩ Z.n Z.dS
       Z.dC),
     ("batCut", batCut (((laidOf p).take 1).map (·.1))),
     ("foldCutOwn", foldCutOwn a.k (((laidS p).take (1 + a.k)).map (·.1))),
     ("h ≤ k", decide (a.h ≤ a.k)),
     ("the first stage", decide (stageAt p 0 a = some ⟨Z.i.1, Z.i.2, a.k, a.h⟩)),
     ("two rounds", decide (((((laidS p).drop (1 + a.k)).take 2).map (·.1)).length = 2)),
     ("nF", decide ((foldAt guardedProximityTestParts p 0 a (laidS p) : Block T12 Unit).rounds.length =
       1 + ((sgOf a).h + (sgOf a).g))),
     ("oF", decide ((foldAt guardedProximityTestParts p 0 a (laidS p) : Block T12 Unit).openings = 0)),
     ("nS", decide ((switchAt guardedProximityTestParts p 0 a next (nx' :: rest').isEmpty (laidS p) :
       Block T12 Unit).rounds.length = 2)),
     ("oS", decide ((switchAt guardedProximityTestParts p 0 a next (nx' :: rest').isEmpty (laidS p) :
       Block T12 Unit).openings = nT)),
     ("nB", decide ((batAt guardedProximityTestParts p (laidOf p) : Block T12 Unit).rounds.length = 1)),
     ("oB", decide ((batAt guardedProximityTestParts p (laidOf p) : Block T12 Unit).openings = 0)),
     ("h ≤ k, next", decide (next.h ≤ next.k)),
     ("sizes", sizedB a),
     ("later stages fit", fitAllB next (nx' :: rest')),
     ("room", decide ((sgOf a).h + 2 * (sgOf a).g + 1 ≤ (sgOf a).Z.l)),
     ("a mask code's length", decide ((K.mask.getD Z.i.2 default).ell = a.Z.l)),
     ("switchPlanB", switchPlanB p K 0 a next Z.n),
     ("planFromOk at the renumbered place",
       planFromOk (renumP p) (nx' :: rest') (0 + 1) next ((laidS p).drop (a.k + 3)) K),
     ("sorts", decide (((laidS p).drop (a.k + 3)).map asked = bodyItems next (nx' :: rest')))]
  | _ => [("three stages or more", false)]

def planOB (p : P12) (K : Codes) (nT : ℕ) : Bool := (planOL p K nT).all (·.2)

def planONo (p : P12) (K : Codes) (nT : ℕ) : List String :=
  ((planOL p K nT).filter (!·.2)).map (·.1)

/-- For the controls alone: the renumbering by n in the place of 1. -/
def renumByP (n : ℕ) (p : P12) : P12 :=
  { p with nums := { p.nums with ownMask := false, free := p.nums.free + n } }

/-- For the controls alone: the names of the later stages' clauses that refuse at q, at the rounds
of p. -/
def laterNo (q p : P12) (K : Codes) : List String :=
  match p.nums.stages with
  | a :: next :: nx' :: rest' => planFromNo q (nx' :: rest') 1 next ((laidS p).drop (a.k + 3)) K
  | _ => ["fewer than three stages"]

theorem renumByP_one (p : P12) : renumByP 1 p = renumP p := rfl

/-! ## 1 What the test gives -/

/-- **The library's public facts on the later stages, at the renumbered place, at the rounds of
p.** -/
theorem planAll_of_OB (p : P12) (K : Codes) (nT : ℕ) (a next nx' : Fmt.M1.Stage)
    (rest' : List Fmt.M1.Stage) (hst : p.nums.stages = a :: next :: nx' :: rest')
    (h : planOB p K nT = true) :
    PlanAll (renumP p) (nx' :: rest') (0 + 1) next ((laidS p).drop (a.k + 3)) K := by
  unfold planOB planOL at h
  split at h
  · rename_i a₁ n₁ x₁ r₁ hst₁
    have e := hst₁.symm.trans hst
    simp only [List.cons.injEq] at e
    obtain ⟨rfl, rfl, rfl, rfl⟩ := e
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, p21, p22⟩ := h
    exact ⟨planFrom_of_ok (renumP p) _ _ _ _ _ p21, p22⟩
  · simp at h

theorem switchPlan_renum {p : P12} {K : Codes} {j : ℕ} {cur next : Fmt.M1.Stage} {n : IoppStage}
    (h : SwitchPlan p K j cur next n) : SwitchPlan (renumP p) K j cur next n :=
  ⟨h.early, h.one, h.stageN, h.idx, h.hkN, h.fits, h.codeN, h.zkN, h.nk, h.nh, h.lengths, h.bounds,
    h.trees, h.oneTree⟩

/-- Where a further stage follows the next one. -/
theorem firstSwitchPlan_renum {p : P12} {K : Codes} {j : ℕ} {cur next : Fmt.M1.Stage}
    {n : IoppStage} (x : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (h : FirstSwitchPlan p K j cur next n (x :: rest)) :
    FirstSwitchPlan (renumP p) K j cur next n (x :: rest) :=
  switchPlan_renum (p := p) h

/-! ## 2 At the library's written places, by an evaluation in Lean's kernel -/

set_option maxRecDepth 100000 in
theorem planOB_O_full : planOB piOFull codesFull 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem planOB_O_small : planOB piO codesSmall 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem planOB_KO_full : planOB piKOFull codesKeyFull 3 = true := by decide +kernel

/-! ## 3 The test can say no -/

set_option maxRecDepth 100000 in
theorem planONo_O_two : planONo piOFull codesFull 2 = ["oS"] := by decide +kernel

set_option maxRecDepth 100000 in
theorem planONo_O_four : planONo piOFull codesFull 4 = ["oS"] := by decide +kernel

set_option maxRecDepth 100000 in
theorem planONo_U_full : planONo piUFull codesFull 2 =
    ["foldCutOwn", "planFromOk at the renumbered place"] := by decide +kernel

set_option maxRecDepth 100000 in
theorem planONo_W_full : planONo piWFull codesFull 3 =
    ["foldCutOwn", "planFromOk at the renumbered place"] := by decide +kernel

set_option maxRecDepth 100000 in
theorem planONo_L_full : planONo piLFull codesFull 1 =
    ["foldCutOwn", "planFromOk at the renumbered place"] := by decide +kernel

set_option maxRecDepth 100000 in
theorem laterNo_O_zero : laterNo (renumByP 0 piOFull) piOFull codesFull =
    ["1:Dealt", "2:Dealt", "3:Dealt"] := by decide +kernel

set_option maxRecDepth 100000 in
theorem laterNo_O_one : laterNo (renumByP 1 piOFull) piOFull codesFull = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem laterNo_O_two : laterNo (renumByP 2 piOFull) piOFull codesFull =
    ["1:Dealt", "2:Dealt", "3:Dealt"] := by decide +kernel

set_option maxRecDepth 100000 in
theorem laterNo_O_self : laterNo piOFull piOFull codesFull =
    ["1:ownMask", "2:label", "2:ownMask", "3:ownMask"] := by decide +kernel

end ProofFile.Honest.K12.Own

#print axioms ProofFile.Honest.K12.Own.planOL
#print axioms ProofFile.Honest.K12.Own.planOB
#print axioms ProofFile.Honest.K12.Own.planONo
#print axioms ProofFile.Honest.K12.Own.renumByP
#print axioms ProofFile.Honest.K12.Own.laterNo
#print axioms ProofFile.Honest.K12.Own.renumByP_one
#print axioms ProofFile.Honest.K12.Own.planAll_of_OB
#print axioms ProofFile.Honest.K12.Own.switchPlan_renum
#print axioms ProofFile.Honest.K12.Own.firstSwitchPlan_renum
#print axioms ProofFile.Honest.K12.Own.planOB_O_full
#print axioms ProofFile.Honest.K12.Own.planOB_O_small
#print axioms ProofFile.Honest.K12.Own.planOB_KO_full
#print axioms ProofFile.Honest.K12.Own.planONo_O_two
#print axioms ProofFile.Honest.K12.Own.planONo_O_four
#print axioms ProofFile.Honest.K12.Own.planONo_U_full
#print axioms ProofFile.Honest.K12.Own.planONo_W_full
#print axioms ProofFile.Honest.K12.Own.planONo_L_full
#print axioms ProofFile.Honest.K12.Own.laterNo_O_zero
#print axioms ProofFile.Honest.K12.Own.laterNo_O_one
#print axioms ProofFile.Honest.K12.Own.laterNo_O_two
#print axioms ProofFile.Honest.K12.Own.laterNo_O_self
