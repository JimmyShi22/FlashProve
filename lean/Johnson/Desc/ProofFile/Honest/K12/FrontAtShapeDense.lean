-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FrontAtShapeDense.lean: the "dense" twins of `frontAsks_of_five`,
`frontAsks_all` (FrontAtShape.lean in this folder).

What it is. The old statements and structures hold, take or give `FrontAsks` (ShapeAll.lean) or
`ShapeAsks` (PlanB.lean), each with a field `plainRows`, which asks that no open row and no sample
row of the whole statement on entry has a written-out variable (`stPlainB`,
Johnson/Desc/Ground/Shape/Marks.lean). The twins have `FrontAsksD` (ShapeAllDense.lean) and
`ShapeAsksD` (PlanBDense.lean) in their places, whose field `denseRows` asks `DenseRow` of the rows
taken in at the group under test. `PlainRow` (OnBytes/Slice/BlkPlain.lean) says that no tensor of a
row has a written-out variable. `DenseRow` (OnBytes/Slice/BlkProxDense.lean) allows such variables
where every tensor is in order and its slice lies inside its vector; it follows from `PlainRow`
(`denseRow_of_plain`). The rows meant are those that the proximity test takes in at the group under
test (`runRows`, OnBytes/Slice/BlkBegin.lean). Apart from that and from the twins' names, each
statement is the old one, letter for letter. The files named here lie in
Johnson/Desc/ProofFile/Honest/K12/.

Why. Without these twins `ShapeAsksD` could be had from the old `ShapeAsks` alone, and so from the
old mark. These are the statements that make a `ShapeAsks` from tests on the front, and the second
member's condition at a play and at a run.

Main names. `frontAsksD_of_five`, `frontAsksD_all`.

By what. Each twin's proof is the old proof with the twins' names in it.

Limits.
- These statements stand over Johnson/Prover/Link/FormFirst.lean, whose structure
  `TestFront` has the field `dense`, as all the twins do
  (Johnson/Desc/K12/Honest/Shape/TestDoorDense.lean says why).
- They do not reach the first chain's proximity test yet. The library proves the hypothesis on the
  rows there, of the verifier's state (`taken_dense_entered`,
  Johnson/AtFull/Shape/TakenRowsDense.lean). These files do not show the other hypotheses there: the
  tests on the front (`frontFiveB`), `stTidyB` and `claimsB` on entry, `planB`, and the hypotheses
  on the prover's data. `onFreeTD_at_run` (OnFreeTAtRunDense.lean) speaks of the shared chain, on
  which that test does not lie.
- The state on entry is the job's own `rec₀`. It is not shown to be the verifier's.
- Without a twin: `sorts_of_coreB` (SortsMember.lean), which makes a `ShapeAsks` from the test
  `coreB`, whose list has the clause `stPlainB`; `frontAsks_of_shape` (OneToAll.lean, not in the
  library), which no statement on the way to `OnFreeTD` calls; the forms without trees
  (`OnPlan`, `OnFree`, `AtEntry` and what is stated of them); the statements that conclude
  `ShapeAsks`, `FrontAsks` or `OnFreeT` at the shared chain's first test or at a small example:
  there the new conclusions follow from the old by `shapeAsksD_of`, `frontAsksD_of`, `onFreeTD_of`.
- Only the case in which the fresh table has come earlier is served, as in the old statements.
- Nothing here is a statement on completeness, on soundness or on what a proof hides.
-/
import Johnson.Desc.ProofFile.Honest.K12.FrontAtShape
import Johnson.Desc.ProofFile.Honest.K12.ShapeAllDense

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ProofFile.Honest.K12
open OnBytes.Slice.ProxRun (DenseRow denseRow_of_plain)
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.JointK H2K.First
open Johnson.Prover.Link
open ProofFile.Honest.K12.Thin (thin_batT frontPubB frontPub_of_B)
open ProofFile.Honest.Sh (ThinSh thinSh batThin PlainS plainSh gpOfS gpOfS_eq gpLS gpLS_eq TestSh testSh
  thinOf thinOf_eq claimsB)
variable {W X : Type}

/-- The twin of `frontAsks_of_five` (FrontAtShape.lean): the hypothesis on the rows is the field
`denseRows` as it stands. -/
theorem frontAsksD_of_five (J : TestJob W X) (w : W) (fr : Front X) (K : Codes)
    (he : J.p.early = true) (h : frontFiveB J.p K (testSh (J.rec₀ w fr)) = true)
    (ht : stTidyB (J.rec₀ w fr).st = true)
        (hpl : ∀ G, (J.rec₀ w fr).st.groups[(J.rec₀ w fr).g]? = some G →
      ∀ r ∈ (runRows (J.rec₀ w fr).st G).toList, DenseRow r)
    (hc : claimsB (J.rec₀ w fr) = true) : ∃ Dp : Plain, FrontAsksD J w fr K Dp := by
  unfold frontFiveB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  rw [thinOf_eq] at h5 h6
  have hp : (J.rec₀ w fr).pass = .nothing := by
    have h4' : (match ProofFile.Honest.Sh.passSh (J.rec₀ w fr).pass with
      | .nothing => true
      | _ => false) = true := h4
    cases hq : (J.rec₀ w fr).pass with
    | nothing => rfl
    | claim _ _ => rw [hq] at h4'; cases h4'
    | single _ _ => rw [hq] at h4'; cases h4'
    | switched _ _ _ => rw [hq] at h4'; cases h4'
  obtain ⟨Dp, hD⟩ := frontPlain₀_of_B J.p _ hp he h5
  exact ⟨Dp, ⟨h1, h2, h3, ht, hpl, hc, hD,
    fun G id hG hm => frontPub_of_B J.p _ hp he h6 G id hG hm⟩⟩

/-- The twin of `frontAsks_all` (FrontAtShape.lean): the middle one of the three hypotheses on the
state is the field `denseRows` as it stands. -/
theorem frontAsksD_all (J : TestJob W X) (K : Codes) (N : TestSh) (he : J.p.early = true)
    (hN : ∀ w fr, testSh (J.rec₀ w fr) = N) (h : frontFiveB J.p K N = true)
    (h3 : ∀ w fr, stTidyB (J.rec₀ w fr).st = true ∧ (∀ G, (J.rec₀ w fr).st.groups[(J.rec₀ w fr).g]?
        = some G →
      ∀ r ∈ (runRows (J.rec₀ w fr).st G).toList, DenseRow r) ∧
      claimsB (J.rec₀ w fr) = true) (w : W) (fr : Front X) :
    ∃ Dp : Plain, FrontAsksD J w fr K Dp :=
  frontAsksD_of_five J w fr K he (by rw [hN]; exact h) (h3 w fr).1 (h3 w fr).2.1 (h3 w fr).2.2

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.frontAsksD_of_five
#print axioms ProofFile.Honest.K12.frontAsksD_all
