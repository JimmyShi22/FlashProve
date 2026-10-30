-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LShapeFront.lean: at the first chain's closing proximity
test, from tests on the shape of the state on entry to what is asked of the plan, the front and the
prover's data together, at one and the same plain data.

  `nothingPasses_of_door`  the door's test holds that the state passes nothing on and that the masks
                        come early
  `fitsAtL_of_front`    `FitsAtL` at the plain data of `FrontAsksD`, where the test
                        `closingFitsAtShape` (LShapeTest.lean) is true at the shape on entry
  `planAtTrees_of_fits` the plan's test at the number of the plain data's trees, from the test at 1
  `asks_of_shape`       the plan's test, `FrontAsksD` and `DataFront` at the job `jobL`

Hypotheses of `asks_of_shape`.
  hFits        the test `closingFitsAtShape` at the shape of the state on entry
  hP           the plan's test at one tree
  S            `FrontAsksD` at the plain data Dp
  hrows        the sender's text returns the rows R at the coins that the first stage reads
  hSay         the rows that the test takes in say their claims of these rows' words

Who calls it. LShapeAtHead.lean calls `planAtTrees_of_fits` alone.

Limits.
- hFits, hP, S, hrows and hSay are premises. None is shown at any state here.
- The state on entry is the job's own. It is not shown to be the verifier's.
- hSay reads the targets. At a door that has lost them it is false wherever a target is not 0: so at
  such a door the law says nothing. It is meant for the door patched with the verifier's record
  (LShapeAsks.lean).
- `claimsB` at the state on entry is a field of S.
- Nothing on completeness, on soundness or on hiding.
NOT IN FRONT OF A LAW OVER COINS: `asks_of_shape` bears this label; the rule is at its home, the
head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: hrows and hSay tie the letter R, and S
ties the letter Dp, to the coins C and to what the state on entry holds.
Terms: the head of LShapeTest.lean; Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LShapeTest
import Johnson.Desc.ProofFile.Honest.K12.ShapeAllDense

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open OnBytes (Codes TreeLay)
open VerifiableInference.Desc.K12 (P12 T12)
open H2K.First (Plain Seat1)
open ProofFile.Honest.K12 (TestJob TestCoins FrontAsksD DataFront PlainRows planB)
open ProofFile.Honest.Sh (testSh thinOf thinOf_eq claimsB doorB batOwesB passSh)

variable {W X : Type}

/-- Where the door's test is true at a state's shape, the state passes nothing on, and the masks
come early. -/
theorem nothingPasses_of_door {q : P12} {cur nxt : Fmt.M1.Stage} {cut : List Fmt.DeclaredRound}
    {i n : ℕ × ℕ} {t : T12} (h : doorB q cur nxt cut i n (testSh t) = true) :
    t.pass = .nothing ∧ q.early = true := by
  unfold doorB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, hb⟩, -⟩, -⟩ := h
  unfold batOwesB at hb
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨h1, h2⟩, -⟩, -⟩ := hb
  refine ⟨?_, h2⟩
  have h1' : (match passSh t.pass with
    | .nothing => true
    | _ => false) = true := h1
  cases hq : t.pass with
  | nothing => rfl
  | claim _ _ => rw [hq] at h1'; cases h1'
  | single _ _ => rw [hq] at h1'; cases h1'
  | switched _ _ _ => rw [hq] at h1'; cases h1'

/-- **`FitsAtL` at the plain data of `FrontAsksD`**, where the test `closingFitsAtShape` is true at
the shape of the state on entry. -/
theorem fitsAtL_of_front (J : TestJob W X) (w : W) (fr : Front X) (K : Codes) (Dp : Plain)
    (p : K2.SwitchPlace) (S : FrontAsksD J w fr K Dp)
    (hFits : closingFitsAtShape J.p p (thinOf (testSh (J.rec₀ w fr))) = true) :
    ∃ s u Ly, FitsAtL J.p p Dp s u Ly := by
  obtain ⟨hPass, hEarly⟩ := nothingPasses_of_door S.door
  rw [thinOf_eq] at hFits
  have hc : claimsB (J.rec₀ w fr) = true := S.claims
  unfold claimsB at hc
  cases hG : (J.rec₀ w fr).st.groups[(J.rec₀ w fr).g]? with
  | none =>
    rw [hG] at hc
    cases hc
  | some G =>
    exact (closingFitsTest_iff J.p p Dp).1
      (closingFitsTest_of_shape J.p p _ hPass hEarly hFits G hG Dp (S.plain G hG).1)

/-- The plan's test at the number of the plain data's trees. -/
theorem planAtTrees_of_fits {q : P12} {p : K2.SwitchPlace} {Dp : Plain} {s : Seat1} {u : ℕ}
    {Ly : TreeLay} (H : FitsAtL q p Dp s u Ly) {K : Codes} (hP : planB q K 1 = true) :
    planB q K Dp.ts.length = true := by
  rw [treeCount_of_fits H]
  exact hP

variable {W₀ Rc Xi Tr : Type}

open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb VerifiableInference.Desc
  VerifiableInference.Desc.Ground.Sh in
/-- **The plan's test, `FrontAsksD` and `DataFront` at one plain data, at the job `jobL`.** -/
theorem asks_of_shape (q : P12) (door : Local W₀ Rc Xi Tr → Front X → T12) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing) (p : K2.SwitchPlace)
    (w : Local W₀ Rc Xi Tr) (fr : Front X) (C : TestCoins) (K : Codes) (Dp : Plain)
    {R : Johnson.Prover.Send.Rows}
    (hFits : closingFitsAtShape q p (thinOf (testSh (door w fr))) = true)
    (hP : planB q K 1 = true) (S : FrontAsksD (jobL q door D readers closing p) w fr K Dp)
    (hrows : carryRows D readers closing p w (heardL fr) C.mem = .ok R)
    (hSay : ∀ G, (door w fr).st.groups[(door w fr).g]? = some G →
      AllSay rdE (begun (door w fr).st (door w fr).g G) (runRows (door w fr).st G).toList
        (ProofFile.Honest.K12.wordsAt (begun (door w fr).st (door w fr).g G)
          (layoutOf (door w fr).st G)
          (plainL R ((jobL q door D readers closing p).first w fr C)))) :
    ∃ (cc : ℕ → ℕ → List UInt64) (Rr : PlainRows),
      planB (jobL q door D readers closing p).p K Dp.ts.length = true ∧
        FrontAsksD (jobL q door D readers closing p) w fr K Dp ∧
        DataFront (jobL q door D readers closing p) w fr C Dp cc Rr := by
  obtain ⟨s, u, Ly, H⟩ := fitsAtL_of_front (jobL q door D readers closing p) w fr K Dp p S hFits
  exact ⟨_, _, planAtTrees_of_fits H hP, S,
    dataFront_L q door D readers closing p w fr C hrows H hSay⟩

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.nothingPasses_of_door
#print axioms ProofFile.Honest.K12.AtProof.fitsAtL_of_front
#print axioms ProofFile.Honest.K12.AtProof.planAtTrees_of_fits
#print axioms ProofFile.Honest.K12.AtProof.asks_of_shape
