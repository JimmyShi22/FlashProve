-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ManyFitsAt.lean

What it proves. The first three clauses of DataFront (ShapeAll.lean: cols, state, trees) at the job
of the proximity test on G_u of the shared chain (jobAtU, JobShared.lean, as a TestJob), with the
state function doorUF (DoorsByShape.lean), at the job's own rows and columns (plainMany, colsMany,
ManyFits.lean) and at the same plain data at which FrontAsks holds: at every input, whatever
precedes the test, and all random values. At the small made-up chain P3 (SharedSmall.lean), and
under the head P5J.AtMg at the proof file's shared chain.

Names.
  many_of_S   where the test on the thin shape (manyFitsS) is true, manyFitsB is true at the shape
      of the plain data that the library's function makes.
  dataThree_of_front   so the three clauses, at FrontAsks' plain data.
  manyFitsS_alike, depthOf_alike   manyFitsS and the trees' depths read of the test's parameters no
      more than Alike (FrontAtHead.lean) holds.
  treesU, treesU_alike   jobAtU's list of trees.
  many_small, dataThree_small   at P3: the kernel's evaluation; the theorem.
  many_real, many_at, dataThree_head   at the typed sizes; under the head.

By what. dataThree_many (ManyFitsLaw.lean); thin_batT (FrontThin.lean); gpOfS_eq
(Johnson/Desc/K12/Honest/Shape/TestDoor.lean); frontAsks_small, five_small (FrontAtSmall.lean);
shape_small_UF (DoorsAtSmall.lean); frontAsks_head, five_head, alike_head_U (FrontAtHead.lean);
shape_head_UF (MarksAtHead.lean); shapes_plan_U (NearAtHead.lean).

Limits.
- DataFront's fourth clause (allSay: the rows that the test takes in say true things of the job's
  words) is not touched: it is no fact at every input and whatever precedes the test.
- The three clauses say that the job's own state, columns and trees are laid as the verifier's plain
  data ask. They do not say that the columns are those beneath the roots that the verifier was sent.
- True of doorUF's fall-back too: no statement that the state on entry is the verifier's.
- The test on G_u alone.
- It stands over files that are not in the library yet, as MarksBehind.lean does.
- Nothing on completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.ManyFitsLaw
import Johnson.Desc.ProofFile.Honest.K12.AsksAtHead
import Johnson.Desc.ProofFile.Honest.K12.FrontAtSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (Codes OracleNotice TableKey Group)
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (P12 T12)
open Johnson.G (codesFull2)
open Desc.K14 (P14 St blocks)
open H2K.Member (piUFull)
open H2K.First (Plain gpOf logAt)
open Johnson.Prover.Link (batT)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12 (TestJob TestCoins FrontAsks frontFiveB stA ColsAt StateAt groupTrees)
open ProofFile.Honest.K12.Thin (thin_batT)
open ProofFile.Honest.Sh (testSh TestSh ThinSh thinSh batThin gpOfS gpOfS_eq plainSh claimsB)

variable {W X : Type}
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-! ## 1 From the thin shape to the plain data -/

theorem many_of_S (p : P12) (ms : List MemShape) (trees : List (ℕ × List Piece)) (t : T12)
    (hp : t.pass = .nothing) (he : p.early = true)
    (h : manyFitsS p ms trees (thinSh t) = true) (G : Group) (hG : t.st.groups[t.g]? = some G)
    (Dp : Plain)
    (hD : gpOf p (batT t G {}) (stA p) (OnBytes.Means.layoutOf t.st G) = some Dp) :
    manyFitsB (stA p) ms trees (plainSh Dp) = true := by
  unfold manyFitsS at h
  split at h
  · rename_i aB hB
    have eT := thin_batT p t G {} aB hp he hG hB
    split at h
    · rename_i L hL
      have eL : L = OnBytes.Means.layoutOf t.st G := by
        have k : (thinSh (batT t G {})).pass = .claim (OnBytes.Means.layoutOf t.st G) := rfl
        rw [eT, hL] at k
        injection k
      subst eL
      have k := gpOfS_eq p (batT t G {}) (stA p) (OnBytes.Means.layoutOf t.st G)
      rw [eT, hD] at k
      rw [k] at h
      exact h
    · cases h
  · cases h

/-- **The three clauses at FrontAsks' plain data**, where the five clauses on the shape and the test
manyFitsS hold at the shape of the state on entry. -/
theorem dataThree_of_front (A : ManyJob W X) (w : W) (fr : Front X) (K : Codes) (Dp : Plain)
    (he : A.p.early = true) (h5 : frontFiveB A.p K (testSh (A.rec₀ w fr)) = true)
    (S : FrontAsks A.toRun.toTest w fr K Dp)
    (hS : manyFitsS A.p (A.mems.map (·.shape)) A.trees
      (ProofFile.Honest.Sh.thinOf (testSh (A.rec₀ w fr))) = true) (C : TestCoins) :
    ColsAt A.s₀ Dp (colsMany A Dp.ts w fr C) (plainMany A w fr C) ∧
      StateAt A.s₀ Dp (A.toRun.toTest.first w fr C) (plainMany A w fr C) ∧
      A.toRun.toTest.trees₀ w fr C.mem (A.toRun.toTest.first w fr C) =
        groupTrees Dp.ts (logAt Dp.book) (colsMany A Dp.ts w fr C) := by
  unfold frontFiveB at h5
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h5
  obtain ⟨⟨⟨⟨-, -⟩, h4⟩, -⟩, -⟩ := h5
  rw [ProofFile.Honest.Sh.thinOf_eq] at hS
  have hp : (A.rec₀ w fr).pass = .nothing := by
    have h4' : (match ProofFile.Honest.Sh.passSh (A.rec₀ w fr).pass with
      | .nothing => true
      | _ => false) = true := h4
    cases hq : (A.rec₀ w fr).pass with
    | nothing => rfl
    | claim _ _ => rw [hq] at h4'; cases h4'
    | single _ _ => rw [hq] at h4'; cases h4'
    | switched _ _ _ => rw [hq] at h4'; cases h4'
  have hc : claimsB (A.rec₀ w fr) = true := S.claims
  unfold claimsB at hc
  cases hG : (A.rec₀ w fr).st.groups[(A.rec₀ w fr).g]? with
  | none =>
    rw [hG] at hc
    cases hc
  | some G =>
    exact dataThree_many A Dp (many_of_S A.p _ _ _ hp he hS G hG Dp (S.plain G hG).1) w fr C

/-! ## 2 What the test reads of the parameters -/

theorem manyFitsS_alike {p q : P12} (A : Alike p q) (ms : List MemShape)
    (trees : List (ℕ × List Piece)) (a : ThinSh) :
    manyFitsS p ms trees a = manyFitsS q ms trees a := by
  unfold manyFitsS
  simp only [batThin_alike A, gpOfS_alike A, stA_alike A]

theorem depthOf_alike {p q : P12} (A : Alike p q) (i : ℕ) : depthOf p i = depthOf q i := by
  unfold depthOf
  rw [A.nums]

/-- jobAtU's list of trees. -/
def treesU (p : P12) : List (ℕ × List Piece) :=
  [(depthOf p 0, [.main 0, .fresh]), (depthOf p 1, [.mask 1])]

theorem treesU_alike {p q : P12} (A : Alike p q) : treesU p = treesU q := by
  unfold treesU
  rw [depthOf_alike A, depthOf_alike A]

/-! ## 3 Under the head -/

theorem many_real : (realSized.all fun q =>
    manyFitsS piUFull ((emptyU q.2 q.1.shape).mems.map (·.shape)) (treesU piUFull)
      (ProofFile.Honest.Sh.thinOf
        (Desc.K14.Shape.doorU (endOf (planOf q.2 q.1.shape).P (sentOf q.1.shape))))) = true := by
  decide +kernel

theorem many_at {x : OnBytes.Params.LinSized} (hx : realSized = some (x, codesFull2)) :
    manyFitsS piUFull ((emptyU codesFull2 x.shape).mems.map (·.shape)) (treesU piUFull)
      (ProofFile.Honest.Sh.thinOf
        (Desc.K14.Shape.doorU (endOf (planOf codesFull2 x.shape).P (sentOf x.shape)))) = true := by
  have k := many_real
  rw [hx] at k
  simpa only [Option.all_some] using k

/-- **The first three clauses of DataFront at jobAtU with doorUF, under the head**, beside FrontAsks
at the same plain data. bs: the plan's eight blocks (hb; there are such: blocks_head,
NearAtHead.lean). -/
theorem dataThree_head (h : P5J.AtMg o Z D r Zp Np cF) (bs : List (Block St Unit))
    (hb : blocks (K1.qAt Zp Np) = some bs) (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (weights : W → Weights) (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E))
    (w : W) (fr : Front X) :
    let A := jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U
      (doorUF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs key cols) weights rand u?
    ∃ Dp : Plain, FrontAsks A.toRun.toTest w fr codesFull2 Dp ∧ ∀ C : TestCoins,
      ColsAt A.s₀ Dp (colsMany A Dp.ts w fr C) (plainMany A w fr C) ∧
        StateAt A.s₀ Dp (A.toRun.toTest.first w fr C) (plainMany A w fr C) ∧
        A.toRun.toTest.trees₀ w fr C.mem (A.toRun.toTest.first w fr C) =
          groupTrees Dp.ts (logAt Dp.book) (colsMany A Dp.ts w fr C) := by
  intro A
  obtain ⟨Dp, S⟩ := frontAsks_head h bs hb A.toRun.toTest rfl key cols rfl w fr
  have hN : testSh (A.rec₀ w fr) =
      Desc.K14.Shape.doorU (endOf (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)) :=
    shape_head_UF h bs hb key cols w fr
  have he : A.p.early = true := H2K.JointK.early_of_planOk _ (planOk_head_U h)
  have h5 : frontFiveB A.p codesFull2 (testSh (A.rec₀ w fr)) = true := by
    rw [hN]
    exact five_head h
  have hS : manyFitsS A.p (A.mems.map (·.shape)) A.trees
      (ProofFile.Honest.Sh.thinOf (testSh (A.rec₀ w fr))) = true := by
    obtain ⟨x, hx, Wr⟩ := written_at_head h
    have e1 : A.mems.map (·.shape) = (emptyU (K1.qAt Zp Np).codes (K1.qAt Zp Np).S).mems.map
        (·.shape) := shapes_plan_U (K1.qAt Zp Np) 0 _ _ weights rand u?
    have e2 : A.trees = treesU (fourOf Np).U := rfl
    have eC : (K1.qAt Zp Np).codes = codesFull2 := by rw [qAt_written Wr Np]
    have eS : (K1.qAt Zp Np).S = x.shape := by rw [qAt_written Wr Np]
    rw [hN, e1, e2, eC, eS]
    show manyFitsS (fourOf Np).U _ _ _ = true
    rw [manyFitsS_alike (alike_head_U h), treesU_alike (alike_head_U h), qAt_written Wr Np,
      endOf_plan _ _ _ _ _ (Desc.K14.beforePointOf Np) []]
    exact many_at hx
  exact ⟨Dp, S, fun C => dataThree_of_front A w fr codesFull2 Dp he h5 S hS C⟩

end ProofFile.Honest.K12.Light

namespace ProofFile.Honest.K12.Light.SharedSmall
open OnBytes (TableKey)
open VerifiableInference.Desc (OpenedColumn)
open H2K.First (Plain logAt)
open ProofFile.Honest.K12 (TestCoins FrontAsks ColsAt StateAt groupTrees)
open ProofFile.Honest.Sh (testSh)

variable {W X : Type}

/-! ## 4 At P3 -/

theorem many_small : manyFitsS p (shapesAtU ⟨P3, 0⟩ p) (treesU p)
    (ProofFile.Honest.Sh.thinOf (Desc.K14.Shape.doorU (endOf P3 sentU3))) = true := by
  decide +kernel

/-- **The first three clauses of DataFront at jobAtU with doorUF, at P3**, beside FrontAsks at the
same plain data. -/
theorem dataThree_small (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (weights : W → Weights) (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E))
    (w : W) (fr : Front X) :
    let A := jobAtU ⟨P3, 0⟩ p (doorUF P3 sentU3 bs3 key cols) weights rand u?
    ∃ Dp : Plain, FrontAsks A.toRun.toTest w fr P3.codes Dp ∧ ∀ C : TestCoins,
      ColsAt A.s₀ Dp (colsMany A Dp.ts w fr C) (plainMany A w fr C) ∧
        StateAt A.s₀ Dp (A.toRun.toTest.first w fr C) (plainMany A w fr C) ∧
        A.toRun.toTest.trees₀ w fr C.mem (A.toRun.toTest.first w fr C) =
          groupTrees Dp.ts (logAt Dp.book) (colsMany A Dp.ts w fr C) := by
  intro A
  obtain ⟨Dp, S⟩ := frontAsks_small A.toRun.toTest rfl key cols rfl w fr
  have hN : testSh (A.rec₀ w fr) = Desc.K14.Shape.doorU (endOf P3 sentU3) :=
    shape_small_UF key cols w fr
  refine ⟨Dp, S, fun C => dataThree_of_front A w fr P3.codes Dp early_p ?_ S ?_ C⟩
  · rw [hN]
    exact five_small
  · rw [hN, shapes_atU]
    exact many_small

-- the test can fail: at the trees in the other order; at shapes with one main row more; at a tree
-- whose two pieces are swapped
#guard !manyFitsS p (shapesAtU ⟨P3, 0⟩ p) (treesU p).reverse
  (ProofFile.Honest.Sh.thinOf (Desc.K14.Shape.doorU (endOf P3 sentU3)))
#guard !manyFitsS p ((shapesAtU ⟨P3, 0⟩ p).map fun m => { m with mainRows := m.mainRows + 1 })
  (treesU p) (ProofFile.Honest.Sh.thinOf (Desc.K14.Shape.doorU (endOf P3 sentU3)))
#guard !manyFitsS p (shapesAtU ⟨P3, 0⟩ p)
  [(depthOf p 0, [.fresh, .main 0]), (depthOf p 1, [.mask 1])]
  (ProofFile.Honest.Sh.thinOf (Desc.K14.Shape.doorU (endOf P3 sentU3)))

end ProofFile.Honest.K12.Light.SharedSmall

#print axioms ProofFile.Honest.K12.Light.many_of_S
#print axioms ProofFile.Honest.K12.Light.dataThree_of_front
#print axioms ProofFile.Honest.K12.Light.manyFitsS_alike
#print axioms ProofFile.Honest.K12.Light.depthOf_alike
#print axioms ProofFile.Honest.K12.Light.treesU
#print axioms ProofFile.Honest.K12.Light.treesU_alike
#print axioms ProofFile.Honest.K12.Light.many_real
#print axioms ProofFile.Honest.K12.Light.many_at
#print axioms ProofFile.Honest.K12.Light.dataThree_head
#print axioms ProofFile.Honest.K12.Light.SharedSmall.many_small
#print axioms ProofFile.Honest.K12.Light.SharedSmall.dataThree_small
