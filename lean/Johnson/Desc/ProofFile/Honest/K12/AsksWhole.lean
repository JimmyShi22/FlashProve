-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AsksWhole.lean

What it proves. Under the head P5J.AtMg, at the job of the proximity test on G_u of the proof file's
shared chain (jobAtU, JobShared.lean, as a TestJob) with the state function doorUF
(DoorsByShape.lean): the clause asks of the condition at the second part's entry (OnFreeT,
Sim/TreesExact.lean), both halves, at the table of codes codesFull2 and at a list os of two entries,
follows from two things: that condition's own clause heardFit, and one sentence on values (SaysAt):
the rows that the test takes in say true things of the words that the job's own rows make. K and os
are arguments of OnFreeT: that they are these two at this job is not shown here.

What it is, in part. dataAsks_of_one is a second text of dataAsks_of_front (ShapeAll.lean): the same
statement with FormAsks' first clause in the place of the whole FormAsks, and the same proof to the
sign but for the one place that took that clause out of FormAsks. Why: as in ShapeOfTwo.lean.

Names.
  dataAsks_of_one   DataAsks from planB, FrontAsks, the batching's round's form, and DataFront.
  SaysAt   DataFront's fourth clause at a ManyJob's job and the job's own rows.
  asks_head   at every input, whatever precedes the test, all coins and every list of challenges
      that fits the declared rounds up to the end of the first fold.
  asks_heard   at the input, the front, the coins and the challenges that OnFreeT names; at
      codesFull2 for its K and 2 for the length of its os.

By what. dataThree_head (ManyFitsAt.lean); ts_of_front, ts_head, planB_head, formPubB_head
(AsksAtHead.lean); five_head (FrontAtHead.lean); shape_head_UF (MarksAtHead.lean);
shapeAsks_of_draws, two_of_draws (ShapeOfTwo.lean); formPub_of_B (FormPubAt.lean); heardIn_byNo
(AsksAtHead.lean); planOk_head_U (NearAtHead.lean).

Limits.
- SaysAt is a premise. What it is worth hangs on the state on entry. Where doorUF's fold returns,
  the rows are the verifier's, and SaysAt is a sentence on the prover's values; nothing here shows
  it there. Where the fold fails, the state is the fall-back fallU, whose rows have no summand and
  the right side 0: there SaysAt holds for nothing, at every input and all random values
  (saysAt_fails, SaysAtFall.lean). So both premises of asks_head can be had without anything
  honest, and a statement that rests on them says nothing on a run unless the fold is shown to
  return.
- True of doorUF's fall-back too: no statement that the state on entry is the verifier's.
- The test on G_u alone; the case in which the first fold's mask has come.
- The other clauses of OnFreeT are not touched.
- It stands over files that are not in the library yet, as MarksBehind.lean does.
- Nothing on completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.ManyFitsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Sh (TermAsks SwitchPub claimsB testSh readPubB singleSh switchPub_of runRows_plain
  switchPubB SingleSh door_facts batT_codes rounds_split gpLS_eq)

variable {W X : Type}

/-- **DataAsks at the challenges, from the state in front and one fact on the form of what the
batching's round shows.** -/
theorem dataAsks_of_one (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (K : Codes) (Dp : Plain) (c : ℕ → ℕ → List UInt64) (R : PlainRows)
    (hP : planB J.p K Dp.ts.length = true) (S : FrontAsks J w fr K Dp)
    (f1 : roundsFit (((laidOf J.p).take 1).map (·.1)) [⟨[], D 0⟩] = true)
    (Dt : DataFront J w fr C Dp c R) : DataAsks J w fr C D Dp c R := by
  refine ⟨Dt.cols, Dt.state, Dt.trees, fun row' L' h G' hG' => ?_⟩
  unfold planB planL at hP
  split at hP
  · rename_i a next nx' rest' hst
    have hA : stA J.p = a := by
      unfold stA
      rw [hst]
      rfl
    have hN : stN J.p = next := by
      unfold stN
      rw [hst]
      rfl
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq] at hP
    obtain ⟨-, -, -, p4, -⟩ := hP
    obtain ⟨id, hm⟩ := Option.isSome_iff_exists.1 S.came
    have s2 := S.door
    simp only [hA, hN] at s2
    obtain ⟨G, row, x, H, hr, eB, -⟩ :=
      door_facts s2 hm S.tidy (fun G hG => runRows_plain S.plainRows hG) S.claims p4 f1
    have eR : J.recB w fr (D 0) = batT (J.rec₀ w fr) G row := (recB_eq J w fr (D 0)).trans eB
    obtain rfl : G = G' := Option.some.inj (H.group.symm.trans hG')
    rw [eR] at h ⊢
    have h' : Passing.claim row (layoutOf (J.rec₀ w fr).st G) = .claim row' L' := h
    injection h' with h1 h2
    subst h1 h2
    exact Dt.allSay G hG'
  · simp at hP

end ProofFile.Honest.K12

namespace ProofFile.Honest.K12.Light
open OnBytes (Codes TableKey)
open OnBytes.Slice (rdE)
open OnBytes.Means (AllSay layoutOf)
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc (K1.qAt)
open Johnson.G (codesFull2)
open Desc.K14 (St blocks)
open H2K.JointK (laidOf)
open H2K.First (Plain)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12 (TestCoins PlainRows FrontAsks ShapeAsks DataAsks DataFront frontFiveB planB
  formPubB formPub_of_B byNo shapeAsks_of_draws two_of_draws dataAsks_of_one)
open ProofFile.Honest.Sh (testSh)

variable {W X : Type}
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **The sentence on values**: the rows that the test takes in say true things of the words that
the job's own rows make. -/
def SaysAt (A : ManyJob W X) (w : W) (fr : Front X) (C : TestCoins) : Prop :=
  ∀ G, (A.rec₀ w fr).st.groups[(A.rec₀ w fr).g]? = some G →
    AllSay rdE (OnBytes.Slice.begun (A.rec₀ w fr).st (A.rec₀ w fr).g G)
      (OnBytes.Slice.runRows (A.rec₀ w fr).st G).toList
      (ProofFile.Honest.K12.wordsAt (OnBytes.Slice.begun (A.rec₀ w fr).st (A.rec₀ w fr).g G)
        (layoutOf (A.rec₀ w fr).st G) (plainMany A w fr C))

/-- **ShapeAsks and DataAsks at one set of plain data with two trees, under the head.** bs: the
plan's eight blocks (hb; there are such: blocks_head, NearAtHead.lean). True of the fall-back too,
where SaysAt is empty (SaysAtFall.lean): no statement that the state on entry is the verifier's. -/
theorem asks_head (h : P5J.AtMg o Z D r Zp Np cF) (bs : List (Block St Unit))
    (hb : blocks (K1.qAt Zp Np) = some bs) (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (weights : W → Weights) (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E))
    (w : W) (fr : Front X) (C : TestCoins) (ds : List Fmt.Drawn) :
    let A := jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U
      (doorUF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs key cols) weights rand u?
    drawsFit (((laidOf A.p).take (firstLen A.p.nums.stages)).map (·.1)) ds = true →
    SaysAt A w fr C →
    ∃ (Dp : Plain) (cc : ℕ → ℕ → List UInt64) (R : PlainRows), Dp.ts.length = 2 ∧
      ShapeAsks A.toRun.toTest w fr C (byNo ds) codesFull2 Dp ∧
      DataAsks A.toRun.toTest w fr C (byNo ds) Dp cc R := by
  intro A hd hs
  obtain ⟨Dp, S, T⟩ := dataThree_head h bs hb key cols weights rand u? w fr
  obtain ⟨t1, t2, t3⟩ := T C
  have he : A.p.early = true := H2K.JointK.early_of_planOk _ (planOk_head_U h)
  have hN : testSh (A.rec₀ w fr) =
      Desc.K14.Shape.doorU (endOf (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)) :=
    shape_head_UF h bs hb key cols w fr
  have h5 : frontFiveB A.p codesFull2 (testSh (A.rec₀ w fr)) = true := by
    rw [hN]
    exact five_head h
  have hts : Dp.ts.length = 2 := by
    rw [ts_of_front A.toRun.toTest w fr codesFull2 Dp he h5 S]
    show tsLenOf (fourOf Np).U (ProofFile.Honest.Sh.thinOf (testSh (A.rec₀ w fr))) = 2
    rw [hN]
    exact ts_head h
  have hB : formPubB A.p = true := formPubB_head h
  have hP : planB A.p codesFull2 Dp.ts.length = true := by
    rw [hts]
    exact planB_head h
  have Dt : DataFront A.toRun.toTest w fr C Dp (colsMany A Dp.ts w fr C) (plainMany A w fr C) :=
    ⟨t1, t2, t3, hs⟩
  refine ⟨Dp, colsMany A Dp.ts w fr C, plainMany A w fr C, hts, ?_⟩
  cases hst : A.p.nums.stages with
  | nil =>
    unfold formPubB at hB
    rw [hst] at hB
    cases hB
  | cons a l1 =>
    cases l1 with
    | nil =>
      unfold formPubB at hB
      rw [hst] at hB
      cases hB
    | cons next rest =>
      rw [hst] at hd
      have Pb := formPub_of_B A.p a next rest hst hB
      exact ⟨shapeAsks_of_draws A.toRun.toTest w fr C ds codesFull2 Dp a next rest hst Pb hP S hd,
        dataAsks_of_one A.toRun.toTest w fr C (byNo ds) codesFull2 Dp _ _ hP S
          (two_of_draws A.toRun.toTest w fr C ds a next rest hst Pb hd).1 Dt⟩

/-- **Both halves of the clause asks of OnFreeT, at codesFull2 and a list of two, from its clause
heardFit and the sentence on values**, under the head. True of the fall-back too, where SaysAt is
empty (SaysAtFall.lean): no statement that the state on entry is the verifier's. -/
theorem asks_heard (h : P5J.AtMg o Z D r Zp Np cF) (bs : List (Block St Unit))
    (hb : blocks (K1.qAt Zp Np) = some bs) (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (weights : W → Weights) (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E))
    (mem : ℕ → Stretch) (m : ProofFile.Honest.Mid W X) :
    let A := jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U
      (doorUF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs key cols) weights rand u?
    let J := A.toRun.toTest
    drawsFit (((laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
      (m.st.lately (firstLen J.p.nums.stages)) = true →
    SaysAt A m.st.input (restFront J m) (carriedCoins J mem) →
    ∃ Dp cc R, Dp.ts.length = 2 ∧
      ShapeAsks J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) codesFull2 Dp ∧
      DataAsks J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) Dp cc R := by
  intro A J hd hs
  rw [heardIn_byNo]
  exact asks_head h bs hb key cols weights rand u? _ _ _ _ hd hs

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.dataAsks_of_one
#print axioms ProofFile.Honest.K12.Light.SaysAt
#print axioms ProofFile.Honest.K12.Light.asks_head
#print axioms ProofFile.Honest.K12.Light.asks_heard
