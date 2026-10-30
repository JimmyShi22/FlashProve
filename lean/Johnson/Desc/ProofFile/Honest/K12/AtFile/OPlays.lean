-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/OPlays.lean: the frame's sentence «it plays» at the proximity test on
G_omega, member 10 of the proof file's shared thread, behind the guard, with the thread's tables and counts
as `tableShared` and `fixedShared` (TableShared.lean) lay them.

  `table_seven`, `table_test`   the table at own 7 is `ownTbl`, at own 8 to 10 `testTbl`
  `sent_seven`, `sent_test`   the rounds that send these trees, by the kernel
  `rows_heard_O`   the job's rows read the heard alone
  `old_head_O`   `RunPlays.old` at a stand at 10
  `rounds_zip_O`, `oracles_count_O`   the seated block's counts
  `FixedO`, `trees_head_O`   the new trees are the thread's tables: `trees_of_thr_ten` (K12/TreesAtTen.lean)
  `playsS_head_O`   the statement

The premises beyond `StandO` (OAccepted.lean). `FixedO`: the thread's counts are `fixedShared` at the written rounds,
43 rounds stand in front. c2: the book covers the sending of o_u.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: the thread's pair is a premise, `PlaysS` the end; `ownTbl` is a text at part 0's
  coins, and the head of K12/OwnTbl.lean binds whoever lays it.
- That a stand is reached is not said.
- A yes at a field that is some is a yes at any columns: that the prover plays off the verifier's state is
  `enters`'s, in `acceptedS_head_O`.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OAccepted
import Johnson.Desc.ProofFile.Honest.K12.AtFile.TableLines

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K14 (SendJob Ask jobU jobOmega sendPlace treesU)
open ProofFile.Honest.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (St blocks)
open Johnson.G (proofSendsFull codesFull2)
open H2K.JointK (laidOf)
open H2K.Member (piOFull)
open H2K.Pub (sgOf)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12.Light (ManyJob memOfSending jobAtOmega doorOmegaF sentOf written_at_head qAt_written nums_head_O
  planOk_head_O thin_head_O pairOf pairs_of_planOk planOf count_head_O)
open P2Law.ProofPlan (declProofFull)

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ : Type} (Q : Desc.K14.P14) (wts : W₀ → Weights) (rnd : Rc → TableRand)
  (JU JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)

/-- **The table at own 7 is the first fold's own.** -/
theorem table_seven (hu : treesU Q = 1) :
    tableShared (Bk := Bk) Q wts rnd JU JO own₀ (.own 7) = ownTbl 1 JO own₀ 43 fun _ _ _ => true := by
  show (if 7 < treesU Q then _ else if 7 < 3 then _ else if 7 < 7 then _ else if 7 = 7 then _ else _) = _
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]

/-- **The tables at own 8 to 10 are the test's.** -/
theorem table_test (hu : treesU Q = 1) (τ : ℕ) :
    tableShared (Bk := Bk) Q wts rnd JU JO own₀ (.own (7 + (τ + 1))) =
      testTbl 1 JO own₀ 43 (fun _ _ _ => true) τ := by
  show (if 7 + (τ + 1) < treesU Q then _ else if 7 + (τ + 1) < 3 then _ else
    if 7 + (τ + 1) < 7 then _ else if 7 + (τ + 1) = 7 then _ else
      testTbl 1 JO own₀ 43 (fun _ _ _ => true) (7 + (τ + 1) - 8)) = _
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have e : 7 + (τ + 1) - 8 = τ := by omega
  rw [e]

end

theorem sent_seven : ProofFile.Honest.Small.sentIn declProofFull.2.1 7 = 44 := by decide +kernel

theorem sent_eight : ProofFile.Honest.Small.sentIn declProofFull.2.1 8 = 43 + seedRound piOFull.nums.stages 0 := by
  decide +kernel

theorem sent_nine : ProofFile.Honest.Small.sentIn declProofFull.2.1 9 = 43 + seedRound piOFull.nums.stages 1 := by
  decide +kernel

theorem sent_ten : ProofFile.Honest.Small.sentIn declProofFull.2.1 10 = 43 + seedRound piOFull.nums.stages 2 := by
  decide +kernel

/-- Control: own 7 goes out in no other round. -/
theorem sent_seven_bent : ProofFile.Honest.Small.sentIn declProofFull.2.1 7 ≠ 45 := by decide +kernel

/-- A message's rows read the heard alone, where no vector is handed in. -/
theorem rows_of_none {W X : Type} (J : SendJob) (at_ : Addr) (k : ℕ) (fs : Option ℕ × Option ℕ)
    (ask : W → Ask) (w : W) (fr fr' : Front X) (c : Stretch) (he : fr.heard = fr'.heard) :
    (memOfSending J at_ k fs ask none).rows w fr c = (memOfSending J at_ k fs ask none).rows w fr' c := by
  simp only [memOfSending, he]

/-- **The job's rows read the heard alone**, at all its letters, where no vector is handed in. -/
theorem rows_heard_O {W X : Type} (A : ProofFile.Honest.K14.SendPub) (pO : P12) (door : W → Front X → T12)
    (weights : W → Weights) (rand : W → TableRand) :
    RowsOfHeard (jobAtOmega A pO door weights rand none).toRun.toTest := by
  refine rowsOfHeard_many _ fun m hm w fr fr' c he => ?_
  simp only [jobAtOmega, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> exact rows_of_none _ _ _ _ _ w fr fr' c he

/-- The flattening of a list of lists does not change its length when each entry is mapped. -/
theorem flat_map_length {α β : Type} (f : α → β) : ∀ l : List (List α),
    ((l.map (·.map f)).flatMap id).length = (l.flatMap id).length
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, List.flatMap_cons, id, List.length_append, List.length_map,
      flat_map_length f l]

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {pO : P12}

/-- The seated block's rounds and messages have as many entries as the term. -/
theorem rounds_zip_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) :
    ((proximityTestKind guardedProximityTestParts pO : Block T12 Unit).rounds.zip (proximityTestKind guardedProximityTestParts pO : Block T12 Unit).oracles).length =
      firstLen pO.nums.stages + restLen pO.nums.stages := by
  rw [zip_laid pO (planOk_head_O h hO)]
  exact count_head_O h hO

/-- The seated block declares as many trees as the place has stages. -/
theorem oracles_count_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) :
    ((proximityTestKind guardedProximityTestParts pO : Block T12 Unit).oracles.flatMap id).length = pO.nums.stages.length := by
  have e : pO.oracles.map (·.map pairOf) = piOFull.oracles.map (·.map pairOf) := by
    refine Option.some.inj ?_
    rw [← pairs_of_planOk guardedProximityTestParts pO (planOk_head_O h hO),
      ← pairs_of_planOk guardedProximityTestParts piOFull VerifiableInference.Desc.K12.Coin.At.closed_OFull.plan,
      nums_head_O h hO]
  rw [VerifiableInference.Desc.K12.k12_oracles guardedProximityTestParts pO (planOk_head_O h hO), nums_head_O h hO,
    ← flat_map_length pairOf, e, flat_map_length]
  exact count_O

section
variable {W₀ Rc X₀ S Cl V Pb : Type} {Bk : ProverCoinCounts}

/-- **`RunPlays.old` at a stand of `Thr` at 10.** -/
theorem old_head_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (T : Thread Bk S Cl V (Common W₀ Rc TableKey) X₀ Pb) (wts : W₀ → Weights) (rnd : Rc → TableRand)
    (JU JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (hb : treesTo T.bs 10 = 7) (ht : T.taken = [])
    (htb : T.table = tableShared (K1.qAt Zp Np) wts rnd JU JO own₀)
    (c2 : takesCover Bk ⟨sendPlace 2, 0⟩ (jobU ⟨K1.qAt Zp Np, 0⟩) = true)
    (c5 : takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega ⟨K1.qAt Zp Np, 0⟩) = true)
    (h3 : treesU (K1.qAt Zp Np) ≤ 3)
    {k : Coins Bk} {s : S} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env} (u : Thr T 10 k s m E) :
    ∀ d ∈ (proximityTestKind guardedProximityTestParts pO : Block T12 Unit).rounds, ∀ o ∈ d.opens,
      oldSrc E.sent o.2 = true → ∃ pt, E.tree o.2 = some pt ∧ pt.2.words = o.1.W := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  have hw := wide_O
  rw [hx] at hw
  simp only [Option.all_some] at hw
  refine old_of_hand T _ (fun d hd o ho hS => ?_) u
  rw [hb] at hS
  rw [rounds_head_O h hO] at hd
  have a2 := List.all_eq_true.1 (List.all_eq_true.1 hw d hd) o ho
  rw [hS] at a2
  cases hσ : o.2 with
  | taken a b =>
    rw [hσ] at a2
    simp at a2
  | own n =>
    rw [hσ] at a2
    obtain ⟨hn, hW⟩ : n < 3 ∧ o.1.W = tableWidth (Light.planOf codesFull2 x.shape) n := by simpa using a2
    refine ⟨?_, fun k' w' h' => ?_⟩
    · show _ ∈ T.taken ++ (List.range (treesTo T.bs 10)).map Fmt.TreeSource.own
      rw [ht, hb]
      exact List.mem_append_right _ (List.mem_map.2 ⟨n, List.mem_range.2 (by omega), rfl⟩)
    · rw [htb, words_low _ wts rnd JU JO own₀ h3 n hn k' w' h' c2 c5, hW, qAt_written Wr Np]
      rfl

/-- **What is asked of the thread's counts.** -/
structure FixedO (T : Thread Bk S Cl V (Common W₀ Rc TableKey) X₀ Pb) : Prop where
  fixed : T.fixed = fixedShared declProofFull.2.1
  ahead : T.front = 0
  rounds : roundsTo T.bs 10 = 43

end

section
variable {W₀ Rc X₀ Cl Pb : Type} {Bk : ProverCoinCounts}

set_option maxHeartbeats 1000000 in
/-- **The member's new trees are the thread's tables.** -/
theorem trees_head_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (T : Thread Bk St Cl Empty (Common W₀ Rc TableKey) X₀ Pb)
    (Said : ℕ → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (wts : W₀ → Weights) (rnd : Rc → TableRand) (JU : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (c₀ : OnBytes.Model.Verify.Chains) (bs : List (Block St Unit)) {blk : Block St Cl}
    (H : StandO Zp Np pO T Said wts rnd JU own₀ c₀ bs blk) (Fx : FixedO T)
    (a b : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest.p.nums.stages = a :: b :: rest) :
    ∀ k st m E ds y cols, Thr T 10 k st m E → drawsFit blk.rounds ds = true →
      T.Moved blk k m E ds y cols → T.Trees (T.fresh 10) k y.2 (E.add y.1) := by
  have hn := nums_head_O h hO
  have hS := H.seat
  have hall : ∀ x ∈ (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest.p.nums.stages,
      x.h ≤ x.k := by
    intro x hx
    have e : pO.nums.stages = piOFull.nums.stages := congrArg (·.stages) hn
    have hx' : x ∈ piOFull.nums.stages := e ▸ hx
    exact of_decide_eq_true (List.all_eq_true.1 hk_O x hx')
  have hlen : (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest.p.nums.stages.length = 4 := by
    show pO.nums.stages.length = 4
    rw [hn]
    rfl
  refine trees_of_thr_ten T H.member _ rfl (rows_heard_O _ _ _ _ _) hall a b rest hst hS.place H.half
    ?_ ?_ own₀ ?_ ?_ ?_ ?_
  · rw [hS.rounds, hS.oracles]
    exact rounds_zip_O h hO
  · rw [hS.oracles]
    exact oracles_count_O h hO
  · rw [H.trees, H.table, H.chain, Fx.ahead, Fx.rounds]
    exact table_seven _ wts rnd JU _ own₀ H.oneU
  · intro τ _
    rw [H.trees, H.table, H.chain, Fx.ahead, Fx.rounds]
    exact table_test _ wts rnd JU _ own₀ H.oneU τ
  · rw [H.trees, Fx.fixed, Fx.ahead, Fx.rounds]
    exact sent_seven
  · intro τ hτ
    rw [hlen] at hτ
    have e : (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest.p.nums.stages =
        piOFull.nums.stages := congrArg (·.stages) hn
    rw [H.trees, Fx.fixed, Fx.ahead, Fx.rounds, e]
    have : τ = 0 ∨ τ = 1 ∨ τ = 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact sent_eight
    · exact sent_nine
    · exact sent_ten

set_option maxHeartbeats 1000000 in
/-- **It plays, at member 10**, at a letter that gives the field. -/
theorem playsS_head_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    (T : Thread Bk St Cl Empty (Common W₀ Rc TableKey) X₀ Pb)
    (Said : ℕ → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (wts : W₀ → Weights) (rnd : Rc → TableRand) (JU : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (c₀ : OnBytes.Model.Verify.Chains) (bs : List (Block St Unit)) {blk : Block St Cl}
    (H : StandO Zp Np pO T Said wts rnd JU own₀ c₀ bs blk) (Fx : FixedO T)
    (c2 : takesCover Bk ⟨sendPlace 2, 0⟩ (jobU ⟨K1.qAt Zp Np, 0⟩) = true) :
    PlaysS T Said 10 := by
  obtain ⟨s₁, t₁, rest, hs₀⟩ := stages_O
  have hstg : (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest.p.nums.stages =
      s₁ :: t₁ :: rest := by
    show pO.nums.stages = _
    rw [nums_head_O h hO]
    exact hs₀
  have hk : s₁.k = (sgOf s₁).h + (sgOf s₁).g := by
    have e := k_head_O h hO
    have e' : pO.nums.stages = s₁ :: t₁ :: rest := hstg
    rw [e'] at e
    exact e
  have h3 : treesU (K1.qAt Zp Np) ≤ 3 := by
    rw [H.oneU]
    omega
  refine playsS_at_own T Said H.member _ _ _ H.seat s₁ t₁ rest hstg hk H.half
    (opened_at_ten H.field) 7 (planPlays_head_O h hO _ rfl rfl s₁ (t₁ :: rest) hstg) H.trees ?_
    (fun k st m E u => old_head_O h hO T wts rnd JU _ own₀ H.trees H.taken H.table c2 H.cover h3 u.1)
    (fun k st m E ds y cols u hd hM =>
      trees_head_O h hO T Said wts rnd JU own₀ c₀ bs H Fx s₁ t₁ rest hstg k st m E ds y cols u.1 hd hM)
  intro k st m E c u hc
  rw [H.chain] at hc
  have H₀ := agree_head_O (V := Empty) (W := Common W₀ Rc TableKey) (X := X₀) h hO hB ⟨K1.qAt Zp Np, 0⟩
    (doorOmegaF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs (fourOf Np).U (fun w => w.key)
      ProofFile.Honest.K12.Light.colsOpened)
    (fun c => wts c.w₀) (fun c => rnd c.rc) none _ _ c hc m.st.input (frontOf m)
  exact H₀

end

end ProofFile.Honest.K12.AtFile

end

#print axioms ProofFile.Honest.K12.AtFile.table_seven
#print axioms ProofFile.Honest.K12.AtFile.table_test
#print axioms ProofFile.Honest.K12.AtFile.sent_seven
#print axioms ProofFile.Honest.K12.AtFile.sent_eight
#print axioms ProofFile.Honest.K12.AtFile.sent_nine
#print axioms ProofFile.Honest.K12.AtFile.sent_ten
#print axioms ProofFile.Honest.K12.AtFile.sent_seven_bent
#print axioms ProofFile.Honest.K12.AtFile.rows_heard_O
#print axioms ProofFile.Honest.K12.AtFile.rounds_zip_O
#print axioms ProofFile.Honest.K12.AtFile.oracles_count_O
#print axioms ProofFile.Honest.K12.AtFile.old_head_O
#print axioms ProofFile.Honest.K12.AtFile.trees_head_O
#print axioms ProofFile.Honest.K12.AtFile.playsS_head_O
