-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/OSaid.lean: that the letter which keeps the field is carried over member 10
of the shared thread: the depths of the tables that `tableShared` (TableShared.lean) lays, then `SaidNext` at 10.

  `depths_U_line`, `depths_O_line`, `trees_eleven`   closed lines: the stages that stand behind own 3 to 6 and own 8 to 10 have
                 the depths that `depthShared` (DepthsLaw.lean) says; eleven trees; with controls
  `arm_U`, `arm_own`, `arm_O`   the arms of `tableShared`
  `table_depths`   every own tree below 11 has the depth that `depthShared` says, at every coin, input and list
  `declared_shared`   `DepthsDeclared` at border 11
  `saidNext_ten`   `SaidNext` at 10, at the letter that keeps the field

The premises. hLU, hLO: the book lays the two jobs (`laysB`): at the maker's book `lays_at_head` with `laysB_congr`
(AtFullSide/K12/PaysAtHead.lean). hfit: the thread's test on its rows, a public check.

Limits.
- Depths alone: nothing on what a table holds.
- NOT IN FRONT OF A LAW OVER COINS: `SaidNext` is a sentence behind `Thr`.
- Nothing on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OField
import Johnson.Desc.ProofFile.Honest.K12.AtFile.DepthsLaw
import Johnson.Desc.ProofFile.Honest.K12.DepthsOfText
import Johnson.Desc.ProofFile.Honest.K12.OwnTbl

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open OnBytes (TableKey)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block Place Chain Alike₂)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open Desc.K14 (St blocks P14)
open ProofFile.Honest
open ProofFile.Honest.K14 (jobU jobOmega sendPlace sendTable treesU witOf WitLens)
open ProofFile.Honest.K12
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12.Light (written_at_head qAt_written nums_head_U nums_head_O)
open ProofFile.Honest.SharedThread (lettersShared)
open H2K.Member (piUFull piOFull)
open P2Law.ProofPlan (WP)

/-- The stages behind own 3 to 6. -/
theorem depths_U_line : ((List.range 4).all fun τ => decide (τ + 1 < piUFull.nums.stages.length) &&
    ((piUFull.nums.stages.getD (τ + 1) default).C.a == depthShared (.own (τ + 3)))) = true := by
  decide +kernel

/-- The stages behind own 8 to 10. -/
theorem depths_O_line : ((List.range 3).all fun τ => decide (τ + 1 < piOFull.nums.stages.length) &&
    ((piOFull.nums.stages.getD (τ + 1) default).C.a == depthShared (.own (τ + 8)))) = true := by
  decide +kernel

/-- Control: one place over, no. -/
theorem depths_U_bent : ((List.range 4).all fun τ =>
    ((piUFull.nums.stages.getD (τ + 1) default).C.a == depthShared (.own (τ + 4)))) = false := by
  decide +kernel

/-- Control: one place over, no. -/
theorem depths_O_bent : ((List.range 3).all fun τ =>
    ((piOFull.nums.stages.getD (τ + 1) default).C.a == depthShared (.own (τ + 7)))) = false := by
  decide +kernel

/-- Eleven trees stand behind member 10. -/
theorem trees_eleven : ((sharedR.take 11).map (·.2)).sum = 11 := by decide +kernel

/-- Control: not ten. -/
theorem trees_eleven_bent : ((sharedR.take 11).map (·.2)).sum ≠ 10 := by decide +kernel

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ : Type} (Q : P14) (wts : W₀ → Weights) (rnd : Rc → TableRand)
  (JU JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)

/-- The arm of the test on G_u. -/
theorem arm_U (hu : treesU Q = 1) (n : ℕ) (h3 : 3 ≤ n) (h7 : n < 7) :
    tableShared (Bk := Bk) Q wts rnd JU JO own₀ (.own n) =
      testTbl 1 JU own₀ 8 (fun _ _ _ => true) (n - 3) := by
  show (if n < treesU Q then _ else if n < 3 then _ else if n < 7 then _ else _) = _
  rw [if_neg (by omega), if_neg (by omega), if_pos h7]

/-- The arm of the test's own tree. -/
theorem arm_own (hu : treesU Q = 1) :
    tableShared (Bk := Bk) Q wts rnd JU JO own₀ (.own 7) =
      ownTbl 1 JO own₀ 43 fun _ _ _ => true := by
  show (if 7 < treesU Q then _ else if 7 < 3 then _ else if 7 < 7 then _ else if 7 = 7 then _ else _) = _
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]

/-- The arm of the test on G_omega. -/
theorem arm_O (hu : treesU Q = 1) (n : ℕ) (h8 : 8 ≤ n) :
    tableShared (Bk := Bk) Q wts rnd JU JO own₀ (.own n) =
      testTbl 1 JO own₀ 43 (fun _ _ _ => true) (n - 8) := by
  show (if n < treesU Q then _ else if n < 3 then _ else if n < 7 then _ else if n = 7 then _ else _) = _
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

end

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {pO : P12}
  {W₀ Rc X₀ : Type} {Bk : ProverCoinCounts}

set_option maxHeartbeats 1000000 in
/-- **Every own tree below 11 has the depth that `depthShared` says.** -/
theorem table_depths (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (wts : W₀ → Weights) (rnd : Rc → TableRand) (JU JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (hJU : JU.p = (fourOf Np).U) (hJO : JO.p = pO) (hfr : JO.fresh = none)
    (hLU : laysB Bk 1 JU = true) (hLO : laysB Bk 1 JO = true)
    (hu : treesU (K1.qAt Zp Np) = 1)
    (c2 : takesCover Bk ⟨sendPlace 2, 0⟩ (jobU ⟨K1.qAt Zp Np, 0⟩) = true)
    (c5 : takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega ⟨K1.qAt Zp Np, 0⟩) = true)
    (n : ℕ) (hn : n < 11) (k : Coins Bk) (w : Common W₀ Rc TableKey) (hd : List Fmt.Drawn) :
    (tableShared (Bk := Bk) (K1.qAt Zp Np) wts rnd JU JO own₀ (.own n) k w hd).2.logLength =
      depthShared (.own n) := by
  have hnU : JU.p.nums = piUFull.nums := by
    rw [hJU]
    exact nums_head_U h
  have hnO : JO.p.nums = piOFull.nums := by
    rw [hJO]
    exact nums_head_O h hO
  by_cases h3 : n < 3
  · obtain ⟨x₀, hx₀, Wr⟩ := written_at_head h
    have hU0 : ((VerifiableInference.Desc.Own.treesMade (jobU ⟨K1.qAt Zp Np, 0⟩).Q.codes
        (jobU ⟨K1.qAt Zp Np, 0⟩).Q.sent).getD {}).shapes.toList.map (·.logN) = [24] := by
      have q := shapes_U
      rw [hx₀] at q
      simp only [Option.all_some] at q
      rw [qAt_written Wr Np]
      exact beq_iff_eq.1 q
    have hO0 : ((VerifiableInference.Desc.Own.treesMade (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.codes
        (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.sent).getD {}).shapes.toList.map (·.logN) = [22, 13] := by
      have q := shapes_O
      rw [hx₀] at q
      simp only [Option.all_some] at q
      rw [qAt_written Wr Np]
      exact beq_iff_eq.1 q
    have lenU : 0 < ((VerifiableInference.Desc.Own.treesMade (jobU ⟨K1.qAt Zp Np, 0⟩).Q.codes
        (jobU ⟨K1.qAt Zp Np, 0⟩).Q.sent).getD {}).shapes.toList.length := by
      have e := congrArg List.length hU0
      simp only [List.length_map, List.length_cons, List.length_nil] at e
      omega
    have lenO : 2 = ((VerifiableInference.Desc.Own.treesMade (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.codes
        (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.sent).getD {}).shapes.toList.length := by
      have e := congrArg List.length hO0
      simp only [List.length_map, List.length_cons, List.length_nil] at e
      omega
    match n, hn, h3 with
    | 0, _, _ =>
      have arm : tableShared (Bk := Bk) (K1.qAt Zp Np) wts rnd JU JO own₀ (.own 0) =
          sendTable (jobU ⟨K1.qAt Zp Np, 0⟩) (witOf (K1.qAt Zp Np) wts rnd) (sendPlace 2) 1 0 := by
        show (if 0 < treesU (K1.qAt Zp Np) then _ else _) = _
        rw [if_pos (by omega)]
      rw [arm, sendTable_depth _ _ _ 1 0 k w hd (cut_of_cover k _ _ c2) lenU, hU0]
      rfl
    | 1, _, _ =>
      have arm : tableShared (Bk := Bk) (K1.qAt Zp Np) wts rnd JU JO own₀ (.own 1) =
          sendTable (jobOmega ⟨K1.qAt Zp Np, 0⟩) (witOf (K1.qAt Zp Np) wts rnd) (sendPlace 5) 1 0 := by
        show (if 1 < treesU (K1.qAt Zp Np) then _ else if 1 < 3 then _ else _) = _
        rw [if_neg (by omega), if_pos (by omega), hu]
      rw [arm, sendTable_depth _ _ _ 1 0 k w hd (cut_of_cover k _ _ c5) (by omega), hO0]
      rfl
    | 2, _, _ =>
      have arm : tableShared (Bk := Bk) (K1.qAt Zp Np) wts rnd JU JO own₀ (.own 2) =
          sendTable (jobOmega ⟨K1.qAt Zp Np, 0⟩) (witOf (K1.qAt Zp Np) wts rnd) (sendPlace 5) 1 1 := by
        show (if 2 < treesU (K1.qAt Zp Np) then _ else if 2 < 3 then _ else _) = _
        rw [if_neg (by omega), if_pos (by omega), hu]
      rw [arm, sendTable_depth _ _ _ 1 1 k w hd (cut_of_cover k _ _ c5) (by omega), hO0]
      rfl
  · by_cases h7 : n < 7
    · have q := List.all_eq_true.1 depths_U_line (n - 3) (List.mem_range.2 (by omega))
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at q
      have hk : ∀ a ∈ JU.p.nums.stages, a.h ≤ a.k := by
        rw [hnU]
        exact hk_U
      have hτ : n - 3 + 1 < JU.p.nums.stages.length := by
        rw [hnU]
        exact q.1
      rw [arm_U _ wts rnd JU JO own₀ hu n (by omega) h7,
        testTbl_depth JU hk 1 (Or.inr rfl) hLU own₀ 8 hτ k w hd, hnU, q.2]
      congr 2
      omega
    · by_cases h8 : n = 7
      · subst h8
        obtain ⟨s₁, t₁, l, hs₀⟩ := stages_O
        have hst : JO.p.nums.stages = s₁ :: t₁ :: l := by
          rw [hnO]
          exact hs₀
        have hz : s₁.Z.a = 13 := by
          have e := depths_head_O h hO
          rw [← hJO, hst] at e
          exact e.2.2
        have hd1 : depthAt JO 1 = some 13 := by
          have hfi : JO.fresh.isNone = true := by rw [hfr]; rfl
          unfold depthAt
          rw [hst, hfi, ← hz]
          rfl
        rw [arm_own _ wts rnd JU JO own₀ hu, ownTbl_depth JO hfr 1 (Or.inr rfl) hLO own₀ 43 hd1 k w hd]
        rfl
      · have q := List.all_eq_true.1 depths_O_line (n - 8) (List.mem_range.2 (by omega))
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at q
        have hk : ∀ a ∈ JO.p.nums.stages, a.h ≤ a.k := by
          rw [hnO]
          exact fun a ha => of_decide_eq_true (List.all_eq_true.1 hk_O a ha)
        have hτ : n - 8 + 1 < JO.p.nums.stages.length := by
          rw [hnO]
          exact q.1
        rw [arm_O _ wts rnd JU JO own₀ hu n (by omega),
          testTbl_depth JO hk 1 (Or.inr rfl) hLO own₀ 43 hτ k w hd, hnO, q.2]
        congr 2
        omega

/-- **`DepthsDeclared` at border 11**, at a thread alike to the written list whose tables are `tableShared`. -/
theorem declared_shared {Cl V Pb : Type} (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (T : Thread Bk St Cl V (Common W₀ Rc TableKey) X₀ Pb)
    (hl : List.Forall₂ Alike₂ WP.shared.blocksInOrder T.bs) (ht : T.taken = [])
    (wts : W₀ → Weights) (rnd : Rc → TableRand) (JU JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (htb : T.table = tableShared (K1.qAt Zp Np) wts rnd JU JO own₀)
    (hJU : JU.p = (fourOf Np).U) (hJO : JO.p = pO) (hfr : JO.fresh = none)
    (hLU : laysB Bk 1 JU = true) (hLO : laysB Bk 1 JO = true)
    (hu : treesU (K1.qAt Zp Np) = 1)
    (c2 : takesCover Bk ⟨sendPlace 2, 0⟩ (jobU ⟨K1.qAt Zp Np, 0⟩) = true)
    (c5 : takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega ⟨K1.qAt Zp Np, 0⟩) = true) :
    DepthsDeclared T 11 := by
  refine declared_of_each T hl depthShared depths_shared (by rw [ht]; exact opens_shared) 11 ?_
  intro σ hσ k w hd
  have hσ' : σ ∈ T.taken ++ (List.range (treesTo T.bs 11)).map Fmt.TreeSource.own := hσ
  have h11 : treesTo T.bs 11 = 11 := by
    rw [trees_rounds, ← rounds_alike hl]
    exact trees_eleven
  rw [ht, h11, List.nil_append] at hσ'
  obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hσ'
  rw [htb]
  exact table_depths h hO wts rnd JU JO own₀ hJU hJO hfr hLU hLO hu c2 c5 n (List.mem_range.1 hn) k w hd

variable {x₀ : VerifiableInference.Desc.First.Look.Place}
  {Tr X P₁ Wt : Type}
  {H : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ X} {N : NumbersS}
  {Mg : Common W₀ Rc TableKey → MeaningS St P₁ Wt} {shape : ℕ → St → Bool} {nothingLeft : St → Bool}
  {order : St → Prop} {wit : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt}
  {table : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table}
  {fixed : Fmt.TreeSource → ℕ} {n₁ n₂ : ℕ} {Vd : Common W₀ Rc TableKey → Prop}
  {Rd : ℕ → Common W₀ Rc TableKey → St → Prop} {Kp : Place → St → St → Prop}
  {w : Common W₀ Rc TableKey} {ℓ : WitLens Wt} {Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt}
  {wts : W₀ → Weights} {rnd : Rc → TableRand}
  {rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Words Cb.Gl.E}
  {JU : TestJob (Common W₀ Rc TableKey) X₀} {own₀ : X₀}

/-- The thread's letters. -/
local notation "𝐋" => lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w

set_option maxHeartbeats 1000000 in
/-- **`SaidNext` at member 10, at the letter that keeps the field.** -/
theorem saidNext_ten (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hO : (fourOf Np).O = some pO)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (G : LetterO N Mg wit table fixed Zp Np pO [b1, b2, b3, b4, b5, b6, b7, b8] ℓ Mg₀ wts rnd rest JU
      own₀)
    (hhalf : (H.shared.find? fun g => g.place == pO.place) =
      some (proverSideOfProximityTest (jobDoorO (X₀ := X₀) Zp Np pO [b1, b2, b3, b4, b5, b6, b7, b8] wts rnd).toRun.toTest :
        Placed Empty _ X₀).needsField)
    (c2 : takesCover Bk ⟨sendPlace 2, 0⟩ (jobU ⟨K1.qAt Zp Np, 0⟩) = true)
    (c5 : takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega ⟨K1.qAt Zp Np, 0⟩) = true)
    (hJU : JU.p = (fourOf Np).U) (hLU : laysB Bk 1 JU = true)
    (hLO : laysB Bk 1 (jobDoorO (X₀ := X₀) Zp Np pO [b1, b2, b3, b4, b5, b6, b7, b8] wts rnd).toRun.toTest =
      true)
    {n : ℕ} (hfit : (𝐋).thread.fits n = true) (hn : 10 ≤ n) :
    SaidNext (𝐋).thread (SaidField (𝐋).thread BaseNil) 10 := by
  have hl : List.Forall₂ Alike₂ WP.shared.blocksInOrder (𝐋).thread.bs :=
    ProofFile.Honest.K14.alike_shared_at_laid h.scope h.laid
  have hD : DepthsDeclared (𝐋).thread 11 :=
    declared_shared h.toAtMg hO (𝐋).thread hl rfl wts rnd JU _ own₀ G.table hJU rfl rfl hLU hLO
      (treesU_head h.toAtMg) c2 c5
  exact saidNext_field (𝐋).thread hfit hn (treesNext_ten h hO b1 b2 b3 b4 b5 b6 b7 b8 hb G hhalf c5)
    (baseNil_kept _ 10) (opensAvailable_shared _ hl rfl 11) fun k m => depthsAt_of_declared hD k m

end ProofFile.Honest.K12.AtFile

end

#print axioms ProofFile.Honest.K12.AtFile.depths_U_line
#print axioms ProofFile.Honest.K12.AtFile.depths_O_line
#print axioms ProofFile.Honest.K12.AtFile.depths_U_bent
#print axioms ProofFile.Honest.K12.AtFile.depths_O_bent
#print axioms ProofFile.Honest.K12.AtFile.trees_eleven
#print axioms ProofFile.Honest.K12.AtFile.trees_eleven_bent
#print axioms ProofFile.Honest.K12.AtFile.arm_U
#print axioms ProofFile.Honest.K12.AtFile.arm_own
#print axioms ProofFile.Honest.K12.AtFile.arm_O
#print axioms ProofFile.Honest.K12.AtFile.table_depths
#print axioms ProofFile.Honest.K12.AtFile.declared_shared
#print axioms ProofFile.Honest.K12.AtFile.saidNext_ten
