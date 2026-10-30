-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WTrees.lean: the clause `trees` of `StandAtW` (WAccepted.lean):
the last chain's test's new trees are the thread's tables.

  `trees_of_thr_field`   `trees_of_thr` (K12/TreesOfThr.lean) behind the guard: from `Thr`, the field,
                 the draws and `Thread.Moved`. General in the thread and the job
  `rows_heard_first`, `rows_heard_omega`   a member's rows read of the front what was heard alone
  `rows_heard_W`   so at the job of the last chain's test, at its sendings
  `rounds_zip_W`, `oracles_count_W`, `hk_head_W`   the seated block's counts, and h ≤ k at each stage
  `trees_head_W`   the clause, at a thread whose own trees' tables and counts are the test's

The premises of `trees_head_W`. htable, hfixed: the thread's own trees: `ownLast` (LastTerm.lean) at
the rounds in front, and the round that fixes each. hchain: the last chain's number.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: it stands behind `Thr` and `Thread.Moved`.
- `testTbl` is a text of a test's tree: the head of K12/ScriptLots.lean binds whoever lays it.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WAtHead
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LastTerm
import Johnson.Desc.ProofFile.Honest.K12.TreesOfThr
import Johnson.Desc.ProofFile.Honest.K12.TablesAtFront
import Johnson.Desc.ProofFile.Honest.K12.FieldGuardLift
import Johnson.Desc.ProofFile.Honest.K12.AtProof.JobW

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K12
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open H2K.Member (piWFull)
open ProofFile.Honest.K12.AtProof (fourOf jobW memK1)
open ProofFile.Honest.K12.Light (ManyJob memOfSending nums_head_W reads_head_W facts_head_W pairOf
  pairs_of_planOk facts_WFull)

/-- **The new trees are the thread's tables, behind the guard.** -/
theorem trees_of_thr_field {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb) {b : ℕ}
    {blk : Block S Cl} (hblk : T.bs[b]? = some blk) (J : TestJob W X)
    (hfresh : J.fresh.isNone = false) (hR : RowsOfHeard J)
    (hk : ∀ a ∈ J.p.nums.stages, a.h ≤ a.k)
    (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: t :: rest)
    (hpl : blk.place = J.p.place)
    (hhalf : (T.hs.find? fun g => g.place == blk.place) =
      some (proverSideOfProximityTest J : Placed V W X).needsField)
    (hrs : (blk.rounds.zip blk.oracles).length =
      firstLen J.p.nums.stages + restLen J.p.nums.stages)
    (hcount : (blk.oracles.flatMap id).length + 1 = J.p.nums.stages.length)
    (own₀ : X)
    (htable : ∀ τ, τ + 1 < J.p.nums.stages.length → T.table (.own (treesTo T.bs b + τ)) =
      testTbl T.chain J own₀ (T.front + roundsTo T.bs b) (fun _ _ _ => true) τ)
    (hfixed : ∀ τ, τ + 1 < J.p.nums.stages.length → T.fixed (.own (treesTo T.bs b + τ)) =
      T.front + roundsTo T.bs b + seedRound J.p.nums.stages τ) :
    ∀ k st m E ds y cols, Thr T b k st m E → m.opened.isSome = true →
      drawsFit blk.rounds ds = true →
      T.Moved blk k m E ds y cols → T.Trees (T.fresh b) k y.2 (E.add y.1) := by
  intro k st m E ds y cols hT hop _ hMv σ hσ
  obtain ⟨⟨l, hl, hy⟩, -⟩ := hMv
  obtain ⟨c', hc', rfl⟩ := steps_one_half hhalf hl
  have hc'' : lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) blk.place
      ((proverSideOfProximityTest J : Placed V W X).parts.map Part.needsField) 0 = .ok c' := hc'
  rw [lendRow_guarded] at hc''
  obtain ⟨c, hc, rfl⟩ := map_ok hc''
  rw [placedSteps_guarded (proverSideOfProximityTest J) blk (T.φ.sees m.st.input) c] at hy
  obtain ⟨cs, hcs⟩ := Option.isSome_iff_exists.1 hop
  rw [play_guarded _ ds [] m cs hcs] at hy
  rw [hpl] at hc
  have hy' : play (rowSteps blk.name J.p.place (T.φ.sees m.st.input)
      [(firstPart J : Part V W X), restPart J] 0 (blk.rounds.zip blk.oracles) c) ds [] m =
      .ok y := by
    have e := hy
    unfold Placed.steps at e
    rw [hpl] at e
    exact e
  obtain ⟨i, hi, rfl⟩ := K14.fresh_mem_own T hblk hσ
  have hi' : i + 1 < J.p.nums.stages.length := by omega
  have hsent : E.sent = treesTo T.bs b := hT.2.2.2.2.1.2.2.1
  have hheard : m.st.heard.length = T.front + roundsTo T.bs b := by
    have e := drawsFit_length _ _ hT.2.1
    rw [List.length_append] at e
    exact e
  obtain ⟨-, hst2⟩ := half_tables J s t rest hst blk.name (T.φ.sees m.st.input) _ hrs c ds [] m y hy'
  have hin : y.2.st.input = m.st.input := by rw [hst2]
  have hhd : y.2.st.heard = m.st.heard ++ ds := by rw [hst2]
  have hmain := table_in_run J hR hk s t rest hst blk.name (T.φ.sees m.st.input) _ hrs T.chain k c hc
    ds [] m y hy' own₀ _ hheard hi'
    ((m.st.heard ++ ds).take (T.front + roundsTo T.bs b + seedRound J.p.nums.stages i))
    (by rw [List.take_take, Nat.min_self])
  rw [hfresh] at hmain
  simp only [Bool.false_eq_true, if_false, Nat.add_zero] at hmain
  have htree : (E.add y.1).tree (.own (treesTo T.bs b + i)) =
      some (testTbl T.chain J own₀ (T.front + roundsTo T.bs b) (fun _ _ _ => true) i k m.st.input
        ((m.st.heard ++ ds).take (T.front + roundsTo T.bs b + seedRound J.p.nums.stages i))) := by
    rw [← hsent, K14.add_own, hmain]
    rfl
  have htab : T.tableAt (.own (treesTo T.bs b + i)) k y.2 =
      testTbl T.chain J own₀ (T.front + roundsTo T.bs b) (fun _ _ _ => true) i k m.st.input
        ((m.st.heard ++ ds).take (T.front + roundsTo T.bs b + seedRound J.p.nums.stages i)) := by
    unfold Thread.tableAt
    rw [htable i hi', hfixed i hi', hhd, hin]
  unfold Thread.handAt
  rw [htree, htab]
  simp [Table.same_refl]

section
variable {W X Wd Xi : Type}

/-- **A sending's member reads of the front what was heard alone**, where the sending's data does. -/
theorem rows_heard_first (J : K1.SendJob Wd X) (lift : W → Wd) (at_ : Addr) (k : ℕ)
    (fs : Option ℕ × Option ℕ)
    (hJ : ∀ x (fr fr' : Front X), fr.heard = fr'.heard → J.data x fr = J.data x fr')
    (w : W) (fr fr' : Front X) (c : Stretch) (he : fr.heard = fr'.heard) :
    (memK1 J lift at_ k fs).rows w fr c = (memK1 J lift at_ k fs).rows w fr' c := by
  show ProofFile.Honest.K12.AtProof.psOfRows J.P k (K1.rowsR J.P J.ride (J.data (lift w) fr) _ k) =
    ProofFile.Honest.K12.AtProof.psOfRows J.P k (K1.rowsR J.P J.ride (J.data (lift w) fr') _ k)
  rw [hJ _ _ _ he]

/-- **Omega's member reads of the front what was heard alone.** -/
theorem rows_heard_omega (J : ProofFile.Honest.K14.SendJob) (at_ : Addr) (k : ℕ)
    (fs : Option ℕ × Option ℕ) (ask : W → ProofFile.Honest.K14.Ask) (w : W) (fr fr' : Front X)
    (c : Stretch) (he : fr.heard = fr'.heard) :
    (memOfSending J at_ k fs ask none).rows w fr c =
      (memOfSending J at_ k fs ask none).rows w fr' c := by
  simp only [memOfSending, he]

/-- **The job's rows read the heard alone.** -/
theorem rows_heard_W (q : P12) (door : W → Front X → T12) (JI : K1.SendJob Readers X)
    (JW : K1.SendJob (K1.PlaceIn Xi) X) (A : ProofFile.Honest.K14.SendPub) (readers : W → Readers)
    (wit : W → K1.PlaceIn Xi) (ask : W → ProofFile.Honest.K14.Ask) (n₁ : ℕ)
    (hI : ∀ x (fr fr' : Front X), fr.heard = fr'.heard → JI.data x fr = JI.data x fr')
    (hW : ∀ x (fr fr' : Front X), fr.heard = fr'.heard → JW.data x fr = JW.data x fr') :
    RowsOfHeard (jobW q door JI JW A readers wit ask n₁).toRun.toTest := by
  refine rowsOfHeard_many _ fun m hm w fr fr' c he => ?_
  simp only [jobW, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · exact rows_heard_first _ _ _ _ _ hI w fr fr' c he
  · exact rows_heard_first _ _ _ _ _ hW w fr fr' c he
  · exact rows_heard_omega _ _ _ _ _ w fr fr' c he

end

/-- h ≤ k at every stage of the written place. By the kernel. -/
theorem hk_W : (piWFull.nums.stages.all fun a => decide (a.h ≤ a.k)) = true := by decide +kernel

/-- The written place's messages: one tree fewer than stages. By the kernel. -/
theorem count_W : (piWFull.oracles.flatMap id).length + 1 = piWFull.nums.stages.length := by
  decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- The flattening of a list of lists does not change its length when each entry is mapped. -/
theorem flat_length {α β : Type} (f : α → β) : ∀ l : List (List α),
    ((l.map (·.map f)).flatMap id).length = (l.flatMap id).length
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, List.flatMap_cons, id, List.length_append, List.length_map,
      flat_length f l]

/-- The seated block's rounds and messages have as many entries as the term. -/
theorem rounds_zip_W (h : P5J.AtMg o Z D r Zp Np cF) :
    ((proximityTestKind guardedProximityTestParts (fourOf Np).W : Block T12 Unit).rounds.zip
      (proximityTestKind guardedProximityTestParts (fourOf Np).W : Block T12 Unit).oracles).length =
      firstLen (fourOf Np).W.nums.stages + restLen (fourOf Np).W.nums.stages := by
  rw [zip_laid (fourOf Np).W (reads_head_W h).2.2.2]
  exact (facts_head_W h).count

/-- The seated block declares one tree fewer than the place has stages. -/
theorem oracles_count_W (h : P5J.AtMg o Z D r Zp Np cF) :
    ((proximityTestKind guardedProximityTestParts (fourOf Np).W : Block T12 Unit).oracles.flatMap id).length + 1 =
      (fourOf Np).W.nums.stages.length := by
  have e : (fourOf Np).W.oracles.map (·.map pairOf) = piWFull.oracles.map (·.map pairOf) := by
    refine Option.some.inj ?_
    rw [← pairs_of_planOk guardedProximityTestParts (fourOf Np).W (reads_head_W h).2.2.2,
      ← pairs_of_planOk guardedProximityTestParts piWFull facts_WFull.plan, nums_head_W h]
  rw [VerifiableInference.Desc.K12.k12_oracles guardedProximityTestParts (fourOf Np).W (reads_head_W h).2.2.2,
    nums_head_W h, ← flat_length pairOf, e, flat_length]
  exact count_W

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **The clause `trees` of `StandAtW`.** blk: the seated block; J: the job. The thread's own trees are
the test's, from its number 0 on. -/
theorem trees_head_W (h : P5J.AtMg o Z D r Zp Np cF) (T : Thread Bk S Cl V W X Pb) {b : ℕ}
    {blk : Block S Cl} (hblk : T.bs[b]? = some blk) (J : TestJob W X)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (hseat : SeatOf blk J enter leave) (hp : J.p = (fourOf Np).W)
    (hfresh : J.fresh.isNone = false) (hR : RowsOfHeard J)
    (hhalf : (T.hs.find? fun g => g.place == blk.place) =
      some (proverSideOfProximityTest J : Placed V W X).needsField)
    (own₀ : X)
    (htable : ∀ τ, τ + 1 < J.p.nums.stages.length → T.table (.own (treesTo T.bs b + τ)) =
      testTbl T.chain J own₀ (T.front + roundsTo T.bs b) (fun _ _ _ => true) τ)
    (hfixed : ∀ τ, τ + 1 < J.p.nums.stages.length → T.fixed (.own (treesTo T.bs b + τ)) =
      T.front + roundsTo T.bs b + seedRound J.p.nums.stages τ) :
    ∀ k st m E ds y cols, Thr T b k st m E → m.opened.isSome = true →
      drawsFit blk.rounds ds = true →
      T.Moved blk k m E ds y cols → T.Trees (T.fresh b) k y.2 (E.add y.1) := by
  have hst : ∃ s t rest, J.p.nums.stages = s :: t :: rest := by
    rw [hp, nums_head_W h]
    exact ⟨_, _, _, rfl⟩
  obtain ⟨s, t, rest, hst⟩ := hst
  refine trees_of_thr_field T hblk J hfresh hR ?_ s t rest hst hseat.place hhalf ?_ ?_ own₀ htable
    hfixed
  · intro x hx
    have e : J.p.nums.stages = piWFull.nums.stages := by
      rw [hp, nums_head_W h]
    have hx' : x ∈ piWFull.nums.stages := e ▸ hx
    exact of_decide_eq_true (List.all_eq_true.1 hk_W x hx')
  · rw [hseat.rounds, hseat.oracles, hp]
    exact rounds_zip_W h
  · rw [hseat.oracles, hp]
    exact oracles_count_W h

end

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.trees_of_thr_field
#print axioms ProofFile.Honest.K12.AtFile.rows_heard_first
#print axioms ProofFile.Honest.K12.AtFile.rows_heard_omega
#print axioms ProofFile.Honest.K12.AtFile.rows_heard_W
#print axioms ProofFile.Honest.K12.AtFile.hk_W
#print axioms ProofFile.Honest.K12.AtFile.count_W
#print axioms ProofFile.Honest.K12.AtFile.rounds_zip_W
#print axioms ProofFile.Honest.K12.AtFile.oracles_count_W
#print axioms ProofFile.Honest.K12.AtFile.trees_head_W
