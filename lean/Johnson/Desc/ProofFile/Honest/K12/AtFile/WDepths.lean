-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WDepths.lean: `DepthsDeclared` (Honest/Thread/OneState.lean) at the last
chain's thread whose table is `lastTable` (LastTerm.lean).

  `ownLast_depth`  the test's own tree number τ has the next stage's depth
  `stages_depths`  at the written place the next stages' depths are 18, 15, 13, 15
  `TakenDepths`    the three taken trees' depths, at the two earlier threads' tables
  `declared_last`  `DepthsDeclared` at number 4
  `table_depths_last`   each opening's table has the opening's depth at all k, w, h: the field
                   `tableDepths` of ProofFile's `LastLetters`

By what. `declared_of_each`, `depths_last`, `opens_last` (DepthsLaw.lean, OpensLines.lean); the proof of
`testTbl_depth` (K12/DepthsOfText.lean), at the last chain, where the coins are handed.

Limits. hrest: the frame hands the test's coins at every k: at a filling it is `lent_at_filling`.
`logLength` alone: nothing on what a table holds. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.DepthsLaw
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LastTerm
import Johnson.Desc.ProofFile.Honest.K12.DepthsOfText
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K12
open VerifiableInference.Desc (Block Alike₂ Place)
open H2K.Member (piWFull)
open P2Law.ProofPlan (WP)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12.Light (nums_head_W)

variable {W X : Type} {Bk : ProverCoinCounts}

/-- **The test's own tree number τ has the next stage's depth.** -/
theorem ownLast_depth (J : TestJob W X) (hk : ∀ a ∈ J.p.nums.stages, a.h ≤ a.k) (own₀ : X) (n₀ : ℕ)
    {τ : ℕ} (hτ : τ + 1 < J.p.nums.stages.length) (k : Coins Bk) (w : W) (hd : List Fmt.Drawn)
    (hrest : ∃ c, handedRest 2 J k = some c) :
    (ownLast J own₀ n₀ τ k w hd).2.logLength = (J.p.nums.stages.getD (τ + 1) default).C.a := by
  obtain ⟨c, hc⟩ := hrest
  unfold ownLast testTbl
  simp only [hc, ↓reduceIte, msgAt_table_is_psAt J hk w _ _ _ hτ (depthAt_seed J hτ),
    List.head?_cons, Option.getD_some]

/-- At the written place the next stages' depths. -/
theorem stages_depths : ∀ τ < 4, (piWFull.nums.stages.getD (τ + 1) default).C.a =
    [18, 15, 13, 15].getD τ 0 := by decide +kernel

section
variable {W₂ : Type}

/-- **The three taken trees' depths**, at the two earlier threads' tables. -/
structure TakenDepths (r₁ : ℕ) (toCommon : W → W₂)
    (tb₁ : Fmt.TreeSource → Coins Bk → W → List Fmt.Drawn → Place × Table)
    (tb₂ : Fmt.TreeSource → Coins Bk → W₂ → List Fmt.Drawn → Place × Table) : Prop where
  masks : ∀ k w h, (tb₁ (.own 1) k w h).2.logLength = 13
  own : ∀ k w h, (tb₁ (.own 82) k w h).2.logLength = 22
  omega : ∀ k w h, (tb₂ (.own 1) k w h).2.logLength = 22

/-- What a round of the last chain may open. -/
def srcLast : Fmt.TreeSource → Bool
  | .own n => decide (n < 4)
  | σ => takenLast.contains σ

/-- Every opening of the written last list is of these, at its depth. -/
def opensLast : Bool :=
  lastR.all fun x => x.1.all fun d => d.opens.all fun o => srcLast o.2 && o.1.a == depthLast o.2

#guard opensLast

theorem opens_last_depths : opensLast = true := by decide +kernel

/-- **`lastTable` at a source that may be opened has `depthLast`.** -/
theorem table_depth_last {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles}
    {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} (h : P5J.AtMg o Z D r Zp Np cF)
    (r₁ n₀ : ℕ) (toCommon : W → W₂)
    (tb₁ : Fmt.TreeSource → Coins Bk → W → List Fmt.Drawn → Place × Table)
    (tb₂ : Fmt.TreeSource → Coins Bk → W₂ → List Fmt.Drawn → Place × Table)
    (J : TestJob W X) (own₀ : X) (hp : J.p = (fourOf Np).W) (hk : ∀ a ∈ J.p.nums.stages, a.h ≤ a.k)
    (hrest : ∀ k : Coins Bk, ∃ c, handedRest 2 J k = some c)
    (hD : TakenDepths r₁ toCommon tb₁ tb₂) (σ : Fmt.TreeSource) (hσ : srcLast σ = true) (k : Coins Bk)
    (w : W) (hd : List Fmt.Drawn) :
    (lastTable r₁ toCommon tb₁ tb₂ (ownLast J own₀ n₀) σ k w hd).2.logLength = depthLast σ := by
  cases σ with
  | own n =>
    have hn' : n < 4 := of_decide_eq_true hσ
    have es : J.p.nums.stages = piWFull.nums.stages := by
      rw [hp]
      exact congrArg (·.stages) (nums_head_W h)
    have hτ : n + 1 < J.p.nums.stages.length := by
      rw [es]
      have e5 : piWFull.nums.stages.length = 5 := by decide +kernel
      omega
    show (ownLast J own₀ n₀ n k w hd).2.logLength = [18, 15, 13, 15].getD n 0
    rw [ownLast_depth J hk own₀ n₀ hτ k w hd (hrest k), es]
    exact stages_depths n hn'
  | taken c n =>
    have e : takenLast = [.taken 0 1, .taken 0 82, .taken 1 1] := by decide
    have hm : Fmt.TreeSource.taken c n ∈ takenLast := List.contains_iff_mem.1 hσ
    rw [e] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false, Fmt.TreeSource.taken.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hD.masks k w hd
    · exact hD.own k w hd
    · exact hD.omega k _ _

/-- **The depths of every opening**, at a list alike to the written one: `LastLetters.tableDepths`. -/
theorem table_depths_last {S Cl : Type} {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles}
    {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} (h : P5J.AtMg o Z D r Zp Np cF)
    {bs : List (Block S Cl)} (hl : List.Forall₂ Alike₂ WP.second.blocksInOrder bs)
    (r₁ n₀ : ℕ) (toCommon : W → W₂)
    (tb₁ : Fmt.TreeSource → Coins Bk → W → List Fmt.Drawn → Place × Table)
    (tb₂ : Fmt.TreeSource → Coins Bk → W₂ → List Fmt.Drawn → Place × Table)
    (J : TestJob W X) (own₀ : X) (hp : J.p = (fourOf Np).W) (hk : ∀ a ∈ J.p.nums.stages, a.h ≤ a.k)
    (hrest : ∀ k : Coins Bk, ∃ c, handedRest 2 J k = some c)
    (hD : TakenDepths r₁ toCommon tb₁ tb₂) :
    ∀ d ∈ bs.flatMap (·.rounds), ∀ q ∈ d.opens, ∀ k w hd,
      (lastTable r₁ toCommon tb₁ tb₂ (ownLast J own₀ n₀) q.2 k w hd).2.logLength = q.1.a := by
  intro d hdm q hq k w hd
  obtain ⟨b, hb, hdb⟩ := List.mem_flatMap.1 hdm
  have hx : roundsTrees b ∈ lastR := by
    show roundsTrees b ∈ WP.second.blocksInOrder.map roundsTrees
    rw [rounds_alike hl]
    exact List.mem_map_of_mem hb
  have hall := opens_last_depths
  unfold opensLast at hall
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at hall
  obtain ⟨hs, he⟩ := hall _ hx d hdb q hq
  rw [table_depth_last h r₁ n₀ toCommon tb₁ tb₂ J own₀ hp hk hrest hD q.2 hs k w hd]
  exact he.symm

/-- **`DepthsDeclared` at number 4**, at a thread alike to the written last list whose table is
`lastTable`. -/
theorem declared_last {S Cl V Pb : Type} {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles}
    {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} (h : P5J.AtMg o Z D r Zp Np cF)
    (T : Thread Bk S Cl V W X Pb) (hl : List.Forall₂ Alike₂ WP.second.blocksInOrder T.bs)
    (ht : T.taken = takenLast) (r₁ n₀ : ℕ) (toCommon : W → W₂)
    (tb₁ : Fmt.TreeSource → Coins Bk → W → List Fmt.Drawn → Place × Table)
    (tb₂ : Fmt.TreeSource → Coins Bk → W₂ → List Fmt.Drawn → Place × Table)
    (J : TestJob W X) (own₀ : X) (htb : T.table = lastTable r₁ toCommon tb₁ tb₂ (ownLast J own₀ n₀))
    (hp : J.p = (fourOf Np).W) (hk : ∀ a ∈ J.p.nums.stages, a.h ≤ a.k)
    (hrest : ∀ k : Coins Bk, ∃ c, handedRest 2 J k = some c)
    (hD : TakenDepths r₁ toCommon tb₁ tb₂) : DepthsDeclared T 4 := by
  refine declared_of_each T hl depthLast depths_last (by rw [ht]; exact opens_last) 4 ?_
  intro σ hσ k w hd
  have hσ' : σ ∈ T.taken ++ (List.range (treesTo T.bs 4)).map Fmt.TreeSource.own := hσ
  have h4 : treesTo T.bs 4 = 4 := by
    rw [trees_rounds, ← rounds_alike hl]
    decide +kernel
  rw [ht, h4] at hσ'
  rw [htb]
  rcases List.mem_append.1 hσ' with hm | hm
  · have e : takenLast = [.taken 0 1, .taken 0 82, .taken 1 1] := by decide
    rw [e] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact hD.masks k w hd
    · exact hD.own k w hd
    · exact hD.omega k _ _
  · obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hm
    have hn' := List.mem_range.1 hn
    have es : J.p.nums.stages = piWFull.nums.stages := by
      rw [hp]
      exact congrArg (·.stages) (nums_head_W h)
    have hτ : n + 1 < J.p.nums.stages.length := by
      rw [es]
      have e5 : piWFull.nums.stages.length = 5 := by decide +kernel
      omega
    show (ownLast J own₀ n₀ n k w hd).2.logLength = [18, 15, 13, 15].getD n 0
    rw [ownLast_depth J hk own₀ n₀ hτ k w hd (hrest k), es]
    exact stages_depths n hn'

end

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.ownLast_depth
#print axioms ProofFile.Honest.K12.AtFile.stages_depths
#print axioms ProofFile.Honest.K12.AtFile.TakenDepths
#print axioms ProofFile.Honest.K12.AtFile.declared_last
#print axioms ProofFile.Honest.K12.AtFile.table_depth_last
#print axioms ProofFile.Honest.K12.AtFile.table_depths_last
