-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/M1/BudTestL.lean: what the row of the proximity test that closes the first chain owes to `BudDebts`, at every due list
of challenges. `bound_rest_first_chain` (K12/Sim2/StandL.lean) has the bound at the second member in the field's own form, and
`first_owes_nothing` the first member's where the fresh table came earlier.

  `budOwed_at_L`   under the head, at a list that stands at the test's place with the two parts and whose bud follows from
      `budBoth`: `BudOwed`

Limits. The place L alone. A run of one request. No property of the protocol is claimed: nothing is said on its soundness,
completeness, binding or hiding.
-/
import Johnson.M1.BudShareCore
import Johnson.Desc.ProofFile.Honest.K12.Sim2.StandL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (FileDescription Block Place Chain)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest
open ProofFile.Honest.K12.AtProof
open ProofFile.Honest.K12.Light
open H2K.Pub (sgOf)
open Johnson.G.OfPlan (rootsOf)
open Johnson.M1 (BudOwed)

variable {W₀ Rc Tr : Type} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}

local notation "𝔽" => P5J.F0T OnBytes.secondHashFunction Zp Np cF

/-- **The test's row owes nothing more to `BudDebts`.** -/
theorem budOwed_at_L (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {Y : Type} {Bk : ProverCoinCounts}
    (L : Lettered Bk (𝔽).S₁ (𝔽).Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y ProofFile.Inst)
    (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) Y) (hp : J.p = (fourOf Np).L)
    (hfrN : J.fresh.isNone = false) (Js : SimJob ProofFile.Inst) (hs : Js.p = (fourOf Np).L)
    (ho : Js.own = false) (hpl : L.place = J.p.place) (hrow : L.row = testPairs J Js)
    (hbud : ∀ n ds asks, budBoth Js n ds asks → L.bud n ds asks) : BudOwed 𝔽 L := by
  intro σ hσ u hu pre t n hcut hn ρ hρ
  have hσ' : testSide (𝔽).first.blocksInOrder J Js [] = some σ := by
    unfold testSide
    rw [← hpl, ← hrow]
    exact hσ
  have Fc := facts_head_L h
  rw [← hp] at Fc
  obtain ⟨-, f2, -, -, -⟩ :=
    (first_any_head_L (V := Local W₀ Rc ProofFile.Inst Tr) h J Js hp hfrN hs ho).2.2 [] σ hσ'
  have f2' : σ.members = [firstMember J Js, restMember J Js] := f2
  rw [f2'] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact hbud _ _ _ (budBoth_of_testBud Js _ _ (first_owes_nothing Js ho _ _))
  · have hσ'' := hσ'
    unfold testSide Side.seated at hσ''
    obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.1 hσ''
    have hrowσ : σ.row = testPairs J Js := by rw [← e]
    obtain ⟨s, next, rest, hst⟩ : ∃ s next rest, J.p.nums.stages = s :: next :: rest := by
      have hform := Fc.form
      unfold formPubB at hform
      cases hs' : J.p.nums.stages with
      | nil => rw [hs'] at hform; cases hform
      | cons a l =>
        cases l with
        | nil => rw [hs'] at hform; cases hform
        | cons b' r' => exact ⟨a, b', r', rfl⟩
    have FP := formPub_of_B J.p s next rest hst Fc.form
    have hk : s.k = (sgOf s).h + (sgOf s).g := by
      have := FP.hk
      show s.k = s.h + (s.k - s.h)
      omega
    obtain ⟨b', hf, hpl', hr, hor⟩ := find_last h
    have hb' : b = b' := by
      rw [hp] at hb
      exact Option.some.inj (hb.symm.trans hf)
    have eb : σ.block = b' := by rw [← hb', ← e]
    have hzip : σ.block.rounds.zip σ.block.oracles = J.laid := by
      rw [eb, hr, hor]
      show _ = H2K.JointK.laidOf J.p
      rw [hp]
      exact zip_laid _ (facts_head_L h).plan
    have hblk : σ.block ∈ (𝔽).first.blocksInOrder := by
      rw [hcut]
      exact List.mem_append_right _ List.mem_cons_self
    have hsh : σ.block.shaped = true := planOk_shaped_first h.laid.planOk σ.block hblk
    have hlen : σ.block.rounds.length = J.laid.length := by
      rw [← hzip, List.length_zip, shaped_len σ.block hsh, Nat.min_self]
    have hT : tablesFitB J = true := by
      rw [tablesFitB_eq, hfrN]
      exact Fc.tab
    have hN := trees_rest J pre t σ.block
      (fun x hx => planOk_shaped_first h.laid.planOk x (by rw [hcut]; exact List.mem_append_left _ hx))
      hzip hT Fc.enough
    rw [← hcut] at hN
    obtain ⟨O, hold, ha⟩ := premises_at_last_test h J hp hfrN pre t σ.block hcut (by rw [eb, hpl', hp])
    have hB := bound_rest_first_chain (V := Local W₀ Rc ProofFile.Inst Tr) J Js pre t σ.block hcut [23] _ _ O s
      next rest hst hk hT hold hlen Fc.enough ρ hρ ha
    have l1 : (firstPart J : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y).moves.length =
        firstLen J.p.nums.stages :=
      (congrArg List.length (first_moves J)).trans (len_movesFrom J _ _ _)
    have hTo : σ.roundsTo (restMember (V := Local W₀ Rc ProofFile.Inst Tr) J Js).number =
        firstLen J.p.nums.stages := by
      unfold Side.roundsTo
      rw [hrowσ]
      show (firstPart J : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y).moves.length + 0 = _
      rw [l1]
      rfl
    subst hn
    rw [hTo]
    refine hbud _ _ _ ((both_rest Js _ _).2 ?_)
    rw [hs, ← hp, hN]
    exact hB

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.budOwed_at_L
