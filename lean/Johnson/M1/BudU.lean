-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- what the row of the proximity test on the folded row's group owes to BudDebts.
/-
Johnson/M1/BudU.lean: the field bud₂ of BudDebts at a list that stands at the test on G_u, at every due list of challenges, with the premises
paid by the library's premises_at_U (Sim/AloneAtU.lean). budDebts_U_head there has the one-row form at bud = budBoth; this is the list-by-list form at a bud that budBoth implies, at any letters. No property of the protocol is claimed.

-/
import Johnson.M1.BudW
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstAnyAtHeadU
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstSeatAtHead
import Johnson.Desc.ProofFile.Honest.K12.Sim.AloneAtU

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.M1.BudW
open VerifiableInference.Desc (FileDescription Block Place Chain)
open VerifiableInference.Desc.K12 (P12 T12)
open ProofFile.Honest
open ProofFile.Honest.K12
open ProofFile.Honest.K12.AtProof
open ProofFile.Honest.K12.Light
open H2K.Pub (sgOf)
open Johnson.G.OfPlan (rootsOf)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

local notation "𝔽" => P5J.F0T OnBytes.secondHashFunction Zp Np cF

/-- **THE TEST'S ROW OWES NOTHING MORE TO bud₂**: under the head, at a list that stands at the test on G_u with the two parts and whose bud follows
from budBoth: the field's body, at every due list of challenges. -/
theorem budOwed₂_at_U (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {V W Y Pb : Type} {Bk : ProverCoinCounts}
    (L : Lettered Bk (𝔽).S₂ (𝔽).Cl V W Y Pb) (J : TestJob W Y) (hp : J.p = (fourOf Np).U)
    (hfrN : J.fresh.isNone = false) (Js : SimJob Pb) (hs : Js.p = (fourOf Np).U)
    (ho : Js.own = false) (hpl : L.place = J.p.place) (hrow : L.row = testPairs J Js)
    (hbud : ∀ n ds asks, budBoth Js n ds asks → L.bud n ds asks) :
    ∀ σ, L.side (𝔽).shared.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
      (𝔽).shared.blocksInOrder = pre ++ σ.block :: t →
      n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws, ρ.due 𝔽 = true →
      L.bud u.number ((ρ.shared.drop n).take u.rounds.length)
        (asksFrom (treeAsks 𝔽 ρ 1) (u.rounds.map (·.2.length))
          (((rowsOfChain (𝔽).shared.blocksInOrder).take n).map (·.2.length)).sum) := by
  intro σ hσ u hu pre t n hcut hn ρ hρ
  have hσ' : testSide (𝔽).shared.blocksInOrder J Js [] = some σ := by
    unfold testSide
    rw [← hpl, ← hrow]
    exact hσ
  have Fc := facts_head_U h
  rw [← hp] at Fc
  obtain ⟨-, f2, -, -, -⟩ := (first_any_head_U (V := V) h J Js hp hfrN hs ho).2.2 [] σ hσ'
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
    obtain ⟨b', hf, hpl', hr, hor⟩ := find_gu h
    have hb' : b = b' := by
      rw [hp] at hb
      exact Option.some.inj (hb.symm.trans hf)
    have eb : σ.block = b' := by rw [← hb', ← e]
    have hzip : σ.block.rounds.zip σ.block.oracles = J.laid := by
      rw [eb, hr, hor]
      show _ = H2K.JointK.laidOf J.p
      rw [hp]
      exact zip_laid _ (facts_head_U h).plan
    have hblk : σ.block ∈ (𝔽).shared.blocksInOrder := by
      rw [hcut]
      exact List.mem_append_right _ List.mem_cons_self
    have hsh : σ.block.shaped = true := planOk_shaped h.laid.planOk σ.block hblk
    have hlen : σ.block.rounds.length = J.laid.length := by
      rw [← hzip, List.length_zip, shaped_len σ.block hsh, Nat.min_self]
    have hT : tablesFitB J = true := by
      rw [tablesFitB_eq, hfrN]
      exact Fc.tab
    have hN := trees_rest J pre t σ.block
      (fun x hx => planOk_shaped h.laid.planOk x (by rw [hcut]; exact List.mem_append_left _ hx))
      hzip hT Fc.enough
    rw [← hcut] at hN
    obtain ⟨O, hold, ha⟩ := ProofFile.Honest.K12.Light.AtU.premises_at_U h J hp hfrN pre t σ.block hcut (by rw [eb, hpl', hp])
    have hB := bud_rest_file (V := V) J Js pre t σ.block hcut [24, 13] _ _ O s
      next rest hst hk hT hold hlen Fc.enough ρ hρ ha
    have l1 : (firstPart J : Part V W Y).moves.length = firstLen J.p.nums.stages :=
      (congrArg List.length (first_moves J)).trans (len_movesFrom J _ _ _)
    have hTo : σ.roundsTo (restMember (V := V) J Js).number = firstLen J.p.nums.stages := by
      unfold Side.roundsTo
      rw [hrowσ]
      show (firstPart J : Part V W Y).moves.length + 0 = _
      rw [l1]
      rfl
    subst hn
    rw [hTo]
    refine hbud _ _ _ ((both_rest Js _ _).2 ?_)
    rw [hs, ← hp, hN]
    exact hB

end Johnson.M1.BudW

#print axioms Johnson.M1.BudW.budOwed₂_at_U
