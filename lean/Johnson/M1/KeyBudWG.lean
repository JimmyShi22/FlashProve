-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- At the key file: the own test's row behind the guard.
/-
Johnson/M1/KeyBudWG.lean: budOwed₃_at_KW at a list whose row is the guarded one (guardRow, K12/SimO/Guard.lean), as the key file's proverSideOfGuardedSending lays it: the twin of
budOwed₃_guarded. FieldGuard.lean and SimO/Guard.lean are K12's, copied unchanged. No property of the protocol is claimed here.
-/
import Johnson.M1.KeyBudW
import Johnson.Desc.ProofFile.Honest.K12.SimO.Guard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.M1.KeyBud
open VerifiableInference.Desc (FileDescription Block Place)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open ProofFile.Honest
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light
open H2K.Member (piKWFull)
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription)

variable {Z : VerifierAndGoals.PublicFiles} {Xs : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
  {Pl : VerifiableInference.Desc.Key.LaterPlaces}

local notation "𝔽" => keyFileDescription Xs N Pl

theorem take_guardRow {V W Y Pb : Type} (row : List (ProofFile.Honest.Part V W Y × Sim Pb)) (j : ℕ) :
    (((guardRow row).take j).map fun x => x.1.moves.length) =
      (row.take j).map fun x => x.1.moves.length := by
  unfold guardRow
  rw [← List.map_take, List.map_map]
  exact List.map_congr_left fun x _ => needsField_length x.1

/-- **At the row behind the guard.** -/
theorem budOwed₃_guarded_KW (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N Pl) {V W Y Pb : Type} {Bk : ProverCoinCounts}
    (L : Lettered Bk (𝔽).S₃ (𝔽).Cl V W Y Pb) (J : TestJob W Y) {ds : List Fmt.Drawn} (Fc : PlaceFacts J.p ds)
    (hst : J.p.nums.stages = piKWFull.nums.stages) (hplace : J.p.place = ⟨3, none, 2, .K12⟩)
    {b₀ : Block (𝔽).S₃ (𝔽).Cl} (hf₀ : ((𝔽).second.blocksInOrder.find? fun b => b.place == J.p.place) = some b₀)
    (hpl₀ : b₀.place = J.p.place) (hr₀ : b₀.rounds = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds)
    (hor₀ : b₀.oracles = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles)
    (hfrN : J.fresh.isNone = false) (Js : SimJob Pb) (hs : Js.p = J.p)
    (ho : Js.own = false) (hpl : L.place = J.p.place) (hrow : L.row = guardRow (testPairs J Js))
    (hbud : ∀ n ds asks, budBoth Js n ds asks → L.bud n ds asks) :
    ∀ σ, L.side (𝔽).second.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
      (𝔽).second.blocksInOrder = pre ++ σ.block :: t →
      n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws, ρ.due (𝔽) = true →
      L.bud u.number ((ρ.second.drop n).take u.rounds.length)
        (asksFrom (treeAsks (𝔽) ρ 2) (u.rounds.map (·.2.length))
          (((rowsOfChain (𝔽).second.blocksInOrder).take n).map (·.2.length)).sum) := by
  intro σ hσ u hu pre t n hcut hn ρ hρ
  let L₀ : Lettered Bk (𝔽).S₃ (𝔽).Cl V W Y Pb := { L with row := testPairs J Js }
  have B := budOwed₃_at_KW scope h L₀ J Fc hst hplace hf₀ hpl₀ hr₀ hor₀ hfrN Js hs ho hpl rfl hbud
  have hσ' := hσ
  unfold Lettered.side Side.seated at hσ'
  obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.1 hσ'
  let σ₀ : Side (𝔽).S₃ (𝔽).Cl V W Y Pb := ⟨b, testPairs J Js, fallOf [] L.place⟩
  have hσ₀ : L₀.side (𝔽).second.blocksInOrder = some σ₀ := by
    unfold Lettered.side Side.seated
    show Option.map _ ((𝔽).second.blocksInOrder.find? fun b => b.place == L.place) = _
    rw [hb]
    rfl
  have eb : σ.block = b := by rw [← e]
  have er : σ.row = guardRow (testPairs J Js) := by rw [← e]; exact hrow
  have hm : σ.members = σ₀.members.map Member.guarded := by
    show membersOf σ.row 0 _ = _
    rw [er, membersOf_guardRow, eb]
    rfl
  rw [hm] at hu
  obtain ⟨u₀, hu₀, rfl⟩ := List.mem_map.1 hu
  have hTo : σ.roundsTo u₀.guarded.number = σ₀.roundsTo u₀.number := by
    unfold Side.roundsTo
    rw [er]
    show (((guardRow (testPairs J Js)).take u₀.number).map fun x => x.1.moves.length).sum = _
    rw [take_guardRow]
  exact B σ₀ hσ₀ u₀ hu₀ pre t n (by rw [hcut, eb]) (by rw [hn, hTo]) ρ hρ

end OnBytes.M1.KeyBud

#print axioms OnBytes.M1.KeyBud.budOwed₃_guarded_KW
