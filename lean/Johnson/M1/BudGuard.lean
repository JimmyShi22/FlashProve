-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- the row at W behind the guard.
/-
Johnson/M1/BudGuard.lean: the body of the field bud₃ at a list whose row is guardRow (testPairs J Js), the row that halfW lays behind the field's guard
(K12/SimO/Guard.lean, Sim2/SlotOwnTest.lean). BudOwed₃ (Johnson/M1/BudShareCore.lean) is that body by definition: this file does not import it.
No property of the protocol is claimed. That the filling lays such a list is not said here. By imports the closure holds modules of the old
system; it names none of them.
-/
import Johnson.M1.BudU
import Johnson.Desc.ProofFile.Honest.K12.SimO.Guard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.M1.BudW
open VerifiableInference.Desc (FileDescription Block Place Chain)
open ProofFile.Honest
open ProofFile.Honest.K12
open ProofFile.Honest.K12.AtProof
open ProofFile.Honest.K12.Light

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

local notation "𝔽" => P5J.F0T OnBytes.secondHashFunction Zp Np cF

theorem take_guardRow {V W Y Pb : Type} (row : List (Part V W Y × Sim Pb)) (j : ℕ) :
    (((guardRow row).take j).map fun x => x.1.moves.length) =
      (row.take j).map fun x => x.1.moves.length := by
  unfold guardRow
  rw [← List.map_take, List.map_map]
  exact List.map_congr_left fun x _ => needsField_length x.1

/-- **At the row behind the guard.** -/
theorem budOwed₃_guarded (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {V W Y Pb : Type} {Bk : ProverCoinCounts}
    (L : Lettered Bk (𝔽).S₃ (𝔽).Cl V W Y Pb) (J : TestJob W Y) (hp : J.p = (fourOf Np).W)
    (hfrN : J.fresh.isNone = false) (Js : SimJob Pb) (hs : Js.p = (fourOf Np).W)
    (ho : Js.own = false) (hpl : L.place = J.p.place) (hrow : L.row = guardRow (testPairs J Js))
    (hbud : ∀ n ds asks, budBoth Js n ds asks → L.bud n ds asks) :
    ∀ σ, L.side (𝔽).second.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
      (𝔽).second.blocksInOrder = pre ++ σ.block :: t →
      n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws, ρ.due 𝔽 = true →
      L.bud u.number ((ρ.second.drop n).take u.rounds.length)
        (asksFrom (treeAsks 𝔽 ρ 2) (u.rounds.map (·.2.length))
          (((rowsOfChain (𝔽).second.blocksInOrder).take n).map (·.2.length)).sum) := by
  intro σ hσ u hu pre t n hcut hn ρ hρ
  let L₀ : Lettered Bk (𝔽).S₃ (𝔽).Cl V W Y Pb := { L with row := testPairs J Js }
  have B := budOwed₃_at_W h L₀ J hp hfrN Js hs ho hpl rfl hbud
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

end Johnson.M1.BudW

#print axioms Johnson.M1.BudW.budOwed₃_guarded
