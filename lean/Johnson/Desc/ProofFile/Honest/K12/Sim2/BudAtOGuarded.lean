-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/BudAtOGuarded.lean: CONDITIONAL on the head.

What is here. What a list owes to `BudDebts` at the shared chain goes over to the same list behind the
guard, and so `BudOwed₂` (Johnson/M1/BudShareCore.lean) at the list that stands at the test on G_omega:
`rowAtOmega`'s row (SimO/SlotO.lean) is omegaRow J Js, the guard around `testPairs J Js`, while
`budOwed₂_at_O` (Johnson/M1/BudTestO.lean) stands at the bare row. The fellow of `budOwed₃_guarded`
(Johnson/M1/BudGuard.lean) for W.

  `budOwed₂_guarded`   **general**: in the description, the list and the row: the bud, the place and the
      row's parts but for the guard are the other list's.
  `budOwed₂_at_O_guarded`   **at `IsListAtO` (Sim2/ListO.lean), at both members**, with the list's bound
      `budBoth Js`: the bud of `rowAtOmega`, at which exact is held.
  `budOwed₂_at_lot`   the same at a list with the four fields of a row of `lotAtOmega`: `Unlettered.lay` meets them.

Limits. One list. `budBoth` is `budFirst` at part 0 (positions asked of part 0's own table: in range, at most Z.r
different) and `budOpened` at part 1 (positions asked are among those sampled; no number). The first opening's
positions at the senders' trees are K14's senders'.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.ListO
import Johnson.M1.BudTestO
import Johnson.M1.BudGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.K12 (P12)
open Desc.K14 (St)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof
open Johnson.M1 (BudOwed₂)
open Johnson.M1.BudW (take_guardRow)

/-- CONDITIONAL on hp, hr, hb and B. **THE DEBT GOES OVER TO THE SAME LIST WITH THE GUARD.** -/
theorem budOwed₂_guarded {Xi V W Y Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    (L L₀ : Lettered Bk F.S₂ F.Cl V W Y Pb) (hp : L.place = L₀.place)
    (hr : L.row = guardRow L₀.row) (hb : L.bud = L₀.bud) (B : BudOwed₂ F L₀) : BudOwed₂ F L := by
  intro σ hσ u hu pre t n hcut hn ρ hρ
  have hσ' := hσ
  unfold Lettered.side Side.seated at hσ'
  obtain ⟨b, hf, e⟩ := Option.map_eq_some_iff.1 hσ'
  let σ₀ : Side F.S₂ F.Cl V W Y Pb := ⟨b, L₀.row, fallOf [] L₀.place⟩
  have hσ₀ : L₀.side F.shared.blocksInOrder = some σ₀ := by
    unfold Lettered.side Side.seated
    show Option.map _ (F.shared.blocksInOrder.find? fun b => b.place == L₀.place) = _
    rw [← hp, hf]
    show some _ = some _
    rw [hp]
  have eb : σ.block = b := by rw [← e]
  have er : σ.row = guardRow L₀.row := by rw [← e]; exact hr
  have hm : σ.members = σ₀.members.map Member.guarded := by
    show membersOf σ.row 0 _ = _
    rw [er, membersOf_guardRow, eb]
    rfl
  rw [hm] at hu
  obtain ⟨u₀, hu₀, rfl⟩ := List.mem_map.1 hu
  have hTo : σ.roundsTo u₀.guarded.number = σ₀.roundsTo u₀.number := by
    unfold Side.roundsTo
    rw [er]
    show (((guardRow L₀.row).take u₀.number).map fun x => x.1.moves.length).sum = _
    rw [take_guardRow]
  rw [hb]
  exact B σ₀ hσ₀ u₀ hu₀ pre t n (by rw [hcut, eb]) (by rw [hn, hTo]) ρ hρ

/-- CONDITIONAL on h, hO, hp, hJ, hfr, ho and hL. **bud₂ AT THE LIST OF THE TEST ON G_omega, AT BOTH MEMBERS.** -/
theorem budOwed₂_at_O_guarded {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {pO : P12}
    (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) (hO : (fourOf Np).O = some pO) {W₀ : Type} {Bk : ProverCoinCounts}
    (J : TestJob (Common W₀ IndexCommitterCoins TableKey) Unit) (Js : SimJob TableKey) (hp : J.p = pO)
    (hJ : Js.p = pO) (hfr : J.fresh.isNone = true) (ho : Js.own = true)
    (L : Lettered Bk St ProofFile.Cl Empty (Common W₀ IndexCommitterCoins TableKey) Unit TableKey)
    (hL : IsListAtO L J Js) :
    BudOwed₂ (P5J.F0T o Zp Np cF) L :=
  budOwed₂_guarded (F := P5J.F0T o Zp Np cF) L { L with row := testPairs J Js } rfl hL.row rfl
    (AtO.budOwed₂_at_O h hO Js J hp hJ hfr ho { L with row := testPairs J Js } hL.place rfl hL.bud)

/-- CONDITIONAL on h, hO and hb. **THE SAME AT A LIST THAT TAKES ITS FOUR FIELDS FROM A ROW OF `lotAtOmega`.** -/
theorem budOwed₂_at_lot {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {pO : P12}
    (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) (hO : (fourOf Np).O = some pO)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : Desc.K14.blocks (VerifiableInference.Desc.K1.qAt Zp Np) =
      some [b1, b2, b3, b4, b5, b6, b7, b8]) {W₀ : Type} {Bk : ProverCoinCounts}
    (wt : ProofFile.Pub → W₀ → Weights) (Gr : ProofFile.Ground)
    (row : Unlettered Empty (Common W₀ IndexCommitterCoins TableKey) Unit TableKey)
    (hrow : row ∈ (lotAtOmega wt).rows Zp Gr)
    (L : Lettered Bk St ProofFile.Cl Empty (Common W₀ IndexCommitterCoins TableKey) Unit TableKey)
    (hpl : L.place = row.place) (hr : L.row = row.row) (hOn : L.On = row.On)
    (hbud : L.bud = row.bud) :
    BudOwed₂ (P5J.F0T o Zp Np cF) L := by
  have e := rowsAtOmega_at_head h hO b1 b2 b3 b4 b5 b6 b7 b8 hb (wt Zp)
  have hrow' : row ∈ rowsAtOmega (wt Zp) Zp := hrow
  rw [e] at hrow'
  obtain rfl := List.mem_singleton.1 hrow'
  exact budOwed₂_at_O_guarded h hO _ _ rfl rfl rfl rfl L ⟨hpl, hr, hOn, hbud⟩

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.budOwed₂_at_lot
#print axioms ProofFile.Honest.K12.Sim2.budOwed₂_guarded
#print axioms ProofFile.Honest.K12.Sim2.budOwed₂_at_O_guarded
