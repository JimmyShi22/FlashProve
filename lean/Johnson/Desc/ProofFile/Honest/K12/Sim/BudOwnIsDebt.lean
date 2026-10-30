-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/BudOwnIsDebt.lean: `bud_first_O` (Sim/BudOwnAtHead.lean) in
the letters of the structure `BudDebts` (Johnson/Desc/ProofFile/Honest/Law/OwedRule.lean), which
goes with the frame: under the library's head (`P5J.AtMg`, Johnson/P5J/AtMg.lean), at a list of
parts (`Lettered`, Johnson/Desc/ProofFile/Honest/Rule.lean) that stands at the seated place of the
proximity test on G_omega, whose row is `testPairs J Js` and whose bud is `testBud Js`
(Sim/Row.lean). It imports Mathlib.

  `side_is_testSide`   such a list's side off a list of sub-protocols is `testSide` at no fall
  `debt_first_O`   the body of the field `bud₂` at that list, at the members whose number is 0
  `debt_row_O`   the body of the field `bud₂` at that list, at all its members: from the same clause
                 at the second member, which is a premise
  `budDebts_one_row`   the structure `BudDebts` itself, at the sides whose one list is that list:
                 from the same premise

So of this row's debt the first member's clause is paid, and the second member's is not: it stays a
premise (`budRest`, Sim/Row.lean, is not treated).

Limits.
- The sides in `budDebts_one_row` hold one list: they are no prover's sides of the whole file. The
  statement is there so that Lean itself holds the clause against the structure's text.
- The second member's clause is shown nowhere.
- Law/OwedRule.lean and the files that it imports go with the frame; this file says nothing on them.
- All limits of Sim/BudOwnAtHead.lean stand. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.BudOwnAtHead
import Johnson.Desc.ProofFile.Honest.Law.OwedRule

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (P12)
open Desc.K14 (St)
open ProofFile.Honest.K12.AtProof (fourOf)

variable {S Cl V W X Pb : Type}

theorem side_is_testSide {Bk : ProverCoinCounts} (L : Lettered Bk S Cl V W X Pb) (J : TestJob W X)
    (Js : SimJob Pb) (hpl : L.place = J.p.place) (hrow : L.row = testPairs J Js)
    (bs : List (Block S Cl)) : L.side bs = testSide bs J Js [] := by
  unfold Lettered.side testSide
  rw [hpl, hrow]

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {pO : P12}

section Row
variable (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) (Js : SimJob Pb)
  (J : TestJob W X) (hp : J.p = pO) (hJ : Js.p = pO) {Bk : ProverCoinCounts}
  (L : Lettered Bk (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl V W X Pb)
  (hpl : L.place = J.p.place)
  (hrow : L.row = testPairs J Js) (hbud : L.bud = testBud Js)

include h hO hp hJ hpl hrow hbud in
/-- **The field's body at the members whose number is 0.** -/
theorem debt_first_O : ∀ σ, L.side (P5J.F0T o Zp Np cF).shared.blocksInOrder = some σ → ∀ u ∈ σ.members,
    u.number = 0 → ∀ pre t n, (P5J.F0T o Zp Np cF).shared.blocksInOrder = pre ++ σ.block :: t →
    n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws,
    ρ.due (P5J.F0T o Zp Np cF) = true →
    L.bud u.number ((ρ.shared.drop n).take u.rounds.length)
      (asksFrom (treeAsks (P5J.F0T o Zp Np cF) ρ 1) (u.rounds.map (·.2.length))
        (((rowsOfChain (P5J.F0T o Zp Np cF).shared.blocksInOrder).take n).map (·.2.length)).sum) := by
  intro σ hσ u hu h0 pre t n hcut hn ρ hρ
  have hσ' : testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder J Js [] = some σ :=
    (side_is_testSide L J Js hpl hrow _).symm.trans hσ
  have hm : σ.members = [firstMember J Js, restMember J Js] :=
    (seated_at_O h hO Js J hp hJ [] σ hσ').2
  rw [hm] at hu
  rcases List.mem_cons.1 hu with rfl | hu
  · rw [hbud]
    exact bud_first_O h hO Js J hp hJ [] σ hσ' pre t n hcut hn ρ hρ
  · obtain rfl := List.mem_singleton.1 hu
    exact absurd h0 Nat.one_ne_zero

include h hO hp hJ hpl hrow hbud in
/-- **The field's body at all members of the list**, from the clause at the second member. -/
theorem debt_row_O
    (hrest : ∀ σ, L.side (P5J.F0T o Zp Np cF).shared.blocksInOrder = some σ → ∀ u ∈ σ.members, u.number = 1 →
      ∀ pre t n, (P5J.F0T o Zp Np cF).shared.blocksInOrder = pre ++ σ.block :: t →
      n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws,
      ρ.due (P5J.F0T o Zp Np cF) = true →
      L.bud u.number ((ρ.shared.drop n).take u.rounds.length)
        (asksFrom (treeAsks (P5J.F0T o Zp Np cF) ρ 1) (u.rounds.map (·.2.length))
          (((rowsOfChain (P5J.F0T o Zp Np cF).shared.blocksInOrder).take n).map (·.2.length)).sum)) :
    ∀ σ, L.side (P5J.F0T o Zp Np cF).shared.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
    (P5J.F0T o Zp Np cF).shared.blocksInOrder = pre ++ σ.block :: t →
    n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws,
    ρ.due (P5J.F0T o Zp Np cF) = true →
    L.bud u.number ((ρ.shared.drop n).take u.rounds.length)
      (asksFrom (treeAsks (P5J.F0T o Zp Np cF) ρ 1) (u.rounds.map (·.2.length))
        (((rowsOfChain (P5J.F0T o Zp Np cF).shared.blocksInOrder).take n).map (·.2.length)).sum) := by
  intro σ hσ u hu
  have hσ' : testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder J Js [] = some σ :=
    (side_is_testSide L J Js hpl hrow _).symm.trans hσ
  have hm : σ.members = [firstMember J Js, restMember J Js] :=
    (seated_at_O h hO Js J hp hJ [] σ hσ').2
  have hu' := hu
  rw [hm] at hu'
  rcases List.mem_cons.1 hu' with e | e
  · exact debt_first_O h hO Js J hp hJ L hpl hrow hbud σ hσ u hu (by rw [e]; rfl)
  · exact hrest σ hσ u hu (by rw [List.mem_singleton.1 e]; rfl)

end Row

/-- **The structure itself, at the sides whose one list is that list**, from the clause at the
second member. -/
theorem budDebts_one_row {W₀ Rc Ky Tr X₀ Y : Type} (h : P5J.AtMg o Z D r Zp Np cF)
    (hO : (fourOf Np).O = some pO) (Js : SimJob Ky) (J : TestJob (Common W₀ Rc Ky) X₀)
    (hp : J.p = pO) (hJ : Js.p = pO) {Bk : ProverCoinCounts}
    (L : Lettered Bk (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (hpl : L.place = J.p.place) (hrow : L.row = testPairs J Js) (hbud : L.bud = testBud Js)
    (hrest : ∀ σ, L.side (P5J.F0T o Zp Np cF).shared.blocksInOrder = some σ → ∀ u ∈ σ.members, u.number = 1 →
      ∀ pre t n, (P5J.F0T o Zp Np cF).shared.blocksInOrder = pre ++ σ.block :: t →
      n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws,
      ρ.due (P5J.F0T o Zp Np cF) = true →
      L.bud u.number ((ρ.shared.drop n).take u.rounds.length)
        (asksFrom (treeAsks (P5J.F0T o Zp Np cF) ρ 1) (u.rounds.map (·.2.length))
          (((rowsOfChain (P5J.F0T o Zp Np cF).shared.blocksInOrder).take n).map (·.2.length)).sum)) :
    BudDebts (P5J.F0T o Zp Np cF) Bk
      ({ first := [], shared := [L], second := [] } :
        Sides (P5J.F0T o Zp Np cF) Bk W₀ Rc Ky Tr X₀ Y) where
  bud₁ := fun _ hL => absurd hL List.not_mem_nil
  bud₂ := fun L' hL' => by
    obtain rfl := List.mem_singleton.1 hL'
    exact debt_row_O h hO Js J hp hJ L' hpl hrow hbud hrest
  bud₃ := fun _ hL => absurd hL List.not_mem_nil

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.side_is_testSide
#print axioms ProofFile.Honest.K12.Light.debt_first_O
#print axioms ProofFile.Honest.K12.Light.debt_row_O
#print axioms ProofFile.Honest.K12.Light.budDebts_one_row
