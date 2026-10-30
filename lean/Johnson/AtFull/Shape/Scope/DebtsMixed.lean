-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/DebtsMixed.lean: THE FIRST CHAIN's TWO DEBTS, MEMBER BY MEMBER, FROM EITHER OF TWO PAYMENTS: at
each member below 358 either the values with the family in hand (`ValuesJ`), or the two debts themselves
(`AcceptedJ` and `NextJ`), as a caller may have them by another road (a yes asked without the family gives
`AcceptedJ` by acceptedJ_of; where the table has the strong "carries", `NextJ` needs no values). Under the head, at
the table's own letters, at any thread over the chain's list. A joining; nothing is evaluated.

Limits. As RuleAtTable.lean's: the run on shapes and the test `halved` are premises; T, Said and fall are free
letters. Nothing says that either payment can be made at any member. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.RuleAtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open ProofFile.Honest (Shape Thread Coins Mid ProverCoinCounts ValuesJ NextJ AcceptedJ shapeJ halved fitsAt_of_halved
  nextJ_of_shapeV acceptedJ_of_shapeV)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- **THE TWO DEBTS AT ONE MEMBER, FROM ITS VALUES.** -/
theorem debts_at_member (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {V W X Pb : Type} {Bk : ProverCoinCounts}
    (T : Thread Bk S ProofFile.Cl V W X Pb) (hbs : T.bs = cF.blocksInOrder)
    (Said : Nat → Coins Bk → Mid W X → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String) (a₀ : ShA)
    (hyes : (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes a₀ 358 = true)
    (h4 : halved cF.blocksInOrder T.hs = true) {b : Nat} (hb : b < 358)
    (hV : ValuesJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀)
      (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) fall b) :
    AcceptedJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀) fall b ∧
      NextJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀) fall b :=
  ⟨acceptedJ_of_shapeV T Said _ hb hyes (by rw [hbs]; exact (table_all h hB b hb T.ft).2)
      (fitsAt_of_halved T (by rw [hbs]; exact h4) b) hV,
    nextJ_of_shapeV T Said _ hb hyes
      (by rw [hbs]; exact carriesU_of_V (table_all h hB b hb T.ft).1) hV⟩

/-- **THE FIRST CHAIN's TWO DEBTS, EACH MEMBER PAID IN ONE OF THE TWO WAYS.** -/
theorem debts_mixed (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {V W X Pb : Type} {Bk : ProverCoinCounts}
    (T : Thread Bk S ProofFile.Cl V W X Pb) (hbs : T.bs = cF.blocksInOrder)
    (Said : Nat → Coins Bk → Mid W X → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String) (a₀ : ShA)
    (hyes : (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes a₀ 358 = true)
    (h4 : halved cF.blocksInOrder T.hs = true)
    (hM : ∀ b, b < 358 →
      ValuesJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀)
          (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) fall b ∨
        (AcceptedJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀) fall b ∧
          NextJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀) fall b)) :
    (∀ b, b < T.bs.length →
        AcceptedJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀) fall b) ∧
      (∀ b, b < T.bs.length →
        NextJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀) fall b) := by
  have hl : T.bs.length = 358 := by rw [hbs]; exact flat_len h
  have key : ∀ b, b < T.bs.length →
      AcceptedJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀) fall b ∧
        NextJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀) fall b := by
    intro b hb
    rw [hl] at hb
    rcases hM b hb with hV | hD
    · exact debts_at_member h hB T hbs Said fall a₀ hyes h4 hb hV
    · exact hD
  exact ⟨fun b hb => (key b hb).1, fun b hb => (key b hb).2⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.debts_at_member
#print axioms Johnson.AtFull.Shape.debts_mixed
