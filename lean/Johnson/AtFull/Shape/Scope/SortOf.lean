-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/SortOf.lean: ValuesFold.lean's FOLD, GENERAL IN WHAT IS LAID AT A MEMBER: `SortOf V`: a sentence V at
the 154 members at which the table has a test on values, a field a sort; `fold_of`: with V at the 204 others it gives
V at all 358. And its use at V b := "member b is paid": by its values with the family in hand, or by the two debts
themselves (DebtsMixed.lean): `PaidJ`, `debts_of_paid`. Joinings; nothing is evaluated.

Limits. NOTHING SAYS THAT A FIELD CAN BE MET. debts_of_paid keeps the run on shapes and the test `halved` as premises;
RuleAtTable.lean's Limits are inherited. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.ValuesFold
import Johnson.AtFull.Shape.Scope.DebtsMixed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open ProofFile.Honest (Shape Thread Coins Mid ProverCoinCounts ValuesJ NextJ AcceptedJ shapeJ halved)

/-- **A sentence at the 154 members at which the table has a test on values, a field a sort.** -/
structure SortOf (V : Nat → Prop) : Prop where
  switch : ∀ l, 0 < l → l < 24 → V (14 * l + 1 + 1)
  layers : ∀ l, l < 24 → l % 2 = 0 → V (14 * l + 3 + 1)
  readsAtt : ∀ l, l < 24 → l % 2 = 1 → V (14 * l + 4 + 1)
  batch : ∀ l, l < 24 → V (14 * l + 8 + 1)
  behind : ∀ l, l < 24 → V (14 * l + 9 + 1)
  equation : ∀ l, l < 24 → V (14 * l + 10 + 1)
  close : ∀ l, l < 24 → V (14 * l + 11 + 1)
  reply : V (337 + 1)
  switchHead : V (337 + 2)
  head : V (337 + 4)
  readsHead : V (337 + 5)
  lookHead : V (337 + 8)
  batchHead : V (337 + 10)
  behindHead : V (337 + 11)
  equationHead : V (337 + 12)
  closeHead : V (337 + 13)
  finish : V (353 + 0)
  test : V (353 + 1)

/-- **THE FOLD.** -/
theorem fold_of {V : Nat → Prop} (hP : ∀ b, b < 358 → plainV b = true → V b) (H : SortOf V) (b : Nat)
    (hb : b < 358) : V b := by
  by_cases hp : plainV b = true
  · exact hP b hb hp
  · unfold plainV at hp
    rcases number_cases hb with rfl | ⟨l, j, hl, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · exact absurd rfl hp
    · rw [table_link _ _ _ _ l j hl hj] at hp
      interval_cases j
      · exact absurd rfl hp
      · refine H.switch l (Nat.pos_of_ne_zero fun e => hp ?_) hl
        subst e
        rfl
      · exact absurd rfl hp
      · refine H.layers l hl ?_
        have : ¬ l % 2 = 1 := fun e => hp (show (l % 2 == 1) = true from by simp [e])
        omega
      · refine H.readsAtt l hl ?_
        have : ¬ l % 2 = 0 := fun e => hp (show (l % 2 == 0) = true from by simp [e])
        omega
      · exact absurd rfl hp
      · exact absurd rfl hp
      · exact absurd rfl hp
      · exact H.batch l hl
      · exact H.behind l hl
      · exact H.equation l hl
      · exact H.close l hl
      · exact absurd rfl hp
      · exact absurd rfl hp
    · rw [table_head _ _ _ _ j hj] at hp
      interval_cases j
      · exact absurd rfl hp
      · exact H.reply
      · exact H.switchHead
      · exact absurd rfl hp
      · exact H.head
      · exact H.readsHead
      · exact absurd rfl hp
      · exact absurd rfl hp
      · exact H.lookHead
      · exact absurd rfl hp
      · exact H.batchHead
      · exact H.behindHead
      · exact H.equationHead
      · exact H.closeHead
      · exact absurd rfl hp
      · exact absurd rfl hp
    · rw [table_back _ _ _ _ j] at hp
      interval_cases j
      · exact H.finish
      · exact H.test
      · exact absurd rfl hp
      · exact absurd rfl hp
      · exact absurd rfl hp

/-- A field-wise step from one sentence to another. -/
theorem SortOf.mono {V V' : Nat → Prop} (h : ∀ b, V b → V' b) (H : SortOf V) : SortOf V' where
  switch := fun l h0 hl => h _ (H.switch l h0 hl)
  layers := fun l hl he => h _ (H.layers l hl he)
  readsAtt := fun l hl ho => h _ (H.readsAtt l hl ho)
  batch := fun l hl => h _ (H.batch l hl)
  behind := fun l hl => h _ (H.behind l hl)
  equation := fun l hl => h _ (H.equation l hl)
  close := fun l hl => h _ (H.close l hl)
  reply := h _ H.reply
  switchHead := h _ H.switchHead
  head := h _ H.head
  readsHead := h _ H.readsHead
  lookHead := h _ H.lookHead
  batchHead := h _ H.batchHead
  behindHead := h _ H.behindHead
  equationHead := h _ H.equationHead
  closeHead := h _ H.closeHead
  finish := h _ H.finish
  test := h _ H.test

/-- **"Member b is paid"**: by its values with the family in hand, or by the two debts themselves. -/
def PaidJ {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S ProofFile.Cl V W X Pb)
    (Said : Nat → Coins Bk → Mid W X → Prop) (J : Nat → S → Prop) (Zs : Shape S)
    (fall : Nat → S → List Fmt.Drawn → Option String) (b : Nat) : Prop :=
  ValuesJ T Said J Zs fall b ∨ (AcceptedJ T Said J fall b ∧ NextJ T Said J fall b)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- **THE FIRST CHAIN's TWO DEBTS FROM THE RUN ON SHAPES, ONE TEST WITH CODE, AND EACH SORT PAID IN ONE OF THE TWO
WAYS.** -/
theorem debts_of_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {V W X Pb : Type} {Bk : ProverCoinCounts}
    (T : Thread Bk S ProofFile.Cl V W X Pb) (hbs : T.bs = cF.blocksInOrder)
    (Said : Nat → Coins Bk → Mid W X → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String)
    (hyes : (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes startShA 358 = true)
    (h4 : halved cF.blocksInOrder T.hs = true)
    (H : SortOf (PaidJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) startShA)
      (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) fall)) :
    (∀ b, b < T.bs.length →
        AcceptedJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) startShA) fall b) ∧
      (∀ b, b < T.bs.length →
        NextJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) startShA) fall b) :=
  debts_mixed h hB T hbs Said fall startShA hyes h4
    (fold_of (fun _ hb hp => Or.inl (valuesJ_plain hb hp)) H)

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.fold_of
#print axioms Johnson.AtFull.Shape.SortOf.mono
#print axioms Johnson.AtFull.Shape.debts_of_paid
