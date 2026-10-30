--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/SplitSays.lean: the value of the scalar that an honest prover sends at
"SPLIT", and that the two constraints which "SPLIT" lays hold of the prover's words.

"SPLIT" has a round only where the messages o_u and o_omega have two codes. There it cuts the
constraint (fold), which reads messages of two groups, in two: with kappa, an entry of the mask
message, and mu, the scalar that the prover sends:
  on G_omega: (its part) + kappa = mu;   on G_u: (its part) - kappa = (fold)'s target - mu.
With one code (fold) goes whole to the one group and no scalar is sent: that case is not treated.
The honest mu reads as the left side of the first constraint, applied to the words. Then the first
constraint holds because mu is defined so, and the second holds because the two add up to (fold),
which holds.

  value_sameCoeffs, value_add   a constraint applied to words reads the coefficients alone, and is
                  additive in them
  says_third      of three constraints of which two add up to the third: the sum and one summand
                  hold, so the other holds
  muVal           the honest scalar's value, an element of the field K; written out: muVal_formula
                  (Johnson/Desc/K14/Honest/SplitValue.lean)
  says_onOmega, says_onU, says_split   the two constraints hold
  onTable_addUnit, value_addUnit, muVal_eq   the value is its group's part of (fold), applied to the
                  words, plus the mask's entry

What is assumed, as premises. hmu: the element mu of the program's field that is sent reads as
muVal. says_onOmega is that premise in other words. Such an element exists where the reading is
onto: at Reading.gl by toE_ofE (OnBytes/Slice/Field.lean); not at every reading. hrow: (fold) holds
of the words. In muVal_eq alone: the mask message is there and kappa lies within its mask table;
outside the table both constraints still hold and the value is the bare part of (fold).
The statement T, the constraint, the list of members and kappa are free variables. Whoever calls
these theorems at a state owes what Johnson/Desc/Means/Says.lean asks of a law over Says: that the
row has passed the tests at the statement in force.
What is not claimed. Nothing on a verifier's decision, on soundness or on hiding.

-/
import Johnson.Desc.K14.Law.Lays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Means (Words)
open Desc.K14.Law

variable {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)

/-! ## A constraint applied to words -/

/-- Two constraints with the same coefficients give the same, applied to words. -/
theorem value_sameCoeffs (T : Statement) (a b : Row)
    (h : ∀ o pt i, a.coefficient o pt i = b.coefficient o pt i) (m : Words K) :
    Means.value ρ T a m = Means.value ρ T b m := by
  unfold Means.value Means.onTable
  simp only [h]

/-- Two constraints that add up to a third, entry by entry: so do they, applied to words. -/
theorem value_add (T : Statement) (a b row : Row)
    (hc : ∀ o pt i, ρ.val (a.coefficient o pt i) + ρ.val (b.coefficient o pt i) =
      ρ.val (row.coefficient o pt i)) (m : Words K) :
    Means.value ρ T a m + Means.value ρ T b m = Means.value ρ T row m := by
  have key : ∀ o pt, Means.onTable ρ T a m o pt + Means.onTable ρ T b m o pt =
      Means.onTable ρ T row m o pt := by
    intro o pt
    unfold Means.onTable
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hc o pt i]
    ring
  unfold Means.value
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [← key o .main, ← key o .mask]
  ring

/-- Two constraints add up to a third, entry by entry and in the targets. The third and the first
hold of words: so the second holds. -/
theorem says_third (T : Statement) (a b row : Row)
    (hc : ∀ o pt i, ρ.val (a.coefficient o pt i) + ρ.val (b.coefficient o pt i) =
      ρ.val (row.coefficient o pt i))
    (ht : ρ.val a.target + ρ.val b.target = ρ.val row.target) (m : Words K)
    (hr : Means.Says ρ T row m) (ha : Means.Says ρ T a m) : Means.Says ρ T b m := by
  have h := value_add ρ T a b row hc m
  unfold Means.Says at hr ha ⊢
  linear_combination h + hr - ha - ht

/-! ## The honest scalar -/

/-- **The honest scalar at "SPLIT"**: the left side of the constraint on G_omega, applied to the
words. The target that is written here is not read. -/
def muVal (T : Statement) (row : Row) (members : Array Nat) (oSp kappa : Nat) (m : Words K) : K :=
  Means.value ρ T (onOmega row members oSp kappa zeroE) m

/-- The constraint on G_omega holds: this is the premise hmu in other words. -/
theorem says_onOmega (T : Statement) (row : Row) (members : Array Nat) (oSp kappa : Nat) (mu : E)
    (m : Words K) (hmu : ρ.val mu = muVal ρ T row members oSp kappa m) :
    Means.Says ρ T (onOmega row members oSp kappa mu) m := by
  have e : Means.value ρ T (onOmega row members oSp kappa mu) m =
      Means.value ρ T (onOmega row members oSp kappa zeroE) m :=
    value_sameCoeffs ρ T _ _ (fun _ _ _ => rfl) m
  show Means.value ρ T (onOmega row members oSp kappa mu) m = ρ.val mu
  rw [e, hmu]
  rfl

/-- The constraint on G_u holds, if (fold) does. -/
theorem says_onU (T : Statement) (row : Row) (members : Array Nat) (oSp kappa : Nat) (mu : E)
    (m : Words K) (hmu : ρ.val mu = muVal ρ T row members oSp kappa m)
    (hrow : Means.Says ρ T row m) : Means.Says ρ T (onU row members oSp kappa mu) m :=
  says_third ρ T _ _ row (split_coefficient ρ row members oSp kappa mu)
    (split_target ρ row members oSp kappa mu) m hrow
    (says_onOmega ρ T row members oSp kappa mu m hmu)

/-- **Both constraints that "SPLIT" lays hold of the words**, at the honest scalar, if (fold) holds
of them. -/
theorem says_split (T : Statement) (row : Row) (members : Array Nat) (oSp kappa : Nat) (mu : E)
    (m : Words K) (hmu : ρ.val mu = muVal ρ T row members oSp kappa m)
    (hrow : Means.Says ρ T row m) :
    Means.Says ρ T (onOmega row members oSp kappa mu) m ∧
      Means.Says ρ T (onU row members oSp kappa mu) m :=
  ⟨says_onOmega ρ T row members oSp kappa mu m hmu,
    says_onU ρ T row members oSp kappa mu m hmu hrow⟩

/-! ## The honest scalar, written out -/

/-- A coefficient more on one entry, applied to one table of the words. -/
theorem onTable_addUnit (T : Statement) (r : Row) (o' : Nat) (p' : Part) (i' : Nat) (c : E)
    (m : Words K) (o : Nat) (pt : Part) :
    Means.onTable ρ T (r.addUnit o' p' i' c) m o pt =
      Means.onTable ρ T r m o pt +
        if o' = o ∧ p' = pt ∧ i' < Means.tableSize T o pt then ρ.val c * m o pt i' else 0 := by
  unfold Means.onTable
  have e0 : ∀ i ∈ Finset.range (Means.tableSize T o pt),
      ρ.val ((r.addUnit o' p' i' c).coefficient o pt i) * m o pt i =
        ρ.val (r.coefficient o pt i) * m o pt i +
          (if i' = i then (if o' = o ∧ p' = pt then ρ.val c * m o pt i else 0) else 0) := by
    intro i _
    rw [coefficient_addUnit, add_mul]
    congr 1
    by_cases h3 : i' = i
    · by_cases h12 : o' = o ∧ p' = pt
      · have a : o' = o ∧ p' = pt ∧ i' = i := ⟨h12.1, h12.2, h3⟩
        rw [if_pos a, if_pos h3, if_pos h12]
      · have a : ¬ (o' = o ∧ p' = pt ∧ i' = i) := fun e => h12 ⟨e.1, e.2.1⟩
        rw [if_neg a, if_pos h3, if_neg h12, zero_mul]
    · have a : ¬ (o' = o ∧ p' = pt ∧ i' = i) := fun e => h3 e.2.2
      rw [if_neg a, if_neg h3, zero_mul]
  rw [Finset.sum_congr rfl e0, Finset.sum_add_distrib, Finset.sum_ite_eq]
  congr 1
  by_cases h3 : i' < Means.tableSize T o pt
  · rw [if_pos (Finset.mem_range.2 h3)]
    by_cases h12 : o' = o ∧ p' = pt
    · have a : o' = o ∧ p' = pt ∧ i' < Means.tableSize T o pt := ⟨h12.1, h12.2, h3⟩
      rw [if_pos h12, if_pos a]
    · have a : ¬ (o' = o ∧ p' = pt ∧ i' < Means.tableSize T o pt) := fun e => h12 ⟨e.1, e.2.1⟩
      rw [if_neg h12, if_neg a]
  · have a : ¬ i' ∈ Finset.range (Means.tableSize T o pt) := fun e => h3 (Finset.mem_range.1 e)
    have b : ¬ (o' = o ∧ p' = pt ∧ i' < Means.tableSize T o pt) := fun e => h3 e.2.2
    rw [if_neg a, if_neg b]

/-- A coefficient more on one entry of a table that is there, applied to the words. -/
theorem value_addUnit (T : Statement) (r : Row) (o' : Nat) (p' : Part) (i' : Nat) (c : E)
    (m : Words K) (ho : o' < T.oracles.size) (hi : i' < Means.tableSize T o' p') :
    Means.value ρ T (r.addUnit o' p' i' c) m = Means.value ρ T r m + ρ.val c * m o' p' i' := by
  unfold Means.value
  have e0 : ∀ o ∈ Finset.range T.oracles.size,
      Means.onTable ρ T (r.addUnit o' p' i' c) m o .main +
        Means.onTable ρ T (r.addUnit o' p' i' c) m o .mask =
      (Means.onTable ρ T r m o .main + Means.onTable ρ T r m o .mask) +
        (if o' = o then ρ.val c * m o' p' i' else 0) := by
    intro o _
    rw [onTable_addUnit, onTable_addUnit]
    by_cases h1 : o' = o
    · subst h1
      have a0 : o' = o' := rfl
      rw [if_pos a0]
      cases p' with
      | main =>
        have a1 : o' = o' ∧ Part.main = Part.main ∧ i' < Means.tableSize T o' .main :=
          ⟨rfl, rfl, hi⟩
        have a2 : ¬ (o' = o' ∧ Part.main = Part.mask ∧ i' < Means.tableSize T o' .mask) :=
          fun e => by cases e.2.1
        rw [if_pos a1, if_neg a2]
        ring
      | mask =>
        have a1 : o' = o' ∧ Part.mask = Part.mask ∧ i' < Means.tableSize T o' .mask :=
          ⟨rfl, rfl, hi⟩
        have a2 : ¬ (o' = o' ∧ Part.mask = Part.main ∧ i' < Means.tableSize T o' .main) :=
          fun e => by cases e.2.1
        rw [if_neg a2, if_pos a1]
        ring
    · have a1 : ¬ (o' = o ∧ p' = Part.main ∧ i' < Means.tableSize T o .main) := fun e => h1 e.1
      have a2 : ¬ (o' = o ∧ p' = Part.mask ∧ i' < Means.tableSize T o .mask) := fun e => h1 e.1
      rw [if_neg a1, if_neg a2, if_neg h1]
      ring
  rw [Finset.sum_congr rfl e0, Finset.sum_add_distrib, Finset.sum_ite_eq,
    if_pos (Finset.mem_range.2 ho)]

/-- **The honest scalar is its group's part of (fold), applied to the words, plus the mask's
entry.** -/
theorem muVal_eq (T : Statement) (row : Row) (members : Array Nat) (oSp kappa : Nat) (m : Words K)
    (ho : oSp < T.oracles.size) (hk : kappa < Means.tableSize T oSp .mask) :
    muVal ρ T row members oSp kappa m =
      Means.value ρ T (part row members true) m + m oSp .mask kappa := by
  have e : Means.value ρ T (onOmega row members oSp kappa zeroE) m =
      Means.value ρ T ((part row members true).addUnit oSp .mask kappa oneE) m :=
    value_sameCoeffs ρ T _ _ (fun _ _ _ => rfl) m
  unfold muVal
  rw [e, value_addUnit ρ T _ oSp .mask kappa oneE m ho hk, ρ.one, one_mul]

end Desc.K14.Honest

#print axioms Desc.K14.Honest.value_sameCoeffs
#print axioms Desc.K14.Honest.value_add
#print axioms Desc.K14.Honest.says_third
#print axioms Desc.K14.Honest.says_onOmega
#print axioms Desc.K14.Honest.says_onU
#print axioms Desc.K14.Honest.says_split
#print axioms Desc.K14.Honest.onTable_addUnit
#print axioms Desc.K14.Honest.value_addUnit
#print axioms Desc.K14.Honest.muVal_eq
