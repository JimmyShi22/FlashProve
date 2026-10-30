-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFPol/HeadInScope.lean: the two tests on the plan of the output head's own block give one
verdict at two acceptance policies, if both policies are in the range that the goals' reader asks
and there are 2^10 positions. This pays the premise `HeadSame` of Johnson/LPFPol/Lots.lean.

The two tests. `Par.ok` (Johnson/Desc/Kinds/HeadFrame.lean) is `planOk`
(Johnson/Desc/Kinds/HeadOk.lean): `Policy.ok`, `Sizes.ranges` and the fifteen rows of `noOverflow`.
The three numbers C, theta, cap stand in `Policy.ok` and in the rows 9 to 11 (E2, E3, E4). `laidOk`
(Johnson/Stored/HeadSeatAt.lean) is the seventeen rows of `Laid.tests`
(Johnson/Desc/Kinds/HeadLaid.lean): C and theta stand in the rows 15 and 16 (clip, mean).

How. In the range, the tests that read the three numbers say yes. So each verdict is the verdict of
the other tests, which are the same terms at both policies.

Main names.
* `headSame_of`: THE LAW. Premises: own, W's own three numbers are in the range (theta ≤ C,
  cap ≤ 1024, C < 2^32); new, so are C, theta, cap; hT, the line lt is 10. Then
  `HeadSame W C theta cap`.
* `headSame_read`: the law at the goals' parameter files. Premises: h, `publicOfO secondHashFunction` returns X
  at `policyFile v`, KL, layout; hR and hR', the goals' reader (`settingsAtRef`,
  Johnson/Flat/SettingsRead.lean) returns at `policyFile v` and at
  `policyFile { v with C, theta, cap }`, each with some scale file. Then `HeadSame X C theta cap`.
* `planOk_part`, `laidOk_part`: in the range, each test is the conjunction of its other rows.
* `front_pol`, `back_pol`, `laidFront_pol`, `laidBack_pol`: these other rows are the same at two
  policies.
* `all_split`: a test on all members of a list, cut at two places.
* `lt_of_public`, `pol_of_public`: where `publicOf` returns X at `policyFile v`, the line lt in
  `X.hS` is 10, and the three numbers in `X.hS` are v's.

Limits.
* The law says that the verdicts are equal. It does not say that either is yes.
* Outside the range nothing is said. The range is sufficient; it is not shown to be necessary.
* In `headSame_read` the three returns are premises.
* Nothing on what the head's block decides. Nothing on soundness, on hiding or on a security level.

For proofs only; no program imports this file.


-/
import Johnson.LPFPol.Lots
import Johnson.LPFPol.PublicInScope

set_option autoImplicit false

namespace LPFPol

open OnBytes OnBytes.Model OnBytes.Model.Verify
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Norm (T)

/-- A test on all members of a list, cut behind a members and behind b more. -/
theorem all_split {α : Type} (p : α → Bool) (l : List α) (a b : Nat) :
    l.all p = ((l.take a).all p && (((l.drop a).take b).all p && (l.drop (a + b)).all p)) := by
  have e2 : (l.drop a).take b ++ l.drop (a + b) = l.drop a := by
    have e3 := List.take_append_drop b (l.drop a)
    rw [List.drop_drop] at e3
    exact e3
  have e : l.take a ++ ((l.drop a).take b ++ l.drop (a + b)) = l := by
    rw [e2, List.take_append_drop]
  conv => lhs; rw [← e]
  rw [List.all_append, List.all_append]

section
variable [Sizes] [Policy]

/-- In the range, the test on the plan is the conjunction of the tests that do not read the three
numbers. -/
theorem planOk_part (hT : T ≤ 2 ^ 16) (h1 : theta ≤ C) (h2 : cap ≤ T) (h3 : cap < 2 ^ 16)
    (h4 : C < 2 ^ 32) (sT : Nat) :
    planOk sT = (Sizes.ranges sT &&
      ((noOverflow.take 8).all (·.2.2) && (noOverflow.drop (8 + 3)).all (·.2.2))) := by
  have a : Policy.ok = true := by
    show (decide (theta ≤ C) && decide (cap ≤ T) && decide (cap < 2 ^ 16)) = true
    rw [decide_eq_true h1, decide_eq_true h2, decide_eq_true h3]
    rfl
  have m : ((noOverflow.drop 8).take 3).all (·.2.2) = true := by
    show (decide (T * (2 ^ 40 + 2 ^ 8 * C + 2 ^ 40) + theta * T < 2 ^ 60) &&
      (decide (T * (2 ^ 8 + 2 ^ 16) + cap < 2 ^ 60) &&
        (decide (2 ^ 40 + 2 ^ 40 + C < 2 ^ 60) && true))) = true
    rw [decide_eq_true (e2_bound hT h4 h1), decide_eq_true (by omega), decide_eq_true (by omega)]
    rfl
  unfold planOk
  rw [a, all_split _ noOverflow 8 3, m, Bool.true_and, Bool.true_and]

/-- Where C and theta are below 2^40, the tests on the laid numbers are the conjunction of those
that do not read them. -/
theorem laidOk_part (x : Laid) (h1 : C < 2 ^ 40) (h2 : theta < 2 ^ 40) :
    x.ok = ((x.tests.take 14).all (·.2) && (x.tests.drop (14 + 2)).all (·.2)) := by
  have m : ((x.tests.drop 14).take 2).all (·.2) = true := by
    show (decide (C < 2 ^ 40) && (decide (theta < 2 ^ 40) && true)) = true
    rw [decide_eq_true h1, decide_eq_true h2]
    rfl
  unfold Laid.ok
  rw [all_split _ x.tests 14 2, m, Bool.true_and]

end

/-- The first eight rows of `noOverflow` do not read the policy. -/
theorem front_pol (s : Sizes) (P P' : Policy) :
    (@noOverflow s P).take 8 = (@noOverflow s P').take 8 := by
  simp only [noOverflow, List.take_succ_cons, List.take_zero]

/-- Nor do its rows from the twelfth on. -/
theorem back_pol (s : Sizes) (P P' : Policy) :
    (@noOverflow s P).drop (8 + 3) = (@noOverflow s P').drop (8 + 3) := by
  simp only [noOverflow, Nat.reduceAdd, List.drop_succ_cons, List.drop_zero]

/-- The first fourteen rows of `Laid.tests` do not read the policy. -/
theorem laidFront_pol (s : Sizes) (P P' : Policy) (x : Laid) :
    (@Laid.tests s P x).take 14 = (@Laid.tests s P' x).take 14 := by
  simp only [Laid.tests, List.take_succ_cons, List.take_zero]

/-- Nor does its last row. -/
theorem laidBack_pol (s : Sizes) (P P' : Policy) (x : Laid) :
    (@Laid.tests s P x).drop (14 + 2) = (@Laid.tests s P' x).drop (14 + 2) := by
  simp only [Laid.tests, Nat.reduceAdd, List.drop_succ_cons, List.drop_zero]

/-- **THE LAW.** Premises: own, W's own three numbers are in the range; new, so are C, theta, cap;
hT, the line lt is 10. Then the two tests on the plan of the output head's own block give at C,
theta, cap what they give at W's own numbers. -/
theorem headSame_of {W : Public} {C theta cap : Nat}
    (own : W.hS.theta ≤ W.hS.clipC ∧ W.hS.cap ≤ 1024 ∧ W.hS.clipC < 2 ^ 32)
    (new : theta ≤ C ∧ cap ≤ 1024 ∧ C < 2 ^ 32) (hT : W.hS.lt = 10) :
    HeadSame W C theta cap where
  par w := by
    have t16 : (2 : Nat) ^ W.hS.lt ≤ 2 ^ 16 := by
      rw [hT]
      decide
    have tc : ∀ c : Nat, c ≤ 1024 → c ≤ 2 ^ W.hS.lt := fun c hc => by
      rw [hT]
      omega
    show @planOk (sizesOf W.hS) ⟨C, theta, cap⟩ W.hS.tabS =
      @planOk (sizesOf W.hS) ⟨W.hS.clipC, W.hS.theta, W.hS.cap⟩ W.hS.tabS
    rw [@planOk_part (sizesOf W.hS) ⟨C, theta, cap⟩ t16 new.1 (tc _ new.2.1)
        (Nat.lt_of_le_of_lt new.2.1 (by decide)) new.2.2,
      @planOk_part (sizesOf W.hS) ⟨W.hS.clipC, W.hS.theta, W.hS.cap⟩ t16 own.1 (tc _ own.2.1)
        (Nat.lt_of_le_of_lt own.2.1 (by decide)) own.2.2,
      front_pol (sizesOf W.hS) ⟨C, theta, cap⟩ ⟨W.hS.clipC, W.hS.theta, W.hS.cap⟩,
      back_pol (sizesOf W.hS) ⟨C, theta, cap⟩ ⟨W.hS.clipC, W.hS.theta, W.hS.cap⟩]
  laid := by
    have b : (2 : Nat) ^ 32 ≤ 2 ^ 40 := by decide
    show @Laid.ok (sizesOf W.hS) ⟨C, theta, cap⟩ (laidAt W.hS (borderOf W.y)) =
      @Laid.ok (sizesOf W.hS) ⟨W.hS.clipC, W.hS.theta, W.hS.cap⟩ (laidAt W.hS (borderOf W.y))
    rw [@laidOk_part (sizesOf W.hS) ⟨C, theta, cap⟩ _ (Nat.lt_of_lt_of_le new.2.2 b)
        (Nat.lt_of_le_of_lt new.1 (Nat.lt_of_lt_of_le new.2.2 b)),
      @laidOk_part (sizesOf W.hS) ⟨W.hS.clipC, W.hS.theta, W.hS.cap⟩ _
        (Nat.lt_of_lt_of_le own.2.2 b) (Nat.lt_of_le_of_lt own.1 (Nat.lt_of_lt_of_le own.2.2 b)),
      laidFront_pol (sizesOf W.hS) ⟨C, theta, cap⟩ ⟨W.hS.clipC, W.hS.theta, W.hS.cap⟩,
      laidBack_pol (sizesOf W.hS) ⟨C, theta, cap⟩ ⟨W.hS.clipC, W.hS.theta, W.hS.cap⟩]

/-! ### at the goals' parameter files -/

open VerifierAndGoals (FreeLines policyFile)
open VerifierAndGoals.Lines
open OnBytes.Flat (settingsAtRef)
open VerifiableInference.PlanWritten (publicOfO publicOfO_older)

/-- Where `publicOf` returns X at `policyFile v`, the line lt in the head's shape is 10. -/
theorem lt_of_public {v : FreeLines} {KL : ByteArray} {layout : Option ByteArray} {X : Public}
    (h : publicOf (policyFile v) KL layout = .ok X) : X.hS.lt = 10 := by
  have hP := publicOf_scan h
  have a : X.P.value "lt" = 10 := value_fixed hP (p := ("lt", 10)) (by decide)
  rw [publicOf_lt h, ConfigReaders.polScan_h hP]
  exact a

/-- Where `publicOf` returns X at `policyFile v`, the three numbers in the head's shape are v's. -/
theorem pol_of_public {v : FreeLines} {KL : ByteArray} {layout : Option ByteArray} {X : Public}
    (h : publicOf (policyFile v) KL layout = .ok X) :
    X.hS.clipC = v.C ∧ X.hS.theta = v.theta ∧ X.hS.cap = v.cap := by
  obtain ⟨a1, a2, a3⟩ := OnBytes.Tie.publicOf_hS h
  obtain ⟨-, -, -, -, c1, c2, c3⟩ := hdr_free (publicOf_scan h)
  exact ⟨a1.trans c1, a2.trans c2, a3.trans c3⟩

/-- **The law at the goals' parameter files.** Premises: h, `publicOfO secondHashFunction` returns X at
`policyFile v`, KL, layout; hR, hR', the goals' reader returns at `policyFile v` and at the same
file with the numbers C, theta, cap. -/
theorem headSame_read {v : FreeLines} {C theta cap : Nat} {KL KL1 KL2 : ByteArray}
    {layout : Option ByteArray} {X : Public} {pp pp' : Inst.Model.ScalesAndPolicy}
    (h : publicOfO secondHashFunction (policyFile v) KL layout = .ok X)
    (hR : settingsAtRef (policyFile v) KL1 = .ok pp)
    (hR' : settingsAtRef (policyFile { v with C := C, theta := theta, cap := cap }) KL2 = .ok pp') :
    HeadSame X C theta cap := by
  have h' : publicOf (policyFile v) KL layout = .ok X := by
    rw [← publicOfO_older]
    exact h
  obtain ⟨e1, e2, e3⟩ := pol_of_public h'
  obtain ⟨-, -, p1, p2, p3⟩ := premises_of_read hR
  obtain ⟨-, -, q1, q2, q3⟩ := premises_of_read hR'
  exact headSame_of (by rw [e1, e2, e3]; exact ⟨p1, p2, p3⟩) ⟨q1, q2, q3⟩ (lt_of_public h')

end LPFPol

#print axioms LPFPol.headSame_of
#print axioms LPFPol.headSame_read
