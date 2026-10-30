-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/PlanK6AtAll.lean: THE TYPED TEST planK6C (Law/PlanK6ByBlocks.lean) AT THE
TERMS OF THE COMPOSED MEANING's CONSTANT (Johnson/P5J/LettersAt.lean: At.cs, At.arr, At.ms, At.N,
At.X, At.layout, At.num) IS THE CHEAP PUBLIC TEST planK6AtZ Zp
(Johnson/Desc/Kinds/HeadDoorAtZ.lean). Theorems.
The sister of Law/PadsFreeAtAll.lean.

What is proved.
  k6Row_atR          the first test at arr := arrOf (planSeatsAll Z Z.D), num := numOfPlan (the
          same), any numbers N whose groups and whose list sent 24 0 are numbersOf (planSeats Z
          Z.D.1)'s, and the members by the make off the plan's seats (P5T.msAtR Z rad, at any radii)
          is planK6AtZ Z. By memsSame_atR (Johnson/P5T/MembersByMake.lean): NO
          PREMISE ON THE MEMBERS.
  **planK6C_atTerms**   planK6C (At.cs Zp) (At.arr Zp) (At.ms Zp lay) (At.N Zp cF) (At.X Zp)
          (At.layout Zp) (At.num Zp) (At.num Zp 24 0) 0 = planK6AtZ Zp: AN EQUATION, for every Zp,
          cF, lay.
  planK6C_atAll      so planK6AtZ Zp = true gives that typed test's accept at the constant's terms.
  **planK6_atAll**      under the one head (h : P5J.AtMg o Z D r Zp Np cF) and planK6AtZ Zp = true:
          the four clauses of PlanK6 that planK6_of_row gives (named, seats, maskNamed, maskIn), at
          the constant's terms. laidThere is the head's own h.plan.laid.

No existential quantifier.
Not proved here. planK6AtZ Zp = true: a test with code; in the goals' scope it is a theorem under
four premises (Goal/Meaning/HeadTestsScope.lean). The head is a premise. PlanK6's two other fields
(made, follows). Nothing on soundness.

-/
import Johnson.Desc.Kinds.Law.PadsFreeAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (namedOnce)
open OnBytes.Model.Verify (borderOf)
open P5T (planSeats planSeatsAll numbersOf arrOf numOfPlan msAtR memsSame_atR)

/-- The first test at the members by the make off the plan's seats. -/
theorem k6Row_atR (Z : ProofFile.Pub) (rad : ℕ → ℕ → ℕ) (N : Numbers)
    (hN : N.group = (numbersOf (planSeats Z Z.D.1)).group)
    (hS : N.sent 24 0 = (numbersOf (planSeats Z Z.D.1)).sent 24 0) :
    planK6Row Z (lettersOf (arrOf (planSeatsAll Z Z.D)) (numOfPlan (planSeatsAll Z Z.D)) N
      (msAtR Z rad)) = planK6AtZ Z := by
  unfold planK6AtZ planK6Row lettersOf lettersAt
  dsimp only
  rw [hN, hS]
  exact k6Door_mems _ _ _ _ _ _ _ _ _ _ (memsSame_atR Z rad) _ _

/-- **The typed test at the constant's terms is the cheap test.** -/
theorem planK6C_atTerms (Zp : ProofFile.Pub) (cF : Chain P5J.TS ProofFile.Cl) (lay : ByteArray) :
    planK6C (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp lay) (P5J.At.N Zp cF) (P5J.At.X Zp)
      (P5J.At.layout Zp) (P5J.At.num Zp) (P5J.At.num Zp 24 0) 0 = planK6AtZ Zp :=
  (planK6C_door (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp lay) (P5J.At.N Zp cF) (P5J.At.X Zp)
    (P5J.At.layout Zp) (P5J.At.num Zp) (P5J.At.num Zp 24 0) 0).trans
    (k6Row_atR Zp (P5J.At.rad Zp lay) (P5J.At.N Zp cF) rfl rfl)

theorem planK6C_atAll (Zp : ProofFile.Pub) (cF : Chain P5J.TS ProofFile.Cl) (lay : ByteArray)
    (hp : planK6AtZ Zp = true) :
    planK6C (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp lay) (P5J.At.N Zp cF) (P5J.At.X Zp)
      (P5J.At.layout Zp) (P5J.At.num Zp) (P5J.At.num Zp 24 0) 0 = true :=
  (planK6C_atTerms Zp cF lay).trans hp

/-- **PlanK6's four clauses at the constant's terms, under the one head.** -/
theorem planK6_atAll {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    (h : P5J.AtMg o Z D r Zp Np cF) (hp : planK6AtZ Zp = true) :
    (∀ (μ : Fin (Meaning.sizesOf (P5J.At.X Zp) 24).NM) (r c : Nat),
      r < Alg.symRows ((Meaning.sizesOf (P5J.At.X Zp) 24).m μ) →
      c < (Meaning.sizesOf (P5J.At.X Zp) 24).k μ →
      ColFour (P5J.At.X Zp).hS (P5J.At.X Zp).HLy (borderOf (P5J.At.X Zp).y) μ.val c →
      namedOnce (P5J.At.arr Zp) (P5J.At.N Zp cF) 24
        (seatLay (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp) 24 μ r c).1 = true) ∧
    (∀ (μ : Fin (Meaning.sizesOf (P5J.At.X Zp) 24).NM) (r c : Nat),
      r < Alg.symRows ((Meaning.sizesOf (P5J.At.X Zp) 24).m μ) →
      c < (Meaning.sizesOf (P5J.At.X Zp) 24).k μ →
      ColFour (P5J.At.X Zp).hS (P5J.At.X Zp).HLy (borderOf (P5J.At.X Zp).y) μ.val c →
      InCopy (P5J.At.cs Zp) (P5J.At.arr Zp) (ms0 (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF))
        (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) 24
        (seatLay (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp) 24 μ r c).1 false
        (seatLay (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp) 24 μ r c).2.1
        (seatLay (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp) 24 μ r c).2.2) ∧
    (∀ j, j < (P5J.At.X Zp).H.ns →
      namedOnce (P5J.At.arr Zp) (P5J.At.N Zp cF) 24 (plAt (P5J.At.num Zp 24 0) 0 j).1 = true) ∧
    (∀ j, j < (P5J.At.X Zp).H.ns →
      InCopy (P5J.At.cs Zp) (P5J.At.arr Zp) (ms0 (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF))
        (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) 24 (plAt (P5J.At.num Zp 24 0) 0 j).1
        (plAt (P5J.At.num Zp 24 0) 0 j).2.1 (plAt (P5J.At.num Zp 24 0) 0 j).2.2.1
        (plAt (P5J.At.num Zp 24 0) 0 j).2.2.2) :=
  planK6_of_row Zp (P5J.At.arr Zp) (P5J.At.num Zp) (P5J.At.N Zp cF) (P5J.At.ms Zp Z.lay)
    ((k6Row_atR Zp (P5J.At.rad Zp Z.lay) (P5J.At.N Zp cF) rfl rfl).trans hp) h.plan.laid

end VerifiableInference.Desc.Kinds.Head.Law.OffPad

#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.k6Row_atR
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.planK6C_atTerms
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.planK6C_atAll
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.planK6_atAll
