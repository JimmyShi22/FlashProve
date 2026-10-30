-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/PadsFreeAtAll.lean: P5J.PadsFree AT THE TERMS OF THE COMPOSED MEANING's
CONSTANT (Johnson/P5J/LettersAt.lean: At.cs, At.arr, At.ms, At.N, At.X, At.layout, At.num), from an
accept of the cheap public test padsAtZ (Johnson/Desc/Kinds/HeadDoorAtZ.lean). Theorems.


What is proved.
  padsRow_atR      the second test at arr := arrOf (planSeatsAll Z Z.D), num := numOfPlan (the
          same), any numbers N whose groups are numbersOf (planSeats Z Z.D.1)'s, and the members by
          the make off the plan's seats (P5T.msAtR Z rad, at any radii) is padsAtZ Z. By
          memsSame_atR (Johnson/P5T/MembersByMake.lean): NO PREMISE ON THE MEMBERS.
  **padsFree_atTerms**   padsAtZ Zp = true and Meaning.laidThere (At.X Zp) (Meaning.sizesOf (At.X
          Zp)) (At.layout Zp) = true imply P5J.PadsFree at the constant's terms, for every chain cF
          and every lay.
  **padsFree_atAll**     the same under the one head: (h : P5J.AtMg o Z D r Zp Np cF) and padsAtZ Zp
          = true. laidThere is the head's own h.plan.laid.

No existential quantifier.
Not proved here. padsAtZ Zp = true: a test with code; in the goals' scope it is a theorem
(Goal/Meaning/HeadTestsScope.lean: padsAtZ_in_scope). The head is a premise. Nothing on soundness.

-/
import Johnson.Desc.Kinds.Law.HeadDoorAtZLaw
import Johnson.P5J.AtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (Numbers)
open P5T (planSeats planSeatsAll numbersOf arrOf numOfPlan msAtR memsSame_atR)

/-- The second test at the members by the make off the plan's seats. -/
theorem padsRow_atR (Z : ProofFile.Pub) (rad : ℕ → ℕ → ℕ) (N : Numbers)
    (hN : N.group = (numbersOf (planSeats Z Z.D.1)).group) :
    padsRow Z (lettersOf (arrOf (planSeatsAll Z Z.D)) (numOfPlan (planSeatsAll Z Z.D)) N
      (msAtR Z rad)) = padsAtZ Z := by
  unfold padsRow padsAtZ padsRow lettersOf lettersAt
  dsimp only
  rw [hN]
  exact padsDoor_mems _ _ _ _ _ _ (memsSame_atR Z rad) _ _ _

/-- **PadsFree at the constant's terms.** -/
theorem padsFree_atTerms (Zp : ProofFile.Pub) (cF : Chain P5J.TS ProofFile.Cl) (lay : ByteArray)
    (hp : padsAtZ Zp = true)
    (T : Meaning.laidThere (P5J.At.X Zp) (Meaning.sizesOf (P5J.At.X Zp)) (P5J.At.layout Zp) =
      true) :
    P5J.PadsFree (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp lay) (P5J.At.N Zp cF)
      (Meaning.sizesOf (P5J.At.X Zp))
      (seatLay (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp)) (P5J.At.X Zp) :=
  padsFree_of_row Zp (P5J.At.arr Zp) (P5J.At.num Zp) (P5J.At.N Zp cF) (P5J.At.ms Zp lay)
    (Meaning.sizesOf (P5J.At.X Zp))
    ((padsRow_atR Zp (P5J.At.rad Zp lay) (P5J.At.N Zp cF) rfl).trans hp) T

/-- **Under the one head.** -/
theorem padsFree_atAll {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    (h : P5J.AtMg o Z D r Zp Np cF) (hp : padsAtZ Zp = true) :
    P5J.PadsFree (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF)
      (Meaning.sizesOf (P5J.At.X Zp))
      (seatLay (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp)) (P5J.At.X Zp) :=
  padsFree_atTerms Zp cF Z.lay hp h.plan.laid

end VerifiableInference.Desc.Kinds.Head.Law.OffPad

#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.padsRow_atR
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.padsFree_atTerms
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.padsFree_atAll
