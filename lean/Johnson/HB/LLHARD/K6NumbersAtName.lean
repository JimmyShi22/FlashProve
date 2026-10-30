-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/K6NumbersAtName.lean: one of the seven conditions that are left in front of the
law on the sub-protocol K6 at the head (`K6LeftSeven`, Johnson/Desc/Kinds/Law/K6LeftSeven.lean):
`numbers`: the sub-protocol at place 341 sends nothing, so the first table's numbers of trees and of
oracle messages stay. It holds in scope wherever the value is laid; no test's accept is a premise.

Row or tool. One closed fact with its negative test, and laws in scope by calls of named laws. A
payer for a premise of another law.

At which term. The condition stands at `(dAt h).N`, and `dAt h` abbreviates `h.𝔇`
(Johnson/P5J/MgAtAll.lean). `numbers_at_name` stands at `At.N Zp cF` (Johnson/P5J/LettersAt.lean);
`numbers_at_head` at `h.𝔇.N`.

Who pays what. That the test on the written cut has accepted: `pins_of_laid`
(Johnson/Goal/Skeleton/PinsOfLaid.lean). What the sub-protocols tell is the written cut's:
`told_at_written` (Johnson/Desc/First/CutWritten.lean). The counts at the borders:
`countsAre_at_toldCut` (Johnson/HB/LLHARD/OwedTies.lean) and `told_at` (ToldCounts.lean).

What is here.
  `counts_341`: at the borders 341 and 342 the closed list of counts has (183, 74).
    `counts_342_part`: the negative test: at 342 and 343 the counts part.
  `told_of_laid`: in scope, where the value is laid, what the first chain's sub-protocols tell is
    `toldCut`.
  `numbers_of`: at all numbers that are laid off `toldCut` over the written places, the two numbers
    are the same at the places 341 and 342.
  `numbers_at_name`, `numbers_at_head`.
By evaluations in Lean's kernel (`decide +kernel`): `counts_341`, `counts_342_part`.

Limits. The condition says no more than that the sub-protocol at place 341 tells nothing. Nothing on
soundness.


-/
import Johnson.HB.LLHARD.OwedTies
import Johnson.Goal.Skeleton.PinsOfLaid
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open VerifiableInference.Desc
open VerifiableInference.Desc.First (Numbers flatPlacesOf toldCut told_at_written)
open VerifiableInference.Desc.K13.Law (countsFull told_at countsAre_at_toldCut)

set_option maxRecDepth 1000000 in
/-- **At the borders 341 and 342 the counts are one.** -/
theorem counts_341 :
    countsFull[341]? = some (183, 74) ∧ countsFull[341 + 1]? = some (183, 74) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test: at 342 and 343 they part. -/
theorem counts_342_part : ¬ countsFull[342 + 1]? = countsFull[342]? := by decide +kernel

/-- At all numbers laid off the written cut over the written places. -/
theorem numbers_of (M : Numbers) :
    (M.withTold (flatPlacesOf Sound.linksFull true) toldCut).treesAt
          (flatPlacesOf Sound.linksFull true)[341 + 1]? =
        (M.withTold (flatPlacesOf Sound.linksFull true) toldCut).treesAt
          (flatPlacesOf Sound.linksFull true)[341]? ∧
      (M.withTold (flatPlacesOf Sound.linksFull true) toldCut).msgsAt
          (flatPlacesOf Sound.linksFull true)[341 + 1]? =
        (M.withTold (flatPlacesOf Sound.linksFull true) toldCut).msgsAt
          (flatPlacesOf Sound.linksFull true)[341]? := by
  have a := counts_341.1.symm.trans (told_at M countsAre_at_toldCut (k := 341) (by omega))
  have b := counts_341.2.symm.trans (told_at M countsAre_at_toldCut (k := 341 + 1) (by omega))
  obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj (a.symm.trans b))
  exact ⟨e2.symm, e1.symm⟩

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **What the first chain's sub-protocols tell is the written cut's.** -/
theorem told_of_laid (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) : At.told cF = toldCut := by
  have hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder =
      VerifiableInference.PlanWritten.cutFirstFull := (pins_of_laid hZ L).2
  rw [At.told_is]
  exact (told_at_written hc).2

/-- **The condition, at the closed letters.** -/
theorem numbers_at_name (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    (At.N Zp cF).treesAt (flatPlacesOf Sound.linksFull true)[341 + 1]? =
        (At.N Zp cF).treesAt (flatPlacesOf Sound.linksFull true)[341]? ∧
      (At.N Zp cF).msgsAt (flatPlacesOf Sound.linksFull true)[341 + 1]? =
        (At.N Zp cF).msgsAt (flatPlacesOf Sound.linksFull true)[341]? := by
  unfold At.N
  rw [told_of_laid hZ L]
  exact numbers_of _

/-- **The condition, at the head's own term.** -/
theorem numbers_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    h.𝔇.N.treesAt (flatPlacesOf Sound.linksFull true)[341 + 1]? =
        h.𝔇.N.treesAt (flatPlacesOf Sound.linksFull true)[341]? ∧
      h.𝔇.N.msgsAt (flatPlacesOf Sound.linksFull true)[341 + 1]? =
        h.𝔇.N.msgsAt (flatPlacesOf Sound.linksFull true)[341]? :=
  numbers_at_name h.scope h.laid

end

end P5J

#print axioms P5J.counts_341
#print axioms P5J.counts_342_part
#print axioms P5J.numbers_of
#print axioms P5J.told_of_laid
#print axioms P5J.numbers_at_name
#print axioms P5J.numbers_at_head
