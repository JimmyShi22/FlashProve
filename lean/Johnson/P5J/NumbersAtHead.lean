-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/NumbersAtHead.lean: THE NUMBERS UNDER THE HEAD: at the one head in front of the composed
meaning's constant (`AtMg`, Johnson/P5J/AtMg.lean): in which trees W, the index masks' message and
Omega sit, as numerals, and that they sit below the shared chain's and the last chain's first tree.
FROM THE HEAD ALONE.

What it is for. Laws on the two later chains ask that these three oracle messages sit in trees below
a bound.

WHICH HEAD. The head holds that every entry test of the proof file accepts (`LaidAt.asks`): THE
LIST's FIRST THIRTEEN ROWS (Johnson/Desc/Laid/ProofAsksFirstThirteenTests.lean) AND ONE MORE,
among them the two rows that compare with written values. Over the list of eight rows
(ProofAsksFirstEightTests.lean) `AtMg.pins` and all that follows it here cannot be had.

  How many trees the first and the shared chain send (83 and 11) is another file's:
    `AtMg.data_written`, `AtMg.trees`, `AtMg.trees_at` (Johnson/HB/LLHARD/HeadFacts.lean): called.
    THESE, AND ALL NUMERALS HERE, ARE NUMBERS OF THE WRITTEN VALUES: they hold under the head
    BECAUSE the head's own field holds tests that compare with the written lists and values. They
    are no fact on what the maker of the IOP as written in Lean makes of given public files. They
    speak of the head's own data D.
  `AtMg.first_told`: the first chain's sub-protocols tell 83 trees (`counts_of_planOk`,
    Johnson/Desc/Sound/SeamDesc.lean): that number is the shared table's "first own tree".
  `AtMg.plans_written`: the entries of the public part's list of rounds are the written entries.
    After the proof of `plans_written` (Johnson/Goal/Numbers/PlanWrittenPlans.lean), from the head's
    fields.
  `AtMg.pins`: both rows on written values accept at the head's own public part: ANOTHER FILE's
    (Johnson/P5T/FenceAtMg.lean): CALLED. `AtMg.made_accepts`: the first in the form of which the
    laws speak (`madePinnedAt`, Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean). `AtMg.cut_written`:
    the second: the first chain's cut into sub-protocols is the written one (`cut_of_row`,
    Johnson/Desc/Ok/PlanWritten/CutTestLaws.lean).
  `AtMg.core_written`: the core of the first table's numbers is the written one (`N0Full`): by
    `seats_written` (Johnson/P5T/PlanSeatsTie.lean).
  **`AtMg.seats_at`**: W sits at (82, 0) and the index masks' message at (1, 0).
  `omega_written`: a closed fact, by Lean's kernel (`decide +kernel`): at the written codes and
    shape, with 83 trees in front, Omega sits at (84, 0). `omega_rejects`: the negative test: with
    82 in front it does not.
  **`AtMg.omega_at`**: Omega's tenant, at the terms of which the shared table's numbers are made
    (the trees that the first chain's sub-protocols tell; the layouts of the two sendings at the
    planner's own codes and shape), is (84, 0).
  `AtMg.below_shared`, `AtMg.below_last`: so W and the index masks' message sit below the shared
    chain's first tree, and below the last chain's.

Limits. The full size alone. That a head can be had at given public files is not said here. Nothing
on soundness.
-/
import Johnson.HB.LLHARD.HeadFacts
import Johnson.P5T.FenceAtMg
import Johnson.Desc.Laid.ProofAsksLaw
import Johnson.Desc.Laid.ProofAsksLaw2
import Johnson.Desc.Ok.PlanWritten.CutTestLaws
import Johnson.Goal.Numbers.PlanWrittenPlans
import Johnson.Flat.Dec.DataAtWritten
import Johnson.Desc.Sound.SeamDesc
import Johnson.P5T.PlanSeatsTie
import Johnson.HB.LLHARD.FiveWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open OnBytes OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc (Chain oraclesOf)
open VerifiableInference.Desc.Shared (Msg2)
open _root_.Desc.K14.Law (layUFull layOFull)
open _root_.Desc.K14.Law.Fence (tenantSh)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-! ## The trees that are told; the entries -/

/-- The first chain's sub-protocols tell 83 trees. -/
theorem AtMg.first_told (h : AtMg o Z D r Zp Np cF) :
    (oraclesOf (F0T o Zp Np cF).first.blocksInOrder).length = 83 :=
  (_root_.Desc.K14.Law.Fence.counts_of_planOk (F0T o Zp Np cF) "proof file" D h.laid.planOk
    h.laid.data).1.trans h.trees.1

/-- **The entries of the public part's list of rounds are the written entries.** -/
theorem AtMg.plans_written (h : AtMg o Z D r Zp Np cF) : Zp.plans = P5T.esFull := by
  have hw := (VerifiableInference.PlanWritten.seat_in_scope _ _ Z h.scope
    (LPFD.asks_written h.laid.asks)).1
  obtain ⟨Z', hZ', hpl⟩ := VerifiableInference.PlanWritten.descPure_plans h.laid.value
  obtain rfl : Z' = Zp := Except.ok.inj (hZ'.symm.trans h.laid.pub)
  obtain ⟨e1, e2, e3⟩ := VerifiableInference.PlanWritten.pubBy_entries hZ'
  obtain ⟨w1, w2, w3⟩ := Johnson.G.OfPlan.writtenOf_entries hw
  have hdec : (F0T o Z' Np cF).roundsDeclaredByBlocks = Z'.D :=
    (VerifiableInference.Desc.Sound.decl_of_planOk _ h.laid.planOk).trans hpl
  rw [hdec] at w1 w2 w3
  exact Prod.ext (e1.symm.trans w1.symm)
    (Prod.ext (e2.symm.trans w2.symm) (e3.symm.trans w3.symm))

/-! ## The two rows on written values accept -/

/- That both rows of the entry tests that compare with written values accept at the head's own
public part is `AtMg.pins` (Johnson/P5T/FenceAtMg.lean): called below. -/

/-- The first of the two, in the form of which the laws speak. -/
theorem AtMg.made_accepts (h : AtMg o Z D r Zp Np cF) :
    VerifiableInference.PlanWritten.madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made =
      true :=
  VerifiableInference.PlanWritten.pinnedAt_of_row (by rw [h.pins.1, Bool.or_true])

/-- The second: the first chain's cut into sub-protocols is the written one. -/
theorem AtMg.cut_written (h : AtMg o Z D r Zp Np cF) :
    VerifiableInference.PlanWritten.cutOf (F0T o Zp Np cF).first.blocksInOrder =
      VerifiableInference.PlanWritten.cutFirstFull :=
  (VerifiableInference.PlanWritten.cut_of_row h.pins.2).1

/-! ## The seats -/

/-- **The core of the first table's numbers is the written one.** -/
theorem AtMg.core_written (h : AtMg o Z D r Zp Np cF) :
    P5T.numbersOf (P5T.planSeats Zp Zp.D.1) = P5T.N0Full :=
  (P5T.seats_written h.laid.pub
    (VerifiableInference.PlanWritten.Joined.sends_in_scope h.scope h.laid.pub h.made_accepts)
    ((VerifiableInference.PlanWritten.Joined.first_written_in_scope h.scope h.laid.pub
      h.made_accepts).2.2.1.trans VerifiableInference.PlanWritten.request_shape_written)
    h.plans_written).2.2

/-- **W sits at (82, 0), the index masks' message at (1, 0).** -/
theorem AtMg.seats_at (h : AtMg o Z D r Zp Np cF) :
    (At.N Zp cF).w = (82, 0) ∧ (At.N Zp cF).index = (1, 0) := by
  have e := h.core_written
  constructor
  · show (P5T.numbersOf (P5T.planSeats Zp Zp.D.1)).w = _
    rw [e]
    exact congrArg Prod.snd P5T.N0Full_seats
  · show (P5T.numbersOf (P5T.planSeats Zp Zp.D.1)).index = _
    rw [e]
    exact congrArg Prod.fst P5T.N0Full_seats

set_option maxRecDepth 1000000 in
/-- At the written codes and shape, with 83 trees in front, Omega sits at (84, 0). -/
theorem omega_written : tenantSh 83 layUFull layOFull .oOmega = (84, 0) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test: with 82 trees in front it does not. -/
theorem omega_rejects : ¬ tenantSh 82 layUFull layOFull .oOmega = (84, 0) := by decide +kernel

/-- **Omega's tenant, at the terms of which the shared table's numbers are made.** -/
theorem AtMg.omega_at (h : AtMg o Z D r Zp Np cF) :
    tenantSh (oraclesOf (F0T o Zp Np cF).first.blocksInOrder).length
      ((layTrees (_root_.Desc.K14.p14Of Zp.p.chains (_root_.Desc.K14.beforePointOf Np)).codes
        ((_root_.Desc.K14.withU
          (_root_.Desc.K14.p14Of Zp.p.chains (_root_.Desc.K14.beforePointOf Np)).S).getD
            #[])).getD default)
      ((layTrees (_root_.Desc.K14.p14Of Zp.p.chains (_root_.Desc.K14.beforePointOf Np)).codes
        (_root_.Desc.K14.withOmega
          (_root_.Desc.K14.p14Of Zp.p.chains (_root_.Desc.K14.beforePointOf Np)).S)).getD default)
      .oOmega = (84, 0) := by
  have hs : Zp.p.chains.made.sized.proof = VerifiableInference.PlanWritten.proofSizedFull :=
    VerifiableInference.PlanWritten.sized_in_scope h.scope h.laid.pub
      (VerifiableInference.PlanWritten.sized_of_made h.made_accepts)
  show tenantSh _
    ((layTrees Zp.p.chains.made.sized.proof.codes
      ((_root_.Desc.K14.withU Zp.p.chains.made.sized.proof.batch.shape).getD #[])).getD default)
    ((layTrees Zp.p.chains.made.sized.proof.codes
      (_root_.Desc.K14.withOmega Zp.p.chains.made.sized.proof.batch.shape)).getD default)
    .oOmega = _
  rw [hs, h.first_told, VerifiableInference.PlanWritten.codes_written]
  exact omega_written

/-- W and the index masks' message sit below the shared chain's first tree. -/
theorem AtMg.below_shared (h : AtMg o Z D r Zp Np cF) :
    (At.N Zp cF).w.1 < (oraclesOf (F0T o Zp Np cF).first.blocksInOrder).length ∧
      (At.N Zp cF).index.1 < (oraclesOf (F0T o Zp Np cF).first.blocksInOrder).length := by
  rw [h.first_told, h.seats_at.1, h.seats_at.2]
  exact ⟨by decide, by decide⟩

/-- W and the index masks' message sit below the last chain's first tree. -/
theorem AtMg.below_last (h : AtMg o Z D r Zp Np cF) :
    (At.N Zp cF).w.1 < (D.at frS.P.T.a).t₁ + (D.at frS.P.T.a).t₂ ∧
      (At.N Zp cF).index.1 < (D.at frS.P.T.a).t₁ + (D.at frS.P.T.a).t₂ := by
  rw [h.trees_at.1, h.trees_at.2, h.seats_at.1, h.seats_at.2]
  exact ⟨by decide, by decide⟩

end P5J

#print axioms P5J.AtMg.first_told
#print axioms P5J.AtMg.plans_written
#print axioms P5J.AtMg.made_accepts
#print axioms P5J.AtMg.cut_written
#print axioms P5J.AtMg.core_written
#print axioms P5J.AtMg.seats_at
#print axioms P5J.omega_written
#print axioms P5J.omega_rejects
#print axioms P5J.AtMg.omega_at
#print axioms P5J.AtMg.below_shared
#print axioms P5J.AtMg.below_last
