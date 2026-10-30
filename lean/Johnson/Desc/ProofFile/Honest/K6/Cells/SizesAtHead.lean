-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Cells/SizesAtHead.lean: THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6):
THE LIBRARY's SIZES OF SEGMENT 24 (`Meaning.sizesOf`, Johnson/Goal/Meaning/HidPlan.lean) AT THE
HEAD's SIX OWN MATRICES OFF THE PLANE ARE THE BOUNDS OF THE THREE OWN RANGES OF `InFour`
(Johnson/Desc/Kinds/Law/K6Cut.lean). Under the hypothesis h (`P5J.AtMgA`,
Johnson/P5J/MgAtAll.lean). On public numbers alone. No definition; one theorem.

  `k6_sizes_own`   the list has eight entries; the wide matrix has four parts; rows of cells and
                   columns at the numbers 0 to 3, 4 and 5 are the layout's m, k; mD, kD; mR, kR

Why. The library has one direction: the four ranges lie inside the sizes (`Came.inSizes_in_scope`,
Johnson/Desc/Kinds/Law/HeadRangesOfNumbers.lean). Whoever must show something of a WHOLE column of
the sizes from a premise inside the ranges wants the other: the sizes are no larger.

By. That theorem's own road: `Fo.Pub.public_mats` (OnBytes/Tie/Pv/Lookup/Ends/FoMadePub.lean): the
plan's list of matrices is `matsH` (OnBytes/Model/HeadPlan.lean); the number of parts off the
library's structure of numerals; then evaluation of the list at that number.

What it is not.
  * Nothing on the plane (number 6) or the borrowed stream (number 7).
  * h: the full size and the format's second hash function alone.
  * Modules under lean/Johnson/Goal/ lie in its import closure.
  * Nothing on any property.
-/
import Johnson.Desc.Kinds.Law.HeadRangesOfNumbers
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS At.X)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : First.Look.Place}

/-- CONDITIONAL: the hypothesis h. **THE SIZES AT THE SIX ARE THE THREE OWN RANGES' BOUNDS.** -/
theorem k6_sizes_own (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (Meaning.sizesOf (At.X Zp) 24).NM = 8 ∧ (At.X Zp).hS.NHf = 4 ∧
    (∀ a, a < 4 → (Meaning.sizesOf (At.X Zp) 24).m a = (At.X Zp).HLy.m ∧
      (Meaning.sizesOf (At.X Zp) 24).k a = (At.X Zp).HLy.k) ∧
    ((Meaning.sizesOf (At.X Zp) 24).m 4 = (At.X Zp).HLy.mD ∧
      (Meaning.sizesOf (At.X Zp) 24).k 4 = (At.X Zp).HLy.kD) ∧
    ((Meaning.sizesOf (At.X Zp) 24).m 5 = (At.X Zp).HLy.mR ∧
      (Meaning.sizesOf (At.X Zp) 24).k 5 = (At.X Zp).HLy.kR) := by
  have hP := h.pubOne
  have B := OnBytes.Road.Hd.public_of_core hP (OnBytes.Road.Hd.core_of_scope h.scope h.reads hP)
  have hN4 : (At.X Zp).hS.NHf = 4 := B.full.NHf
  obtain ⟨stream, _, hm, hNM⟩ := _root_.Fo.Pub.public_mats hP
  have e : Meaning.tlAt (At.X Zp) 24 = (At.X Zp).H.tl := by
    unfold Meaning.tlAt
    simp
  refine ⟨?_, hN4, ?_, ?_, ?_⟩
  · show (Meaning.tlAt (At.X Zp) 24).NM = 8
    rw [e, hNM, hm]
    unfold OnBytes.Model.Head.matsH
    rw [hN4]
    simp [List.range, List.range.loop, List.zipIdx]
  · intro a ha
    show ((Meaning.tlAt (At.X Zp) 24).mats.getD a {}).m = (At.X Zp).HLy.m ∧
      ((Meaning.tlAt (At.X Zp) 24).mats.getD a {}).k = (At.X Zp).HLy.k
    rw [e, hm]
    unfold OnBytes.Model.Head.matsH
    rw [hN4]
    interval_cases a <;> simp [List.range, List.range.loop, List.zipIdx]
  · show ((Meaning.tlAt (At.X Zp) 24).mats.getD 4 {}).m = (At.X Zp).HLy.mD ∧
      ((Meaning.tlAt (At.X Zp) 24).mats.getD 4 {}).k = (At.X Zp).HLy.kD
    rw [e, hm]
    unfold OnBytes.Model.Head.matsH
    rw [hN4]
    simp [List.range, List.range.loop, List.zipIdx]
  · show ((Meaning.tlAt (At.X Zp) 24).mats.getD 5 {}).m = (At.X Zp).HLy.mR ∧
      ((Meaning.tlAt (At.X Zp) 24).mats.getD 5 {}).k = (At.X Zp).HLy.kR
    rw [e, hm]
    unfold OnBytes.Model.Head.matsH
    rw [hN4]
    simp [List.range, List.range.loop, List.zipIdx]

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_sizes_own
