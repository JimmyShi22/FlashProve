-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/WideAtFree.lean: THE OUTPUT HEAD'S OWN ROUNDS: FOR WHOEVER PAYS
THE FIELD fence (Law/ScriptAtHead.lean): UNDER THE LIBRARY'S HYPOTHESIS THE HEAD'S PLAN'S NUMBER OF
MASK ENTRIES IN USE IS NO MORE THAN THE PROGRAMS' OWN COUNT OF FREE ENTRIES AT ONE MASK ROW.
WHAT IT IS NOT. THE FIELD fence IS NOT PAID: there free is a letter. Two premises are left in
fence_at_free_one, AND NEITHER IS SHOWN HERE OF ANYTHING: hfree: free is NO LESS THAN
Send.freeMaskEntries at one mask row, at the first chain's mask code and answers: a fact on whatever
lays free (the frame's keeper's ownerOf, Honest/BookEntries.lean, lays that function at the
message's own mask rows, code and answers, in its own letters: that the code and the answers are the
first chain's at the head's message, and the mask rows not 0, is not shown here; at R rows, R not 0,
the count is no less than at one: the library's freeMask_eq, OnBytes/G4/LedgerLaws.lean; not called
here); hc:
cnt is no more than takesOf: Law/SpentIsTakes.lean has cnt = takesOf where the book lends the row,
BUT UNDER room, which Law/DebtsLess.lean makes of fence: A CIRCLE: so hc stays a premise. No new
mathematics: two lemmas of the library's and arithmetic. At the full size and the format's second
hash function alone, as h. Nothing on whether the verifier accepts a proof, on soundness, on completeness or
on what a proof hides. No example.
  wide_at_free_one    by head_ns_fits (Johnson/Desc/Kinds/Law/HeadNsFits.lean: H.ns and the answers
                      have room in the mask's code) and free_one
                      (Johnson/Desc/Sound/Clamp/InsideOfPlan.lean: at one mask row the count is the
                      code's length less the answers).
  fence_at_free_one   fence from hfree and hc: by within_of_takes and fence_of_within
                      (Law/DebtsLess.lean).

-/
import Johnson.Desc.ProofFile.Honest.K6.Law.DebtsLess
import Johnson.Desc.Kinds.Law.HeadNsFits
import Johnson.Desc.Sound.Clamp.InsideOfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS At.X)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : First.Look.Place}

/-- **THE PLAN'S NUMBER IS NO MORE THAN THE FREE ENTRIES AT ONE MASK ROW**, under the one
hypothesis. -/
theorem wide_at_free_one (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (At.X Zp).H.ns ≤ OnBytes.Send.freeMaskEntries 1
      (Zp.first.codes.mask.getD Zp.first.shape.maskCode default).ell Zp.first.shape.answers := by
  have hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok Zp := h.laid.pub
  obtain ⟨zk, hz, hle⟩ := OffPad.head_ns_fits hZ
  have e : Zp.first.codes.mask.getD Zp.first.shape.maskCode default = zk := by
    rw [Array.getD_eq_getD_getElem?, hz]
    rfl
  have hle' : (At.X Zp).H.ns + Zp.first.shape.answers ≤ zk.ell := hle
  rw [e, VerifiableInference.Desc.Sound.free_one (by omega)]
  omega

/-- **THE FIELD fence, WHERE free IS NO LESS THAN THAT COUNT AND cnt NO MORE THAN THE CEILING.** -/
theorem fence_at_free_one (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {cnt free : Nat}
    (hfree : OnBytes.Send.freeMaskEntries 1
      (Zp.first.codes.mask.getD Zp.first.shape.maskCode default).ell Zp.first.shape.answers ≤ free)
    (hc : cnt ≤ takesOf (parOf (At.X Zp).hS (workOf (At.X Zp)))) :
    OnBytes.Model.Forest.elems (At.X Zp).HLy.fs + cnt ≤ free :=
  fence_of_within (within_of_takes h hc) (le_trans (wide_at_free_one h) hfree)

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.wide_at_free_one
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.fence_at_free_one
