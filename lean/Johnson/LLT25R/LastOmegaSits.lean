-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastOmegaSits.lean (`omega_seat_is` says the seat by itself):
WHERE OMEGA SITS AT THE SHARED CHAIN's END (`OmegaSits`, LastSeamEnds.lean: the second of the
two facts at the ends of the earlier chains that the seam's cover asks) IS PAID, INSIDE THE
BOOK-KEEPING's YES AT BORDER 2, FROM TESTS ON THE PLAN.
  `omegaSits_of_plan`: by the shared chain's book at its end Omega sits at the seat (t₁ + nΩ, 0):
    its tree's number there is nΩ by `omega_clause` (the proximity test's
    declared rounds open one number only under "taken 1": `OneOmega`; the block on the taken trees'
    sources has tested that Omega's copy's tree is declared), it is part 0 of its tree (a clause of
    the book-keeping's test), and place and tree are there (`Laid.tree`). FROM: `OneOmega π nΩ`; a
    member x of mine whose seat is (t₁ + nΩ, 0) and whose shape is the plan's for Omega.
Limits. Inside a yes of the book-keeping's test, of which no member is shown here. Nothing on
soundness.
-/
import Johnson.LLT25R.LastSeamEnds
import Johnson.ToldDescR.OmegaDeclared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LLT25
open OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Last VerifiableInference.Desc.Third
open VerifiableInference.Desc.Third.Law (start₃E_border)

/-- Omega's seat at the shared chain's end. -/
theorem omega_seat_is (π : P12) (p : P₁₄) (f : Handed) (e : SharedOut) (s : S₃) (t₁ nΩ : ℕ)
    (hs : shapeAt p (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds 2 f e s = true)
    (hOne : ToldDesc.OneOmega π nΩ) :
    seatBy (noShared t₁) e.book e.omega = some (t₁ + nΩ, 0) := by
  obtain ⟨⟨s₀, B⟩, -⟩ := behindOk_of_two hs
  obtain ⟨b, y, G, dot, L⟩ := B.laid
  obtain ⟨g, hg⟩ := start₃E_border _ _ _ _ _ _ _ _ _ _ _ B.start
  obtain rfl : (⟨g, e⟩ : Border) = b := Option.some.inj (hg.symm.trans L.border)
  obtain ⟨q, tr, tO, hq, htr, -, -, -, -⟩ := L.tree
  rw [seatBy_some _ e.book e.omega q tr hq htr]
  show some (t₁ + tr.number, q.2) = _
  rw [ToldDesc.omega_clause π hs hOne q tr hq htr, B.handed.tenant q hq]

/-- **(H2), from tests on the plan.** -/
theorem omegaSits_of_plan (π : P12) (p : P₁₄) (f : Handed) (e : SharedOut) (s : S₃) (t₁ nΩ : ℕ)
    (mine : List Mem)
    (hs : shapeAt p (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds 2 f e s = true)
    (hOne : ToldDesc.OneOmega π nΩ)
    (hx : ∃ x ∈ mine, seatOf x = (t₁ + nΩ, 0) ∧ p.S.omega = (x.1.l.get x.2).1) :
    OmegaSits p t₁ mine e := by
  obtain ⟨x, hm, hseat, hsh⟩ := hx
  obtain ⟨⟨s₀, B⟩, -⟩ := behindOk_of_two hs
  obtain ⟨b, y, G, dot, L⟩ := B.laid
  obtain ⟨g, hg⟩ := start₃E_border _ _ _ _ _ _ _ _ _ _ _ B.start
  obtain rfl : (⟨g, e⟩ : Border) = b := Option.some.inj (hg.symm.trans L.border)
  obtain ⟨q, tr, tO, hq, htr, -, -, -, -⟩ := L.tree
  refine ⟨x, hm, ?_, hsh⟩
  rw [seatBy_some _ e.book e.omega q tr hq htr, hseat]
  show some (t₁ + tr.number, q.2) = _
  rw [ToldDesc.omega_clause π hs hOne q tr hq htr, B.handed.tenant q hq]

end LLT25

#print axioms LLT25.omega_seat_is
#print axioms LLT25.omegaSits_of_plan
