-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/PinnedAtO.lean: where the key file's piece is laid at what `publicOfO o` returns
(`publicOf` with the second hash function as an argument o:
Johnson/Desc/Ok/PlanWritten/PublicAt.lean), AT EVERY o: the description that was made passes the
written plan's test in its form on the parameter file, and its data are the laid data.

Main names.
  laidFixed_seat_of_publicOfO: publicOfO o pol KL layout = .ok X → keyDataAndDecisionAtFixedDigest X lay = .ok (D, r) →
    ∃ F, descAt X lay fixedDigest = .ok F ∧ seatPinnedKey pol F = true ∧ F.data "key file" = .ok D ∧
    r = (F.pull keyInstanceOfOutOfDomainSample).run.
  laid_bind_seat: the same from the yes of
    `(publicOfO o pol KL (some lay)).bind fun Z => keyDataAndDecisionAtFixedDigest Z lay`.

Limits. A law's file; nothing of the piece imports it. By `laidFixed_seat`
(Johnson/Desc/Key/PinnedIsSeat.lean) and `publicOfO_scan`
(Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean).
"AT EVERY o" IS WORTH "AT EVERY o AT WHICH THE PUBLIC PART IS ACCEPTED". In scope `publicOfO o`
returns only at an o whose digests of the four public tables are the format's: scope fixes these
words as plain numbers, and Johnson/Desc/Ok/PlanWritten/PublicAt.lean holds o's own digests against
them. At every other o a law here that has the yes among its premises holds of nothing.
Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Key.PinnedIsSeat
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

open OnBytes OnBytes.Model OnBytes.Model.Verify

/-- **At every o**: where the piece is laid at what `publicOfO o` returns, the description passes
the test on the parameter file. -/
theorem laidFixed_seat_of_publicOfO {o : Nat → ByteArray → ByteArray} {pol KL lay : ByteArray}
    {layout : Option ByteArray} {X : Public} {D : Maker.WholeD} {r : KeyRun}
    (hX : PlanWritten.publicOfO o pol KL layout = .ok X) (h : keyDataAndDecisionAtFixedDigest X lay = .ok (D, r)) :
    ∃ F, descAt X lay fixedDigest = .ok F ∧ PlanWritten.seatPinnedKey pol F = true ∧
      F.data "key file" = .ok D ∧ r = (F.pull keyInstanceOfOutOfDomainSample).run :=
  laidFixed_seat (PlanWritten.publicOfO_scan hX) h

/-- The same from the yes of the two in a row. -/
theorem laid_bind_seat {o : Nat → ByteArray → ByteArray} {pol KL lay : ByteArray}
    {D : Maker.WholeD} {r : KeyRun}
    (h : ((PlanWritten.publicOfO o pol KL (some lay)).bind fun Z => keyDataAndDecisionAtFixedDigest Z lay) =
      .ok (D, r)) :
    ∃ X F, PlanWritten.publicOfO o pol KL (some lay) = .ok X ∧
      descAt X lay fixedDigest = .ok F ∧ PlanWritten.seatPinnedKey pol F = true ∧
      F.data "key file" = .ok D ∧ r = (F.pull keyInstanceOfOutOfDomainSample).run := by
  cases hX : PlanWritten.publicOfO o pol KL (some lay) with
  | error e =>
    rw [hX] at h
    cases h
  | ok X =>
    rw [hX] at h
    obtain ⟨F, h1, h2, h3, h4⟩ := laidFixed_seat_of_publicOfO hX h
    exact ⟨X, F, rfl, h1, h2, h3, h4⟩

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.laidFixed_seat_of_publicOfO
#print axioms VerifiableInference.Desc.Key.laid_bind_seat
