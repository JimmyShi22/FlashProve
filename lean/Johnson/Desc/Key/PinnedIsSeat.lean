-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/PinnedIsSeat.lean: WHY NO PARAMETER FILE STANDS AMONG THE DOOR's ARGUMENTS: the
written plan's test in its form on (m, F), which the door of the key file's piece lays
(`PlanWritten.pinnedKeyAt`, Johnson/Desc/Key/Asks.lean), IS the test in its form on the parameter
file (`PlanWritten.seatPinnedKey pol F`), wherever X holds that file's scan and m is what the maker
returns at X.

Main names.
  pinned_is_seat: polScan pol = .ok X.P → madeAt X lay c = .ok m →
    pinnedKeyAt m F = seatPinnedKey pol F.
  laidFixed_seat: so where the piece is laid at an X that holds pol's scan: the description F that
    was made passes `seatPinnedKey pol F`, and its data are the laid data.
  laidFixed_seat_of_publicOf: the same at the X that `publicOf pol KL layout` returns (the library's
    `publicOf_scan`).

Limits. A law's file: it grows with nothing and nothing of the piece imports it. That another maker
of X hands the parameter file's scan is that maker's law. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Key.SlotPassesBothTests
import Johnson.Desc.Key.NoCfgLive
import OnBytes.Model.VerifyDerives

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

open OnBytes OnBytes.Model OnBytes.Model.Verify
open Johnson.G.OfPlan (Made)

/-- **The two forms of the written plan's test are one**, where X holds the parameter file's scan. -/
theorem pinned_is_seat {pol lay c : ByteArray} {X : Public} {m : Made} (F : FileDescription Xi)
    (hs : polScan pol = .ok X.P) (hm : madeAt X lay c = .ok m) :
    PlanWritten.pinnedKeyAt m F = PlanWritten.seatPinnedKey pol F := by
  unfold PlanWritten.pinnedKeyAt PlanWritten.seatPinnedKey PlanWritten.keyOf
  rw [hs, madeAt_public hm]

/-- **Where the piece is laid, the description passes the test on the parameter file.** -/
theorem laidFixed_seat {pol lay : ByteArray} {X : Public} {D : Maker.WholeD} {r : KeyRun}
    (hs : polScan pol = .ok X.P) (h : keyDataAndDecisionAtFixedDigest X lay = .ok (D, r)) :
    ∃ F, descAt X lay fixedDigest = .ok F ∧ PlanWritten.seatPinnedKey pol F = true ∧
      F.data "key file" = .ok D ∧ r = (F.pull keyInstanceOfOutOfDomainSample).run := by
  obtain ⟨m, F, hm, hF, hp, hd⟩ := laidFixed_pinned h
  obtain ⟨m', S, N, P, hm', -, -, -, hF', -, -, -, -, -, hr⟩ := laidFixed_is X lay D r h
  obtain rfl : m = m' := Except.ok.inj (hm.symm.trans hm')
  have e : descAt X lay fixedDigest = .ok F := by
    unfold descAt
    rw [hm]
    exact hF
  obtain rfl : F = descriptionFromSource S N P := Except.ok.inj (e.symm.trans hF')
  exact ⟨_, e, (pinned_is_seat _ hs hm).symm.trans hp, hd, hr⟩

/-- The same at what `publicOf` returns. -/
theorem laidFixed_seat_of_publicOf {pol KL lay : ByteArray} {layout : Option ByteArray} {X : Public}
    {D : Maker.WholeD} {r : KeyRun} (hX : publicOf pol KL layout = .ok X)
    (h : keyDataAndDecisionAtFixedDigest X lay = .ok (D, r)) :
    ∃ F, descAt X lay fixedDigest = .ok F ∧ PlanWritten.seatPinnedKey pol F = true ∧
      F.data "key file" = .ok D ∧ r = (F.pull keyInstanceOfOutOfDomainSample).run :=
  laidFixed_seat (publicOf_scan hX) h

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.pinned_is_seat
#print axioms VerifiableInference.Desc.Key.laidFixed_seat
#print axioms VerifiableInference.Desc.Key.laidFixed_seat_of_publicOf
