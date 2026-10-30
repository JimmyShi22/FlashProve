-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/OwnIsOfRec.lean: the lookups' tie of their public record D to the carried
record (OwnIs D l t, Johnson/Desc/First/Look/K3CallerOwn.lean: the record's own five are D's at link
l), from what is known of a record on a run: RecAll (Johnson/Goal/Meaning/RecAll.lean: the codes;
every frame in the record has the shape) and the three that RecAll does not read. One structure, one
theorem; a composition.

  RecOwn D l t   the three: a link is open in the record, with the number l and D's list of arrays
    at l; the live state of the calls has D's layout.
  ownIs_of_rec   RecAll D.codes D.shape t → RecOwn D l t → OwnIs D l t.

Object, letters. Object: OwnIs. Letters: D, l, t: all free.

What is not claimed. RecOwn at any record of any run. Nothing on soundness, nothing on hiding. The
program does not import this file.
-/
import Johnson.Goal.Meaning.RecAll
import Johnson.Desc.First.Look.K3CallerOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Look (Sent OwnIs ownOf)

/-- **What of the record's own five RecAll does not read.** -/
structure RecOwn (D : Sent) (l : ℕ) (t : S) : Prop where
  /-- a link is open in the record: link l, with D's list of arrays at l -/
  link : ∃ L, t.link? = some L ∧ L.link = l ∧ L.arrayOf = D.arrayOf.getD l #[]
  /-- the live state of the calls has D's layout -/
  rows : t.live.rows.layout = D.layout

/-- **The record's own are D's.** -/
theorem ownIs_of_rec {D : Sent} {l : ℕ} {t : S} (A : RecAll D.codes D.shape t)
    (O : RecOwn D l t) : OwnIs D l t := by
  obtain ⟨L, hL, e1, e2⟩ := O.link
  unfold OwnIs ownOf Sent.five
  rw [hL, A.codes, A.live.shape, O.rows]
  show some (D.codes, D.shape, D.layout, L.link, L.arrayOf) = _
  rw [e1, e2]

end Meaning.K2

#print axioms Meaning.K2.ownIs_of_rec
