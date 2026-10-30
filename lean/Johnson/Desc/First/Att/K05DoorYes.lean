-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05DoorYes.lean: kind K5: THE LEAN STRUCTURE DoorYes, IN A LIGHT FILE OF ITS
OWN: "the door's Bools say yes at the verifier's state s, and five equations": so that a file that
holds the table of joints' items can state and prove it without the kind's law family.

EVERY FIELD SPEAKS OF THE ONE STATE s OF THE VERIFIER (First.S). Its one ∀ (ns) runs over a ledger F
that s.fork? pins.

Main name:
  `DoorYes W x D born kept own ps qs hi gL s`: six Bools with code at s (liveReqB · seatsOnB ·
    shapesOnB, Johnson/Desc/First/Att/K05DoorB.lean · readsThereB,
    Johnson/Desc/First/Att/Door/ReadsThereB.lean · lookAttB, Johnson/Desc/First/Att/Door/PubK5.lean
    · K3.sizedB, Look/K3Borders.lean, at the open ledger) · the ledger has at most hi slots ·
    what the verifier has received from the lookup argument is gL · the open link L: its number is
    x.link; its own copy of the live request has D's shape and layout; its list of arrays is D's;
    the statement's codes are D's.
born, kept: letters here, so that this file stays light: the law takes them at bornAt D x.link and
(keptAt D x.link).length (Johnson/Desc/First/Look/K3CallerAtt.lean).
WHAT IT GIVES: frontAll_of_door (Johnson/Desc/First/Att/K05FrontOfDoor.lean).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.PubK5
import Johnson.Desc.First.Look.K3CallerBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look (Sent)
open H2K5.Door (readsThereB lookAttB)

/-- **The door's Bools say yes at the verifier's state s, and five equations.** -/
structure DoorYes (W : Verify.Public) (x : VerifiableInference.Desc.First.Look.Place)
    (D : Sent) (born : Array (ℕ × ℕ)) (kept : ℕ) (own : List (ℕ × ℕ)) (ps : List (ℕ × (ℕ × ℕ))) (qs : List (ℕ × OracleShape)) (hi : ℕ)
    (gL : Forest.Heard) (s : First.S) : Prop where
  live : liveReqB born s = true
  seats : seatsOnB kept ps own s = true
  shapes : shapesOnB kept qs s = true
  reads : readsThereB W own s = true
  look : lookAttB s = true
  sized : s.fork?.any VerifiableInference.Desc.K3.sizedB = true
  ns : ∀ F, s.fork? = some F → F.ns ≤ hi
  heard : s.lookHeard? = some gL
  link : ∃ L, s.link? = some L ∧ L.link = x.link ∧ L.check.frame.shape = D.shape ∧
    L.check.rows.layout = D.layout ∧ L.arrayOf = D.arrayOf.getD x.link #[] ∧ s.st.codes = D.codes

end VerifiableInference.Desc.First.Att.P
