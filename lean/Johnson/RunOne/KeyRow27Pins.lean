-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRow27Pins.lean: THE KEY FILE, ROW 2.7: the premise hpins of the chance's half
(Johnson/RunOne/KeyRow27Chance.lean) AT THE
TABLES' OWN READING of the shared chain, BaseSt.h₂ (Johnson/RunOne/KeyOneReading.lean): its samples
read the two statements, its record
the instance: none reads zFd: so it holds at every record, every list of pins and every d, by rfl.
A fact on a definition. Nothing on soundness.

-/
import Johnson.RunOne.KeyOneReading
import Johnson.Desc.Key.KeyLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Key

theorem pinsStay_h₂_zeta {Cells M Smp Rec : Type} (T : BaseSt Cells M Smp Rec) (at_ : Where) (l :
    List Nat) (p : P₂) (s : St₂)
    (d : List E) : PinsStay T.h₂ at_ l (p, s) (p, { s with loc := { s.loc with zFd := d } }) :=
  ⟨fun _ _ => rfl, rfl⟩

end Johnson.RunOne.KeyRows23
