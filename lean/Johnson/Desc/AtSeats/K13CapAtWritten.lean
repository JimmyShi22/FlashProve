-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/K13CapAtWritten.lean (it imports Johnson/Desc/AtSeats/K13LawCap.lean):
the binder hCapB of the kind K13's law's top: the three comparisons with
the cap (capB) accept at the seated numbers K13.whereOf Z, where the equations Written Z x hold. One
call: capB_real (thirteen rows, no proof of work), at the fields rows and work of Written. A law
file; no running text imports it.
  capB_of_written

What is not claimed. Written Z x at a seat: written_in_scope, under the door's pin:
with it: InScope W → the public part is made → the pin accepts → the value is laid → capB
(K13.whereOf Z) = true, in one line. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.K13LawCap
import Johnson.Goal.Numbers.WrittenAtZ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params

/-- **The three comparisons accept at the seated numbers.** -/
theorem capB_of_written {Z : ProofFile.Pub} {x : LinSized} (W : _root_.Desc.K14.Law.Written Z x) :
    capB (K13.whereOf Z) = true := capB_real _ W.rows W.work

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.capB_of_written
