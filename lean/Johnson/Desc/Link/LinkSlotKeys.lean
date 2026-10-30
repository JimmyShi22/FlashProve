-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Link/LinkSlotKeys.lean: THE VALUE FOR THE SLOT (Johnson/Desc/Link/LinkSlot.lean: decOfRoot) RUNS THE ROOT's DESCRIPTION AT THE KEYS WRITTEN OF THE TWO RECORDS: the first table's, and the copy's with item := 1: by
keys_recX (OnBytes/Flat/LinkSib.lean). That right side is, by reading, what our runs of this value evaluated (in working files that are not in this library).
  decOfRoot_keys   the equation
An equation of values; no premise. Nothing on soundness.
-/
import Johnson.Desc.Link.LinkSlot

set_option autoImplicit false

namespace Desc.K15
open OnBytes OnBytes.Flat OnBytes.Slice TypedOracleCompiler.Slice _root_.Run

theorem decOfRoot_keys (pol lay KL : ByteArray) : decOfRoot pol lay KL =
    match linkOfFilesV pol lay KL with
    | .ok L => fun rr V => L.F.run (keyOf (fun β : NZ => β.val) rr.1, { keyOf (fun β : NZ => β.val) rr.2 with item := 1 }) V
    | .error _ => fun _ _ => false := by
  unfold decOfRoot
  cases linkOfFilesV pol lay KL with
  | error e => rfl
  | ok L =>
    funext rr V
    show L.F.run (keysOfX frS.P.v 29 1 (anT frS.P.v 1) (recX rr)) V = _
    rw [keys_recX]

end Desc.K15

#print axioms Desc.K15.decOfRoot_keys
