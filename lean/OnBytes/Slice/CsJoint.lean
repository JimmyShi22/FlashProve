-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/CsJoint.lean: the code switch in the form in which the blocks of the written proximity
test are chained.

OnBytes/Slice/BlockHolds.lean states what it means that a block is taken off, one definition for
each kind of block. This file shows that the code switch meets its definition (`CsHolds`), with all
that OnBytes/Slice/BlockCs.lean asks of codes and rounds met from plain conditions:
 the sizes of the two stages fit (`CsFit`);
 both stages' codes have room and at most 2^32 positions, and a mask row is not longer than a main
 row (`Sg.Sized`);
 twice the radius after the switch is below the new stage's distance, so that a word has at most
 one code word within the radius;
 the two written rounds have the entry, kind and items of the format's rounds of a switch (`IsRd`).
No condition is put on the radius before the switch.

Main theorem: `cs_holds`.

Not claimed. Nothing on the sizes of the error counts.
-/
import OnBytes.Slice.BlockHolds
import OnBytes.Slice.CsMet
import OnBytes.Slice.Numbers

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Run

/-- A code switch is taken off, with lists of one member. -/
theorem cs_holds {s s' : Sg} (hf : CsFit s s') (hs : s.Sized) (hs' : s'.Sized) (e e' : ℕ)
    (h2 : 2 * e' < s'.d) {dS dC : PQ.RD} {work tree W : ℕ} (hS : IsRd dS (Fmt.M1.rSeed s'.st))
    (hC : IsRd dC (Fmt.M1.rCs work s.st tree W)) :
    CsHolds s s' e e' dS dC (csErr hf e 1 dS dC) :=
  cs_block hf e e' 1 (Sg.fit_cMid hs).laws (Sg.list_cIn hs' h2) dS dC
    (csRounds_of hS hC (le_trans hs.small (by norm_num)))

end OnBytes.Slice

#print axioms OnBytes.Slice.cs_holds
