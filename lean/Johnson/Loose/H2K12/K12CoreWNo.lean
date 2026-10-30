-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Loose.H2K12.K12CoreW
/-
Johnson/Loose/H2K12/K12CoreWNo.lean: THE NEGATIVE TEST OF coreW
(H2K12/K12CoreW.lean), ALONE IN ITS FILE, since it is the same evaluation in Lean's kernel once
more.
  coreW_no         coreAtW returns, has a place for Omega's test, and EACH of its four places, laid
                   by H2U.proximityTestParametersAt, PARTS from the written member with one answer more (fourNot,
                   H2K12/K12MemberOfParts.lean). So the test of coreW can say no at each of the
                   four. That its yes is equality is a theorem (sameP12_eq), not this file's
No soundness statement. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open OnBytes OnBytes.Params Johnson.G.OfPlan H2U Johnson.Unfolds
open VerifiableInference.Desc.K12 (P12)
open H2K.Member (piLFull piUFull piOFull piWFull)

theorem coreW_no :
    fourNot coreAtW ({ piLFull with answers := piLFull.answers + 1 } : P12)
      ({ piUFull with place := ⟨2, none, 9, .K12⟩, answers := piUFull.answers + 1 } : P12)
      ({ piOFull with place := ⟨2, none, 10, .K12⟩, answers := piOFull.answers + 1 } : P12)
      ({ piWFull with place := ⟨3, none, 2, .K12⟩, answers := piWFull.answers + 1 } : P12) =
      true := by
  simp only [coreAtW, treesOf, sentAt, sendTag, splitOn_eq, toNat?_eq, slice_toNat?_eq,
    mergeSort_eq]
  decide +kernel

end H2K12

#print axioms H2K12.coreW_no
