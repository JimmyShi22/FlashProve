-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Law/PureZOnce.lean: one theorem. `onlineDescriptionFromPublicPart` (OnlineDescriptionFromBlockTables.lean) computes the lots'
blocks once (`baseOf`) and hands them to `faultsAt`, `partsAt` and `lackingAt`. Its value is the
same as if `pureFaults`, `lackingOf` and `partsOf`, each of which computes them again, were asked
one after the other. A proof that prefers that form can rewrite by `pureZ_thrice` first.

-/
import Johnson.Desc.ProofFile.OnlineDescriptionFromBlockTables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Law

theorem pureZ_thrice (Z : Pub) (T : PureSeat) :
    onlineDescriptionFromPublicPart Z T =
      (pureFaults Z T).bind fun faults =>
      (lackingOf Z T).bind fun lack =>
        if !faults.isEmpty then
          .error ("no description: the supplied blocks are inconsistent: " ++
            "; ".intercalate faults)
        else if !lack.isEmpty then
          .error ("no description: nothing usable is supplied for: " ++ ", ".intercalate lack)
        else (partsOf Z T).bind fun P => onlineDescriptionAfterTests Z T P := by
  unfold onlineDescriptionFromPublicPart pureFaults lackingOf partsOf
  cases baseOf Z T with
  | error e => rfl
  | ok B => rfl

end ProofFile.Law

#print axioms ProofFile.Law.pureZ_thrice
