-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/OnePassFull.lean: A TEST ON TWO WRITTEN LISTS, DECIDED BY
LEAN's KERNEL.

The hypothesis hone of `open_k4` (Law/W/OpenAtHead.lean (no part of the library yet)) at the full
size's two lists, in the form in which Honest/Thread/FitsHead.lean asks it: along the first chain's
list of places, whatever a forward row of the table asks or shuts is open in front of it, tested in
one pass. Honest/Thread/FirstFitsThree.lean (no part of the library yet) decides the like test at
three segments in the same way. One statement; its proof is one evaluation by the kernel, which no
independent checker has replayed. A YES ALONE DOES NOT SHOW THAT THE TEST CAN SAY NO: controls at
bent lists, and what the test does not see, stand in Law/W/OnePassFullTest.lean.

  `onePass_full`   the test says true at the full size's two lists.

Not shown here. Nothing on what an item says: lists alone. Nothing on any run, thread or witness.
THE FULL SIZE's TWO WRITTEN LISTS ALONE (`P5J.At.links`, `P5J.At.ps`, Johnson/P5J/LettersAt.lean).
Nothing on soundness, on completeness or on any other property.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 10 modules under Johnson/Goal/ and at 3 under Johnson/Bridge/; it saw 46 modules whose
names hold RecCompile, none under Johnson/D/ or ThirdParty/, none that begins Cb.Bridge and none of
the three names. What lies behind the 13 is not counted: all the numbers are floors. All come with
Johnson/P5J/LettersAt.lean, of which the two lists alone are read; two of the three under
Johnson/Bridge/ come with Honest/Thread/FirstFits.lean too, whose one import,
Honest/Thread/FirstRows.lean, has `opens` and `rowAt`, which are read.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstFits
import Johnson.P5J.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.W
open VerifiableInference.Desc.First (start)
open ProofFile.Honest.FirstRows (opens rowAt)

/-- **Whatever a forward row asks or shuts is open in front of it, at the full size's lists.** -/
theorem onePass_full :
    (((opens P5J.At.links P5J.At.ps (start P5J.At.links)).zip P5J.At.ps).all fun x =>
      ((rowAt P5J.At.links x.2).asks ++ (rowAt P5J.At.links x.2).shuts).all x.1.contains) =
      true := by
  decide +kernel

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.onePass_full
