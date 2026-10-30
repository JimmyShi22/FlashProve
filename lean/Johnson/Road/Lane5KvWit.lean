-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5KvWit.lean

EACH PUBLIC PREMISE OF THE BRIDGE AT ATTENTION WITH A WITNESS, by a run at every build (#guard):
at the two configurations of Lane5KvCfg.lean (cfFull with lid = 28; cfSmall with lid = 24) the
verifier's own function shapeHid ends well, and at the shape S and the lookup's shape fs that it
returns the three tests of Lane5KvCheck.lean say true: numsB S, laidB S, tabsB S fs (every one of
the 4 x 65,536 rows is walked), the two of Lane5KeysIff.lean: tabsEqB S fs, insideB S, and padEqB
S fs of Lane5KvAll.lean. By these files' theorems the premises NumsA, LaidA, TabsA, TabsEq,
InsideA, PadEq hold wherever the tests say true.
(The seam's end asks the reference sizes; the bridge does not.)

The controls. With two shifts in the group laidB says false at its first line (six calls, not
four): that its later lines can say false is not seen. tabsB says false at the small
configuration's shape against the lookup's shape of the same configuration at the shift 11. numsB,
insideB, padEqB and tabsEqB have no control.

A line "#guard" is evaluated when this file is compiled, by Lean's interpreter, and the build
fails if it is false. It is no proof term: the step from "the run said true" to "tabsB S fs =
true" is the build's word.
Not claimed: that these configurations are those of a parameter file. Not run: the two numbers of
SameCalls (Lane5ForIn.lean); they are theorems at the usual call list (sameCalls_of_usual,
Johnson/Road/Lane5SameCalls.lean). The seam's further premises AttSized, hsh, hE are not run here
either.
-/
import Johnson.Road.Lane5KvAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5.KvWit

open OnBytes.Attention (shapeHid)
open KvCfg

#guard ((shapeHid 28 cfFull).toOption.map fun x => numsB x.1) == some true
#guard ((shapeHid 28 cfFull).toOption.map fun x => laidB x.1) == some true
#guard ((shapeHid 28 cfFull).toOption.map fun x => tabsB x.1 x.2) == some true
#guard ((shapeHid 24 cfSmall).toOption.map fun x => numsB x.1) == some true
#guard ((shapeHid 24 cfSmall).toOption.map fun x => laidB x.1) == some true
#guard ((shapeHid 24 cfSmall).toOption.map fun x => tabsB x.1 x.2) == some true
#guard ((shapeHid 28 cfFull).toOption.map fun x => tabsEqB x.1 x.2 && insideB x.1) == some true
#guard ((shapeHid 24 cfSmall).toOption.map fun x => tabsEqB x.1 x.2 && insideB x.1) == some true
#guard ((shapeHid 28 cfFull).toOption.map fun x => padEqB x.1 x.2) == some true
#guard ((shapeHid 24 cfSmall).toOption.map fun x => padEqB x.1 x.2) == some true
-- Controls: two tests can say false: two shifts in the group; the lookup's shape at the shift 11
#guard ((shapeHid 24 { cfSmall with sh := #[12, 12, 11, 11] }).toOption.map fun x => laidB x.1) ==
  some false
#guard ((shapeHid 24 cfSmall).toOption.bind fun x =>
  (shapeHid 24 { cfSmall with sh := #[11, 11, 11, 11] }).toOption.map fun y => tabsB x.1 y.2) ==
  some false

end OnBytes.Road.L5.KvWit
