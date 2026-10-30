-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1FullProgPRv.lean: the nineteen intermediate values that the programs print beside their proof
for the first toy, at the tiny parameters with a repeated position (under a key at which one list
draws the same position twice). Lean computes the same values from the bytes of that proof.

"The programs" are the C++ implementation that comes with this Lean code. `valuesF`
(Fmt/M1Full.lean) is applied to the programs' proof file. The result is compared with the programs'
own list, in that list's form and order, together with the names (`names`, Fmt/M1Targets.lean). The
list was put into this file by a program, from the table of targets that came with the proof.

What is checked when the file compiles. The comparisons just named (#guard).

Theorems. None. No Mathlib. What these runs do not show is in Fmt/M1FullProg.lean.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M1FullProgPRw

open Fmt.M1 in
#guard Full.valuesF KnownT.spec KnownT.par ProgPR.proof == some [(9304136354213669446, 11583715975876258086, 5582187344150694114), (11575046301730029991, 8883825356193821717, 4936564815681879556), (16402372480612881173, 8204258358221534389, 8934874375403678123), (16667449293888268513, 14818924880245746747, 10220927210514127966), (11727132532607862246, 4905760246853883441, 5201717022538874114), (12246451066267544135, 8696923769495108547, 3335442030352934207), (10832869122569517210, 18195120219821523004, 16466096765006655800), (13070711971750157483, 11246750578025826884, 3413912697402142775), (13061787687152097415, 11387018431637265204, 16501168789683734224), (1446596788318286917, 4135959347784065088, 4505194258810502955), (6920631263033619543, 743590428855518691, 5800293230290209740), (6649039375246877526, 17352587703276733113, 7961569972469570314), (8500309792540530238, 9576383885174394398, 18079516542430842037), (2745924903693318272, 15549139075041493962, 11552066937728434399), (3114103901558223350, 12553576153352683942, 15297572133828613793), (2256948054882110246, 14617013154089718120, 1772237689730569720), (3364925080669929625, 3859111463665647186, 15218666978258258741), (17870765021179092812, 14898480447770624231, 17879911232133922276), (17870765021179092812, 14898480447770624231, 17879911232133922276)]
open Fmt.M1 in
#guard names 3 == ["BAT: target", "FOLD: target", "CS: y_main at the first draw", "CS: y_0 at the first draw", "CS: y_1 at the first draw", "CS: target", "CS: c'[0]", "CS: d'[0]", "CS: d's last entry", "FOLD: target", "CS: y_main at the first draw", "CS: y_0 at the first draw", "CS: y_1 at the first draw", "CS: target", "CS: c'[0]", "CS: d'[0]", "CS: d's last entry", "BASE: left side of the linear check", "BASE: right side of the linear check"]
