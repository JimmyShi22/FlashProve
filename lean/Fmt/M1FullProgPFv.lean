-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1FullProgPFv.lean: the nineteen intermediate values that the programs print beside their proof
for the first toy, at the full parameters. Lean computes the same values from the bytes of that
proof.

"The programs" are the C++ implementation that comes with this Lean code. `valuesF`
(Fmt/M1Full.lean) is applied to the programs' proof file. The result is compared with the programs'
own list, in that list's form and order, together with the names (`names`, Fmt/M1Targets.lean). The
list was put into this file by a program, from the table of targets that came with the proof.

What is checked when the file compiles. The comparisons just named (#guard).

Theorems. None. No Mathlib. What these runs do not show is in Fmt/M1FullProg.lean.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M1FullProgPFw

open Fmt.M1 in
#guard Full.valuesF KnownF.spec KnownF.par ProgPF.proof == some [(2166996948891947046, 3650673811153277223, 11644545328877844763), (5843136388882871676, 9857641664784202168, 10126993328148702619), (15157971653614399005, 6245619301607599744, 9648677070648794674), (6941180393721492303, 106105062504435896, 8191260680956291295), (4213438435932505364, 13913391882195829507, 15106097162742257806), (7647466665579153101, 5618125486191639550, 1298975912307191118), (16896622008343573813, 3177683923063335782, 15288328166946233371), (2792136470085601780, 864727883374470067, 4353404755133226034), (7556901618310605497, 14086765174605756100, 12846462571778767000), (13663400813198123720, 1472905085020507397, 7197122638866568959), (16995138027182233847, 10487183301274854497, 1236119099341920516), (2517612609143610548, 3784989893154063167, 6618140326442423756), (15122926737722244059, 14359142668714992976, 13907827358619074412), (1158926177730761436, 16353628314843376054, 17948254889232124663), (4534591662568656568, 5152744046390091679, 12486676621535612413), (5319942489304765241, 17167763654113124679, 11366815141767941098), (14735030324704496585, 3928122498488415065, 17176505830409675952), (15814141273981527967, 13639215737672171125, 6809407831656219400), (15814141273981527967, 13639215737672171125, 6809407831656219400)]
open Fmt.M1 in
#guard names 3 == ["BAT: target", "FOLD: target", "CS: y_main at the first draw", "CS: y_0 at the first draw", "CS: y_1 at the first draw", "CS: target", "CS: c'[0]", "CS: d'[0]", "CS: d's last entry", "FOLD: target", "CS: y_main at the first draw", "CS: y_0 at the first draw", "CS: y_1 at the first draw", "CS: target", "CS: c'[0]", "CS: d'[0]", "CS: d's last entry", "BASE: left side of the linear check", "BASE: right side of the linear check"]
