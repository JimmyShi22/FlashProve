-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1FullProgPTv.lean: the nineteen intermediate values that the programs print beside their proof
for the first toy, at the tiny parameters. Lean computes the same values from the bytes of that
proof.

"The programs" are the C++ implementation that comes with this Lean code. `valuesF`
(Fmt/M1Full.lean) is applied to the programs' proof file. The result is compared with the programs'
own list, in that list's form and order, together with the names (`names`, Fmt/M1Targets.lean). The
list was put into this file by a program, from the table of targets that came with the proof.

What is checked when the file compiles. The comparisons just named (#guard).

Theorems. None. No Mathlib. What these runs do not show is in Fmt/M1FullProg.lean.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M1FullProgPTw

open Fmt.M1 in
#guard Full.valuesF KnownT.spec KnownT.par ProgPT.proof == some [(7769331917339957888, 6738900114519537070, 1378441798464557971), (2474987803316508242, 8270515720943440954, 8069380268126986632), (9588128869360487429, 18323986476162748603, 1860801976805803229), (3775727749801301640, 15548697021082170919, 2312381650525645159), (10969496128444647042, 780533358604457346, 3474272185799347905), (5879441130735576153, 17339452360816528114, 678732502951615036), (17868246639366842900, 17512279626948153953, 14601968181772053254), (15318079925924239733, 374854880371564196, 8827540928440380893), (17736297808774914320, 8965208038864002020, 10988398581973033192), (2942287637505714498, 11495697173886495776, 17406083578350168866), (8115093761454721739, 18399905890146563487, 2309691355962117724), (6400165703570079430, 8013500929602058414, 1195396404918975646), (15577516389870125167, 17231918178869743973, 9542943601689374584), (11631403752640566061, 5544749286976009968, 14909802322449305468), (18184510797497076759, 8600904467437787390, 4142408510634629682), (8707591026953364775, 2548041486914942901, 16633683329728317039), (4499233422314938948, 17165268233609539412, 11600651822967223451), (18186970385001107890, 15669389047495260717, 11773223107899995487), (18186970385001107890, 15669389047495260717, 11773223107899995487)]
open Fmt.M1 in
#guard names 3 == ["BAT: target", "FOLD: target", "CS: y_main at the first draw", "CS: y_0 at the first draw", "CS: y_1 at the first draw", "CS: target", "CS: c'[0]", "CS: d'[0]", "CS: d's last entry", "FOLD: target", "CS: y_main at the first draw", "CS: y_0 at the first draw", "CS: y_1 at the first draw", "CS: target", "CS: c'[0]", "CS: d'[0]", "CS: d's last entry", "BASE: left side of the linear check", "BASE: right side of the linear check"]
