-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1FullFv.lean: the verifier on bytes for the first toy, at the full parameters, on files of
this library's own: the nineteen intermediate values that the programs' tool prints beside a proof,
computed from the honest file's bytes, are the reference program's own.

What is run. The function `valuesF` (Fmt/M1Full.lean): the strict reader in its fast form (proved
equal to the reader of the rules at the format's hash), the view, and on the view `targets`
(Fmt/M1Targets.lean) in place of the decision; the head of Fmt/M1Full.lean says what reader and
decision are. The sizes are the full parameters: 30 rounds; three trees of depth 15, 14, 14, opened
at 73, 74, 74 drawn positions; 20 bits of proof of work; files of 160,960 to 162,016 bytes. The
parameter bytes are the programs' own, byte for byte (Fmt/M1PlanKnownF.lean compares them with
Fmt/M1Theirs.lean). The proof files are this library's own, not the programs' (Fmt/M1FilesF.lean):
they were made
outside Lean by a reference program of this library's own in Python, written independently of the
Lean blocks.
"The programs" are the C++ implementation that comes with this Lean code.

What is checked when the file compiles. `valuesF` (Fmt/M1Full.lean) at the honest file is compared
with the reference program's list (put into this file by a program, from its table), in the list's
form and order, together with the names (#guard). The head of Fmt/M1Targets.lean lists the values in
order.

Theorems. None. No Mathlib. The count over all thirteen files, and what these runs do not show, are
in Fmt/M1FullF.lean.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M1FullFw

open Fmt.M1 Fmt.M1.Full in
#guard valuesF KnownF.spec KnownF.par FilesF.honest == some [(6779616238327667854, 3245252718045530024, 11405117075884725935), (8960308637661156804, 3028551958810418484, 14008346732252803307), (13398499383852471517, 13615840976177370141, 6251287066219883759), (7963979869997518473, 1904387894371044315, 9603169483262648208), (9925072332816197432, 16792669602917524112, 7247766962009894010), (3892065435064110238, 2996861558608692931, 5694699882336281676), (8530911779170888635, 2705833622137710950, 12454687646296121645), (16073259213318325093, 805362502546679700, 17450419354638589044), (10275344881110436026, 1038219955563472426, 7745862179201819351), (16877760834073594136, 15114625992140105825, 10776286426205186746), (11544223700458782653, 8142446418139113665, 17323565943953924167), (16837653562899900141, 7640145387812267190, 6119414179016903814), (12318133984852328758, 849908729033821291, 8503426515167918168), (16286121049947588078, 666274360617192824, 7324324957194098054), (16679148002103128663, 15971703674799201641, 5763580262019822892), (6876430756594091566, 6965393258102536577, 15398587473431861291), (15035687068459919232, 7939976096406612821, 5988683200855887540), (10452190072312860685, 8280665744366358893, 12048534261262016120), (10452190072312860685, 8280665744366358893, 12048534261262016120)]
open Fmt.M1 in
#guard names 3 == ["BAT: target", "FOLD: target", "CS: y_main at the first draw", "CS: y_0 at the first draw", "CS: y_1 at the first draw", "CS: target", "CS: c'[0]", "CS: d'[0]", "CS: d's last entry", "FOLD: target", "CS: y_main at the first draw", "CS: y_0 at the first draw", "CS: y_1 at the first draw", "CS: target", "CS: c'[0]", "CS: d'[0]", "CS: d's last entry", "BASE: left side of the linear check", "BASE: right side of the linear check"]
