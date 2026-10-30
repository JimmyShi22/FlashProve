-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQSFProgSmall.lean: on all 68 of the programs' own proof files for the first toy, the size
bounds hold under which the parser that fills whole paths is the same function at the format's hash
and at the format's hash over the format's oracle.

"The programs" are the C++ implementation that comes with this Lean code. Run/FullDom.lean proves
`full_HO`: `smallF S b = true` →
`parseFullW (m := Id) (Fmt.HO Fmt.oracle) S T b = parseFullW (m := Id) Fmt.formatHash S T b`. The theorems
that connect a tree of oracle queries with a function speak of the first form. The runs stand at the
second hash, `Fmt.formatHash`.

What is checked when the file compiles. Three tests (#guard): `smallF` is evaluated on every file,
at the description of the file's set: `KnownF.spec` for `ProgPF` (full parameters), `KnownT.spec`
for `ProgPT` and for `ProgPR` (both at the tiny parameters: Fmt/M1FullProgPRw.lean tests
`ProgPR.params == KnownT.spec.params`).

Theorems. None here.

Terms: lean/GLOSSARY.md.
-/
import Run.FullDom
import Fmt.M1FullProgPFw
import Fmt.M1FullProgPTw
import Fmt.M1FullProgPRw

open Fmt.M1 in
#guard ProgPF.all.all fun x => Run.smallF KnownF.spec x.2.1
open Fmt.M1 in
#guard ProgPT.all.all fun x => Run.smallF KnownT.spec x.2.1
open Fmt.M1 in
#guard ProgPR.all.all fun x => Run.smallF KnownT.spec x.2.1
