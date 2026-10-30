-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/M1PlanQ.lean: the first toy is within the limits of the generic construction: tests.

The first toy is a product test of the programs (the C++ implementation that comes with this Lean
code). Fmt/M1Plan.lean gives its proof as a description (`Fmt.Spec`), generic in the sizes.
Run/PlanQTypes.lean makes a protocol for the compiled verifier from a description, within limits
that it tests (`Run.PQ.ok`): the description's own conditions; at most one root a round; no tree
given from outside; each own tree opened at most once; the chain's random bytes in the file.

Sources. Written from no file of that toy, without its parameters' further items and its
configuration; the tests hold whatever these are (two choices are tried; `Fmt.Spec.ok` asks a
configuration of 32 bytes and, in `Spec.small`, parameter bytes of at most
2^32 - 144 bytes). The depths, widths and round numbers in the tests are those of the programs'
description of the toy. The programs' files are judged in Run/M1EngineTypedT.lean,
Run/M1EngineOneT.lean and their companion files.

1. What the file contains. Tests only.

2. What is checked when the file compiles. Six tests (#guard), at the toy's full parameters and at
small sizes of this library's own. The limits hold. There are as many rounds' data as rounds (30
and 22). At the full parameters the rounds that send a root carry their tree's shape, which the
description has at the opening and which is looked up ahead.

3. Theorems. None.

4. What is not claimed. No file is judged here. It is not claimed that a description within the
limits opens every tree that it sends: that is a test of its own (`Run.PQ.opensEachOnce`; at these
descriptions: Run/PlanQSOnce.lean).

Terms: lean/GLOSSARY.md.
-/
import Run.PlanQTypes
import Fmt.M1Plan

namespace Run.M1Q
open _root_.Fmt.M1

#guard PQ.ok (specOf toyPar _root_.Fmt.zero32 [])
#guard PQ.ok (specOf toyPar (_root_.Fmt.pattern 32) [("codes", _root_.Fmt.pattern 8)])
#guard PQ.ok (specOf tinyPar _root_.Fmt.zero32 [])
#guard (PQ.rds (specOf toyPar _root_.Fmt.zero32 [])).length = 30 && (PQ.rds (specOf tinyPar _root_.Fmt.zero32 [])).length = 22
-- the rounds that send a root (the text's rounds 0, 22, 26), each with its tree's depth and width
#guard ((PQ.rds (specOf toyPar _root_.Fmt.zero32 [])).zipIdx.filterMap fun x => x.1.tree.map fun s => (x.2, s.a, s.W)) = [(0, 15, 9), (22, 14, 18), (26, 14, 12)]
-- the own trees that are opened behind a round's positions (the text's rounds 23, 27, 29)
#guard ((PQ.rds (specOf toyPar _root_.Fmt.zero32 [])).zipIdx.filter fun x => !x.1.opens.isEmpty).map (fun x => (x.2, x.1.opens)) = [(23, [0]), (27, [1]), (29, [2])]

end Run.M1Q
