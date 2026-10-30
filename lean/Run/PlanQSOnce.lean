-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQSOnce.lean: tests of `Run.PQ.opensEachOnce` (each tree that a description sends is opened
exactly once) at the descriptions that part 2 lists.

Why. The limits of the generic construction (`Run.PQ.ok`, Run/PlanQTypes.lean) allow a tree that is
sent and opened nowhere. So "within the limits" does not say that a chain opens all its trees, and a
description from which an opening was left out by mistake would still be within them: its verifier
would check less, and every theorem would hold of it. For a description that is meant to open all
its trees the fact is tested here (`Run.PQ.opensEachOnce`).

1. What the file contains. Tests only.

2. What is checked when the file compiles. Ten tests (#guard). `opensEachOnce` is true at the
   descriptions that, by a search of this directory, another file (Run/PlanQSBare.lean apart) tests
   against the limits or hands to a run function:
   the product test (the programs' first toy): the six known-answer descriptions, the description at
     the public file of the C++ programs' full parameters, the descriptions at the programs' own
     tiny and full parameters, and the generic description at three choices of its arguments;
   the chain of links (the second toy): at the tiny and the full parameters, generic (at one choice
     of its other arguments) and the programs' own;
   the two known-answer chains of the format's rules (`Fmt.Known8.spec`, in both fields), and the
     small description of Run/ParseChain.lean (`ParseEx.spec`, tested at the claim (1, 2, 3));
   and its twin in Fmt/Toy1.lean (`Fmt.Toy1.spec`, tested at the claim (1, 2, 3)), which no file of
     this directory tests against the limits or hands to a run function, but of whose rounds' data a
     statement speaks (Run/PlanDrawsQ.lean).
   It is false at the two made-up chains of Run/PlanQSBare.lean, which send a tree that they never
     open, and at a chain that opens a tree twice (`Fmt.Toy8K2.specT`).

3. Theorems. None.

4. What is not claimed. That these are all descriptions that will ever be meant to open all their
   trees: a new one wants its own line here. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Run.M1PlanQ
import Run.M1RunTie
import Run.M1RunTieTheirs
import Run.M2Tie
import Run.PlanQXFastR
import Fmt.M3Items
import Fmt.M3Dec
import Fmt.ParamsRead
import Fmt.Rules5Fast
import Fmt.M3Entry
import Run.PlanQSBare
import Fmt.M2Theirs
import Fmt.M1PlanKnownP
import Fmt.Toy1

set_option autoImplicit false

-- the product test
open Run.PQ Run.M1RunTie in
#guard opensEachOnce SA && opensEachOnce SB && opensEachOnce ST && opensEachOnce SF && opensEachOnce SR && opensEachOnce SK
open Run.PQ in
#guard opensEachOnce _root_.Fmt.M1.KnownP.spec
open Run.PQ Run.M1RunTieTheirs in
#guard opensEachOnce SN && opensEachOnce SM
open Run.PQ _root_.Fmt.M1 in
#guard opensEachOnce (specOf toyPar _root_.Fmt.zero32 []) && opensEachOnce (specOf toyPar (_root_.Fmt.pattern 32) [("codes", _root_.Fmt.pattern 8)]) && opensEachOnce (specOf tinyPar _root_.Fmt.zero32 [])
-- the chain of links
open Run.PQ Run.M2Tie in
#guard opensEachOnce (ST (_root_.Fmt.pattern 32) []) && opensEachOnce (SF (_root_.Fmt.pattern 32) [])
open Run.PQ in
#guard opensEachOnce _root_.Fmt.M2.Theirs.specTiny && opensEachOnce _root_.Fmt.M2.Theirs.specFull
-- the known-answer chains of the format's rules; Run/ParseChain.lean's small description, its twin
open Run.PQ Run.PQ.TS in
#guard opensEachOnce (K8 .two) && opensEachOnce (K8 .one)
open Run.PQ in
#guard opensEachOnce (T1.S (1, 2, 3)) && opensEachOnce (_root_.Fmt.Toy1.spec (1, 2, 3))
-- not so: a tree that is never opened; a tree that is opened twice
open Run.PQ in
#guard !opensEachOnce Bare.one && !opensEachOnce Bare.three && !opensEachOnce _root_.Fmt.Toy8K2.specT
