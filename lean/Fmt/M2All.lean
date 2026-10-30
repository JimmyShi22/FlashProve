-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M2All.lean: the verifier's decision of the second toy (a chain of three links), with all blocks
put in: `dec : Par → Fmt.View → Bool`.

The second toy is a test protocol of the programs, a small interactive proof with oracle messages;
the head of Fmt/M2Dec.lean says what it is. Its purpose is to show, for vectors x_1, b_m, c_m over
the base field, that x_(m+1) = c_m = x_m b_m entry by entry, for m = 1, 2, 3. "The programs" are the
C++ implementation that comes with this Lean code. Fmt/M2Dec.lean defines the decision of the second
toy as a pass through the rounds of a transcript; the pass is generic in the blocks' functions (its
record `Blocks`). A block is one step of the protocol. This file puts the blocks in. Core Lean, no
Mathlib; every function is total; generic in the sizes and in the number of links.

Sources. The blocks' files name theirs; this file adds none.

1. What the file contains.
   `blocks`: the first toy's six (Fmt/M1All.lean), and:
       `sampleOf` (Fmt/M2Send.lean): a member's sample row, the linear equation that the prover's
         answer for a sampled oracle message claims;
       `pscOf` (Fmt/M2Psc.lean): a link's three rows;
       `foldK` (Fmt/M2Fold.lean): a fold with a kept form: the form on the kept member's table stays
         on that table, unfolded;
       `carried`: the claim carried over;
       `oldSample`: a kept message's old sample row carried over;
       `sumDrawsFrom`: the sum of the draws' rows (these three: Fmt/M2Loc.lean).
     The head of Fmt/M2Dec.lean, 1., tells where each enters the pass. A message that the next link
     reads again is kept. A draw is a position that the verifier has drawn and at which the former
     group's tree is opened.
   `decM P V`: the decision `decWith` of Fmt/M2Dec.lean at these blocks, on the toys' own kind of
     view (`M1.View`).
   `dec P V`: the same on the general untyped view of a transcript (Fmt/View.lean).
   What `dec` tests: the two checks of the last block (its linear check and its checks at the drawn
   positions: `baseOK`, Fmt/M1Fold.lean), on the claim that all blocks before have moved. What else
   it refuses before the last block: the head of Fmt/M2Dec.lean, 1.

2. What is checked when the file compiles (#guard). The programs' full parameters and tiny
   parameters pass the test on sizes (`sizesOK`). The clause on the room for a fold's public vector
   is a clause of its own: at a second stage with k = h = 4 (five entries) a mask row of 4 places is
   refused and one of 8 is taken, while all other clauses hold of both (of the refused one this is
   by reading the clauses; no test). `locFits` (Fmt/M2Loc.lean) holds at both parameters, with and
   without a kept row; it includes the condition on the sizes under which the fast sum of the draws'
   rows is proved equal to the sum with every row written out (`sumDrawsFrom_eq`, Fmt/M2LocEq.lean;
   that theorem also has hypotheses on the row from which the sum starts). A view without rounds is
   refused.

3. Theorems. None in this file (see Fmt/M2DecEq.lean).

4. What is not claimed.
   `dec` does not test form, proof of work or Merkle openings; they are the strict reader's and the
   compiled verifier's matter.
   That an honest proof is accepted and a false one refused is not shown in this file.
   No theorem says that `dec` is what the programs decide. It is compared with the programs on their
   own files by tests (#guard): the parameter bytes, every round, 34 intermediate values and the
   outcome on three honest proofs, 39 altered copies and 27 false proofs: Fmt/M2Theirs.lean,
   Fmt/M2EngineLT.lean, Fmt/M2EngineLR.lean, Fmt/M2EngineLF.lean and the files beside them (the
   verifier on bytes); Run/M2EngineT1.lean and the files beside it (the run functions of the generic
   construction). In Fmt/ and Run/ no altered copy of theirs is shown to reach `dec`: in
   Fmt/M2EngineLTw.lean, M2EngineLRw.lean and M2EngineLFwa.lean to M2EngineLFwe.lean the strict
   reader refuses each of them, before `dec` is run (`who`), and in Run/M2Engine*.lean which check
   of the verifier, or of the reader, refuses is not shown. The tests named here stand on the files
   that come with this code.
   No statement on soundness follows.

Notation:
   `Code`, written ⟨a, l, r⟩: a code: codewords of length 2^a, messages of l entries, a random tail
     of r entries (Fmt/M1Codes.lean);
   `Stage`, written ⟨C, Z, k, h, t⟩: a stage of the proximity test: main code C, mask code Z, 2^k
     main rows, 2^h mask rows, t positions drawn (Fmt/M1Types.lean);
   `toyPar`, `tinyPar`: the programs' full parameters and tiny parameters (Fmt/M2Types.lean);
   `ofView`: from the general view (Fmt/View.lean) to the toy's own (Fmt/M1Dec.lean).

Terms: lean/GLOSSARY.md.
-/
import Fmt.M2Dec
import Fmt.M2Targets
import Fmt.M2Send
import Fmt.M2Psc
import Fmt.M2Fold
import Fmt.M2Loc
import Fmt.M1All

namespace Fmt.M2
open Fmt.M1

/-- The blocks' functions of the second toy, as a value of the record `Blocks` (Fmt/M2Dec.lean). -/
def blocks : Blocks := ⟨M1.blocks, sampleOf, pscOf, foldK, carried, oldSample, sumDrawsFrom⟩

def decM (P : Par) (V : M1.View) : Bool := decWith blocks P V

/-- The decision, on the general untyped view of a transcript (Fmt/View.lean). -/
def dec (P : Par) (V : _root_.Fmt.View) : Bool := decWith blocks P (ofView V)

/-- The intermediate values (`targets`, Fmt/M2Targets.lean) at these blocks. -/
def values (P : Par) (V : _root_.Fmt.View) : Option (List E) := targets blocks P (ofView V)

#guard sizesOK blocks toyPar && sizesOK blocks tinyPar
-- k = h = 4, a public vector of 5 entries: a mask row of 4 places is refused, one of 8 is taken
#guard !sizesOK blocks { tinyPar with stages := [⟨⟨9, 64, 3⟩, ⟨9, 16, 3⟩, 1, 0, 3⟩, ⟨⟨9, 4, 3⟩, ⟨9, 4, 3⟩, 4, 4, 3⟩, ⟨⟨10, 4, 3⟩, ⟨10, 64, 3⟩, 0, 0, 3⟩] }
#guard sizesOK blocks { tinyPar with stages := [⟨⟨9, 64, 3⟩, ⟨9, 16, 3⟩, 1, 0, 3⟩, ⟨⟨9, 4, 3⟩, ⟨9, 8, 3⟩, 4, 4, 3⟩, ⟨⟨10, 4, 3⟩, ⟨10, 64, 3⟩, 0, 0, 3⟩] }
-- `locFits` includes 3 ≤ C.l, which `sumDrawsFrom_eq` (Fmt/M2LocEq.lean) assumes if a row is kept.
#guard locFits toyPar.C toyPar.Z true && locFits toyPar.C toyPar.Z false && locFits tinyPar.C tinyPar.Z true && locFits tinyPar.C tinyPar.Z false
#guard decM tinyPar ⟨[], []⟩ == false

end Fmt.M2
