-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M2ParOfLaws.lean: the second toy. Under the hypotheses below, what Fmt/M2ParOf.lean reads out of
the parameter bytes is what was spelled into them: the sizes, and the whole description. This file
has the statements.

The second toy is a chain of three links. "The programs" are the C++ implementation that comes with
this Lean code; "the format page" is docs/format/FORMAT.md, which comes with the programs. The file
is a companion of Fmt/M1ParOfLaws.lean and Fmt/M3ParOfLaws.lean.
The toy is a test protocol of the programs; the head of Fmt/M2Dec.lean says what it is. The sizes
are the record `Par` (Fmt/M2Types.lean). A description (`Spec`, Fmt/Rules8.lean; here `specOf`,
Fmt/M2Plan.lean) is the record under which a reader reads a proof file; among its fields: label,
plan, parameter bytes, statement, rounds. To spell is to write as bytes.

Why. FORMAT.md, R0.4 and R0.5: the bytes that enter the chain's first value fix the sizes and the
description that the reader follows. (In Lean: `spec_back`, under its hypotheses.)

1. What the file contains. Two definitions.
   Par.small P   What spelling needs, and no more (it is wider than the format's own bounds).
       Every number that becomes a word of the two items (`itemsOf`, Fmt/M2Items.lean) is below
         2^64: each stage's two codes, k and h; the number of stages; the number of links.
       There is at least one link: the positions at a list of the frame and the bits of work are
         read off the plan's first entry "LOC", and without a link there is none.
       The first stage of the last test is the last group: its codes are the sizes' C and Z, its k
         is that group's, its h is 0 (that group is one message without a mask row; a test in
         Fmt/M2ParOf.lean). That stage is not written in the item, so sizes in which it is another
         cannot come back.
   theParams P cfg nonceB   Plan, digest of the public files and items of these sizes (planOf,
     Fmt/M2Plan.lean; itemsOf, Fmt/M2Items.lean).

2. What is checked when the file compiles. Two tests (#guard). The hypotheses Par.small and
Params.fit hold at toyPar and tinyPar, the second at one cfg and one nonceB. Sizes without a link,
or whose first stage is not the last group, are not small.

3. Theorems stated here (Fmt.M2.Spec.*), for every P, cfg, nonceB. The proofs are in
Fmt/M2ParOfLawsProofs.lean. No Mathlib.
   par_back   small ⇒ parOf (theParams ..) = some P.
   read_back   small, and the parameters fit their spelling (Params.fit, Fmt/ParamsReadLaws.lean) ⇒
     from the bytes of the description's parameters, paramsRead and then parOf give some P.
   spec_back   These, and Spec.ok of the description ⇒ specFrom (its parameter bytes) = some (P, the
     description itself).

4. What is not claimed. The other direction is not claimed (specFrom itself tests that the
description's parameters are the bytes). It is not claimed that any hypothesis holds at given sizes;
at the two descriptions at which the programs' files are judged that is in Fmt/M2SpecBack.lean and
Fmt/M2SpecKnown.lean. It is not claimed that the sizes follow from the public file. Nothing is
claimed on a file.

Notation: `cfg`: a byte array, laid in the place of the digest of the public files (`Params.cfg`,
Fmt/ParamsRead.lean); `nonceB`: the bytes of a nonce in a file (`Plan.nonce`, Fmt/Plan.lean).

Terms: lean/GLOSSARY.md.
-/
import Fmt.M2ParOf
import Fmt.M1ParOfLaws

namespace Fmt
namespace M2
open Fmt.M1

def Par.small (P : Par) : Bool :=
  decide (1 ≤ P.links) && decide (P.links < 2 ^ 64) &&
    decide (P.stages.length < 2 ^ 64) && P.stages.all Stage.small &&
  (match P.stages with
   | s :: _ => s.C == P.C && s.Z == P.Z && s.k == kOf (memsOf P.links (P.links + 1)) && s.h == 0
   | [] => false)

/-- The parameters of the description of sizes. -/
def theParams (P : Par) (cfg : ByteArray) (nonceB : Nat) : Params :=
  ⟨planOf P nonceB, cfg, itemsOf P⟩

namespace Spec

def par_back : Prop :=
  ∀ (P : Par) (cfg : ByteArray) (nonceB : Nat),
    P.small = true → parOf (theParams P cfg nonceB) = some P

def read_back : Prop :=
  ∀ (P : Par) (cfg : ByteArray) (nonceB : Nat), P.small = true →
    (theParams P cfg nonceB).fit = true →
    (paramsRead (specOf P cfg (itemsOf P) nonceB).params).bind parOf = some P

def spec_back : Prop :=
  ∀ (P : Par) (cfg : ByteArray) (nonceB : Nat), P.small = true →
    (theParams P cfg nonceB).fit = true → (specOf P cfg (itemsOf P) nonceB).ok = true →
    specFrom (specOf P cfg (itemsOf P) nonceB).params = some (P, specOf P cfg (itemsOf P) nonceB)

end Spec

-- the tests run at the full and at the tiny parameters
#guard toyPar.small && tinyPar.small && (theParams toyPar zero32 8).fit && (theParams tinyPar zero32 8).fit
-- sizes without a link, or whose first stage is not the last group, are not small
#guard !(Par.small { tinyPar with links := 0 }) && !(Par.small { tinyPar with stages := tinyPar.stages.drop 1 }) && !(Par.small { tinyPar with stages := [] })

end M2
end Fmt
