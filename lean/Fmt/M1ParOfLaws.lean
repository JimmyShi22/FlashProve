-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1ParOfLaws.lean: the first toy. The sizes are read back out of the parameter bytes of their own
description. The statements, for all sizes within bounds (`Par.small`; where bytes are read,
`Params.fit` too: part 3).

The first toy is a product test. "The programs" are the C++ implementation that comes with this Lean
code; "the format page" is docs/format/FORMAT.md, which comes with the programs. A description is
what a verifier knows before it sees a file: among other things the parameter bytes, which hold the
plan of rounds, the digest of the public files, and some further items. These bytes are hashed into
the first value of the hash chain. The sizes (`Par`, Fmt/M1Types.lean) are the toy's parameters: the
field, the logarithm K of the rows' length, the stages of the proximity test with their codes, the
bits of work, the bytes of a salt. `specOf` (Fmt/M1Plan.lean) makes the description from the sizes,
and spells its parameter bytes.

Why. The format page asks that a verifier's decision reads nothing but the messages and what stands
in the items of the first query. A run, or a theorem, at the description `specOf P ..` of sizes P
that were written down meets that rule only together with this fact: the sizes that `parOf`
(Fmt/M1ParOf.lean) reads out of that description's parameter bytes are P. Here it is stated for all
sizes within bounds whose parameters fit (`Params.fit`), so at the tiny and the full parameters and
at any other. `read_back` is that fact. `spec_back` adds, for a description that meets `Spec.ok`,
that the whole description (plan, rounds, shapes) is what the bytes give.

Sources. The items are those of the format page (docs/format/FORMAT.md), rules R12.2 to R12.5: a
stage is four words, the choices are one word. This file has not been held against the page as it
ships, and may differ from it.


1. What the file contains. The bounds; each is a test that can be run.
   `Code.small c`, `Stage.small s`: the three numbers of a code, and a stage's two codes and its k
     and h, are below 2^64. (They are spelled as 64-bit words in the items "codes" and "the stages
     of the proximity test".)
   `Par.small P`: there is a stage; there are fewer than 2^64 stages; every stage is small.
   `theParams P cfg nonceB`: the parameters of the description.
   What `parOf` reads, so that one can see what `par_back` says. Field and salt: the plan's words.
     K: the number of elements drawn in the first entry "ZERO". The bits of work: the first entry
     "BASE". A stage's number of positions: the entries "CS" in their order, then "BASE". A stage's
     codes: by their numbers in the item "codes", in which a code that occurs twice stands once. k
     and h: the item on the stages.

2. What is checked when the file compiles. Two tests (#guard). The bounds, and `Params.fit`
(Fmt/ParamsReadLaws.lean), hold at `toyPar` and `tinyPar`. Sizes without a stage are not small.

3. Theorems stated here (`Fmt.M1.Spec.*`). The proofs are in Fmt/M1ParOfLawsProofs.lean. No Mathlib.
Each is stated for all sizes P, all byte strings cfg and all numbers nonceB.
   `par_back`: `P.small = true → parOf (theParams P cfg nonceB) = some P`. (No bytes: from plan and
     items as values.)
   `read_back`: `P.small = true → (theParams P cfg nonceB).fit = true →`
     `(paramsRead (specOf P cfg (itemsOf P) nonceB).params).bind parOf = some P`.
   `spec_back`: the same two hypotheses, and `(specOf P cfg (itemsOf P) nonceB).ok = true →`
     `specFrom (specOf P cfg (itemsOf P) nonceB).params =`
     `some (P, specOf P cfg (itemsOf P) nonceB)`.

4. What is not claimed. That the sizes give a sound protocol, or fit each other: `Par.fits` and
`stagesOK` are not asked for here, and `par_back` holds without them. Nothing on the public file, or
on how sizes follow from it. That a verifier compares the item "configuration" with the digest of
that file's text (the format page) is not here: `cfg`
is any string (of 32 bytes where
`Params.fit` is asked). Nothing on bytes that are not of the form `specOf P ..`; that direction is
`specFrom_form` in Fmt/M1TheirsSpec.lean.

Terms: lean/GLOSSARY.md.
-/
import Fmt.ParamsReadLaws
import Fmt.M1Prog

namespace Fmt
namespace M1

def Code.small (c : Code) : Bool :=
  decide (c.a < 2 ^ 64) && decide (c.l < 2 ^ 64) && decide (c.r < 2 ^ 64)

def Stage.small (s : Stage) : Bool :=
  s.C.small && s.Z.small && decide (s.k < 2 ^ 64) && decide (s.h < 2 ^ 64)

def Par.small (P : Par) : Bool :=
  !P.stages.isEmpty && decide (P.stages.length < 2 ^ 64) && P.stages.all Stage.small

/-- The parameters of the description of the sizes `P`: their plan, `cfg`, their four items. -/
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

-- The tests, run at the toy's sizes (`toyPar`) and at tiny sizes of this library's own
-- (`tinyPar`).
#guard toyPar.small && tinyPar.small && (theParams toyPar Toy4.cfg 8).fit && (theParams tinyPar Toy4.cfg 8).fit
#guard !(Par.small { toyPar with stages := [] })

end M1
end Fmt
