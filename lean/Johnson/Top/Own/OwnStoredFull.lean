-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Own/OwnStoredFull.lean: the three public files of the shipped full-size example
(examples/full-size/config/) as one closed Lean term. Written by a program; not to be edited by
hand.

States. `zStoredFull : OnBytes.K.Pub`: a definition, made of three terms that the library holds
already. Three `#guard` lines check the three lengths (Lean's evaluator) when the file compiles.
Under. No hypothesis.
Does not show.
  1. Anything about another set of files: these are that example's, and its weights are made up.
  2. That all of it is made up: a few constants in config/ go back to work on real models.
  3. Anything read off a commitment to a real model: no such byte belongs in this library.
  4. That the term holds the files' bytes: the sha256 sums in the notes were taken outside Lean.
  5. That any test on these files passes.
  6. That the verifier program, called on these files, exits with code 0.
  7. Anything on soundness or on a probability.
Notes in full, with every limit at length, stand at the end of this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Oracle.SaysLinesFull
import OnBytes.K.Served
import OnBytes.Tie.Pv.Plan.PlanKits
import OnBytes.Tie.Pv.Plan.PlanLayoutFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.K.Arm.Own

/-- The three public files of the stored full-size example. -/
def zStoredFull : OnBytes.K.Pub :=
  ⟨OnBytes.K.Oracle.fullPolicy,
   OnBytes.Tie.Pv.Plan.layoutF.toUTF8,
   (OnBytes.Tie.Pv.Plan.wordsFile OnBytes.Tie.Pv.Plan.scalesF)⟩

-- the three lengths
#guard zStoredFull.pol.size == 2629
#guard zStoredFull.lay.size == 224975
#guard zStoredFull.KL.size == 2784

end OnBytes.K.Arm.Own

/-
Notes in full (other files' comments call these notes "the head of" this file).

Johnson/Top/Own/OwnStoredFull.lean: the three public files of the stored full-size example, as a
closed term: `zStoredFull : OnBytes.K.Pub`. WRITTEN BY A PROGRAM from the example's three files;
not to be turned by hand.

Whose bytes. The three public files of the full-size stored example that ships in the repository's
folder examples/full-size/ (its config/), AND OF NO OTHER SET. That example's weights are made up:
of it lean/OnBytes/LIMITS.md says that it has, by its own page, synthetic weights, with a few
constants in its config/ that go back to work on real models. Nothing here is read off a commitment
to a real model: no such file, byte or number belongs in this library.
  config/policy.txt  2629 bytes  sha256
    ce9e126bb3ba7179319a31981a3fc36ca505d738348971f379dfc795f94a3fae
  config/layout.txt  224975 bytes  sha256
    a99b964bbd3648d6e3b4007fc9370b5c70c7e9668848daa039820bc9e03e8f80
  config/KL.bin      2784 bytes  sha256
    1c3191164c5113fd04d5108a469d7b3d17f4ccb3256e8a676d15bdc94435b919
These sums were taken outside Lean, of the files that the program read, and once more of what its
own reader of Lean's literals reads back out of the text below and out of the library's terms named
there. THEY ARE WORDS: NO THEOREM. A file on a disk is still compared with these bytes by its sum,
outside Lean. Public parameters and scales; no weights.

How each is written.
  pol: the library's own term
       `OnBytes.K.Oracle.fullPolicy`:
       the same bytes, by the program's reading of the library's text; no new literal
  lay: the library's own term
       `OnBytes.Tie.Pv.Plan.layoutF.toUTF8`:
       the same bytes, by the program's reading of the library's text; no new literal
  KL:  the library's own term
       `OnBytes.Tie.Pv.Plan.wordsFile OnBytes.Tie.Pv.Plan.scalesF`:
       the same bytes, by the program's reading of the library's text; no new literal

Main definition: `zStoredFull`.
What is checked in Lean: the three lengths (`#guard`, by Lean's evaluator, when the file
compiles).
What is not claimed: that any test on Z says yes; that any call of the program on these files ends
in 0. Nothing on soundness; no probability.

Terms: lean/GLOSSARY.md.

-/
