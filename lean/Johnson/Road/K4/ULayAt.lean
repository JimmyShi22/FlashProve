-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/ULayAt.lean: THE LAYERS' ARM OF THE ONE STATED FUNCTION, AS A TERM OFF THE PUBLIC
PARAMETERS: what fills the letter uL of uBySort (Johnson/Desc/Sound/StatedAll.lean) in the composed
meaning. A light file: definitions and one call.

  `uLAt X names l`: at link number l: uLay (Johnson/Road/K4/FillStated.lean) at the public
    parameters' structure of the approximate range proof at that link (tlAt X l,
    Johnson/Desc/First/Look/Laid.lean; the empty structure where there is none) and at the matrices
    unpacked from the data's symbols (matsOfData, Johnson/Desc/Sound/DataMats.lean: the text that
    the attention segments' arm reads too), by the link's list of arrays' names, names l.
  `statedIs_uLAt`: at a verifier's state inside a layers' link, Stated.of (uBySort (uLAt X names) uA
    uH) is that arm at the open link's number (stated_lay).
Limits. names is a letter: meant: the built links' own lists. Nothing is said here of what the arm's
cells are worth: Johnson/Road/K4/FillStated.lean and Johnson/Road/K4/ULayPins.lean. K04_law, the law
of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.FillStated
import Johnson.Desc.Sound.StatedAll
import Johnson.Desc.Sound.DataMats
import Johnson.Desc.First.Look.Laid

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.First.Look (tlAt)
open VerifiableInference.Desc.Sound (Stated UFn StatedIs uBySort linkNo stated_lay matsOfData)

/-- **The layers' arm, off the public parameters.** -/
def uLAt (X : Verify.Public) (names : ℕ → Array (ℕ × String)) (l : ℕ) : UFn :=
  uLay ((tlAt X l).getD {}) fun _ B => matsOfData ((tlAt X l).getD {}) (names l) B

/-- At a verifier's state inside a layers' link the one stated function is that arm. -/
theorem statedIs_uLAt (X : Verify.Public) (names : ℕ → Array (ℕ × String)) (uA uH : ℕ → UFn) {s : S}
    {b : LayOwn} (hs : s.here = .lay b) :
    StatedIs (Stated.of (uBySort (uLAt X names) uA uH)) (uLAt X names (linkNo s)) s :=
  stated_lay (uLAt X names) uA uH s b hs

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.statedIs_uLAt
