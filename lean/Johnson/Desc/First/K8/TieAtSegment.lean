-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/TieAtSegment.lean: THE SMALLNESS TEST'S ITEM "tie" OF THE TABLE OF JOINTS,
WITH THE TABLE OF CELLS BY THE SEGMENT'S NUMBER.

A RIGHTING OF `tieK8` (Johnson/Desc/First/K8/LawItems.lean), WHICH DROPS THE SEGMENT'S NUMBER: an
array's number is the link's own (the link's table of arrays): ONE table of cells A cannot serve two
segments. Here A takes the segment's number first: at segment m the sentence is `TieAt (A m)`.
  `tieK8At A`: the item. `tieK8At_eq`: at one m it is `tieK8 (A m)`.
  `tieK8Rec A`: THE FORM FOR THE COMPOSED FILLING: A takes the segment's number AND THE CARRIED
    RECORD: A : ℕ → P × S → W → ℕ → ℕ → ℕ → E: which array a number names is the open link's own
    table's to say. `tieK8Rec_eq`: at one record it is `tieK8At`.
Two definitions and two equations by rfl. Nothing on soundness.

-/
import Johnson.Desc.First.K8.LawItems

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

/-- **The tie in the type of the table's letter, with the table of cells by the segment's
number.** -/
def tieK8At {P W Strs : Type} (A : ℕ → W → ℕ → ℕ → ℕ → Cb.Gl.E) : ℕ → P × S → Strs → W → Prop :=
  fun m a _ w => TieAt (A m) a.2 w

theorem tieK8At_eq {P W Strs : Type} (A : ℕ → W → ℕ → ℕ → ℕ → Cb.Gl.E) (m : ℕ) :
    tieK8At (P := P) (Strs := Strs) A m = tieK8 (A m) m := rfl

/-- **The same with a table of cells that reads the carried record too**: which array a number names
is the open link's own table's to say. -/
def tieK8Rec {P W Strs : Type} (A : ℕ → P × S → W → ℕ → ℕ → ℕ → Cb.Gl.E) :
    ℕ → P × S → Strs → W → Prop :=
  fun m a _ w => TieAt (A m a) a.2 w

theorem tieK8Rec_eq {P W Strs : Type} (A : ℕ → P × S → W → ℕ → ℕ → ℕ → Cb.Gl.E) (m : ℕ)
    (a : P × S) (y : Strs) (w : W) :
    tieK8Rec A m a y w = tieK8At (fun m => A m a) m a y w := rfl

end VerifiableInference.Desc.First.K8
