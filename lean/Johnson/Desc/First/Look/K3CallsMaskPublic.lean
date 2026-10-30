-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
maskCallsB_of_upTo: its premise is evaluated nowhere here.
Johnson/Desc/First/Look/K3CallsMaskPublic.lean: the lookup on a link's CALLS: THE TEST ON PUBLIC
DATA UNDER THE MASK ROW's DICTIONARY (hB of att_maskRow | lay_maskRow,
Johnson/Desc/First/Look/K3CallsMask.lean: maskCallsB … x.ns: "the mask row reaches the place's
number of slots") IS WHAT THE ATTENTION KIND's TEST masksUpTo D x x.ns SAYS
(Johnson/Desc/First/Att/K05MasksAtt.lean). One theorem. A tie of two tests: no error term. NO
SOUNDNESS IS CLAIMED.

Why. masksUpTo … x.ns is a law of the planner's return (masks_of_built,
Johnson/Desc/First/Att/K05PublicOfBuilt.lean): so hB needs no test of its own.

OBJECT: two functions to Bool on public data.
USER: K3DigitsMaskPublic.lean, Johnson/P5J/K03MaskBAt.lean.
LETTERS: D, x, rad free.




  Compiled with the whole library.
Main names:
  `maskCallsB_of_upTo`: masksUpTo D x hi = true gives maskCallsB D (sigListCalls D rad x.link)
    x.link hi = true, at every radius.

Limits. One way.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerAttReads
import Johnson.Desc.First.Att.K05MasksAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att.P (masksUpTo masksUpTo_yes maskMsg)

/-- **The one test gives the other.** -/
theorem maskCallsB_of_upTo {D : Sent} {x : Place} {hi : ℕ} (h : masksUpTo D x hi = true)
    (rad : OracleShape → ℕ) :
    maskCallsB D (sigListCalls D rad x.link) x.link hi = true := by
  obtain ⟨-, k, hk, hm, h1, h2⟩ := masksUpTo_yes h rad
  unfold maskMsg at hm
  obtain ⟨mi, hmi, rfl⟩ := Option.map_eq_some_iff.1 hm
  unfold maskCallsB
  simp only [hmi, List.getElem?_eq_getElem hk, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨h1, h2⟩

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.maskCallsB_of_upTo
