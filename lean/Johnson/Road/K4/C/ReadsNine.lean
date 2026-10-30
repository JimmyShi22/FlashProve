-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/ReadsNine.lean: CONDITIONAL.

What is here. Two small public facts on a plan. Each of the three product layers has at least nine
variables wherever the verifier's `readsOf` returns (`reads_nine`): its own test, read off its text
(OnBytes/Model/LayerLayout.lean). The layout has the two tensors of the gated products, named "s"
and "u" (`tens_su`): from the plan's nine public facts (`K4Plan`,
Johnson/Road/K4/W/GroundOfHear.lean) by the library's `ten_of` (Johnson/Road/FormsKeysFits.lean).
Both are asked by the laws that say that the honest side's functions return jobs of their calls'
shapes.

  `reads_nine`   9 ≤ muV, 9 ≤ muH; with routed experts 9 ≤ muH2.
  `tens_su`   the two tensors are there.

Not shown here. That readsOf returns; K4Plan: hypotheses. WHERE K4Plan HOLDS: the head of
Johnson/Road/K4/W/GroundOfHear.lean; its field sw bars every shape but those with the library's
eleven switches. Nothing on soundness, on completeness or on any other property.
No property is claimed.
-/
import Johnson.Road.K4.W.GroundOfHear
import Johnson.Road.FormsKeysLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Road.K4.W (K4Plan)
open Inst.Model.FFSeg (Dim)

/-- **Each product layer has at least nine variables.** CONDITIONAL: on the return. -/
theorem reads_nine {y : Layer.Lay} {rd : Layer.Reads} (e : Layer.readsOf y = .ok rd) :
    9 ≤ rd.muV ∧ 9 ≤ rd.muH ∧ (y.h.p3 = true → 9 ≤ rd.muH2) := by
  unfold Layer.readsOf at e
  dsimp only at e
  obtain ⟨hc, e⟩ := ok_of_refuse e
  cases e
  obtain ⟨h12, h3⟩ := or_false_split hc
  obtain ⟨h1, h2⟩ := or_false_split h12
  refine ⟨by simpa using h1, by simpa using h2, fun hp => ?_⟩
  rw [hp, Bool.true_and] at h3
  simpa using h3

/-- **The layout has the two tensors of the gated products.** CONDITIONAL: on A. -/
theorem tens_su {hS : Layer.Shape} {pc : List (List String)} {P : Layer.Pub} {g : ℕ}
    {tl : HTailF2} {D : Dim} (A : K4Plan hS pc P g tl D) :
    ∃ ts tu, P.y.T_ "s" = some ts ∧ P.y.T_ "u" = some tu := by
  have Ad := admitted_of_layout A.lay A.sw.p3
  have Sw : Switches P.y.h := by rw [Ad.shape]; exact A.sw
  obtain ⟨ts, hts, _⟩ := ten_of Ad.laid Sw .sl (Or.inl rfl)
  obtain ⟨tu, htu, _⟩ := ten_of Ad.laid Sw .up (Or.inl rfl)
  exact ⟨ts, tu, hts, htu⟩

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.reads_nine
#print axioms OnBytes.Road.K4.C.tens_su
