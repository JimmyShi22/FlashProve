-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Fill/WtPlain.lean: what the layer's sentence for "weights" at the output head says,
unfolded to the verifier's state's own fields. One theorem with its proof.

Why. `wtP1` (FillP1.lean) is the sentence in which the law of the merge of the claims on the
committed table ends, and from which the law of the output head's own sub-protocol begins. It is
written over the merge's typed letters. Whoever joins it to another author's sentence wants it in
plain terms.

What is said. `wtP1_plain`: where `wtP1 Pm ni cellOf maskOf a y w` holds: the layout is a return of
the planner's; the state stands in the output head's part and holds a claim on the committed table
and what the head heard; the claim's unit is one of the layout's; the slot x0.sV of the claim's
value is below the planner's number of slots; and the claim's value (`OnBytes.Road.claimVal`) at the
witness's cells, read by cellOf and cut to the committed table (`K11Caller.cellsIn`), is what was
shown at that slot less the factor there times the mask row's entry there, read by maskOf.

Limits. One direction. The sentence reads the witness's own cells: that these are the cells of the
committed table's commitment is another item's matter. Nothing on soundness.

-/
import Johnson.Top.H0.Fill.FillP1

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.FillP1
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Reading WsShape wsLayOf)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First.MergeLaw
open Johnson.Desc.First.ForkMerge (HeadMergeP)

/-- **WHAT THE SENTENCE FOR "weights" AT THE OUTPUT HEAD SAYS, UNFOLDED**: the verifier's state
stands in the output head's part and holds a claim on the committed table and what the head heard;
the claim's unit is one of the layout's; the slot of its value is below the planner's number of
slots; and the claim's value at the witness's cells is what was shown at that slot, less the factor
there times the mask row's entry there. -/
theorem wtP1_plain {P W : Type} (Pm : HeadMergeP) (ni : ℕ) (cellOf : W → ℕ → ℕ → GE)
    (maskOf : P × S → W → ℕ → GE) (a : P × S) (y : Strs) (w : W)
    (hw : wtP1 Pm ni cellOf maskOf a y w) :
    ∃ (s₀ : WsShape) (p3 : Bool) (lkW : ℕ) (h : wsLayOf s₀ p3 lkW = .ok Pm.lay) (hd : HeadOwn)
      (claim : OnBytes.Model.WsClaim) (x0 : OnBytes.Model.Head.Heard)
      (hu : claim.ui < Pm.lay.U.size),
      a.2.here = .head hd ∧ hd.claim = some claim ∧ hd.x = some x0 ∧ x0.sV < Pm.nMsg ∧
      OnBytes.Road.claimVal Reading.gl Pm.lay
          (K11Caller.cellsIn (planPlace Pm h ⟨claim.ui, hu⟩) (cellOf w)) claim =
        Reading.gl.val (hd.F.vp.getD x0.sV zeroE) -
          Reading.gl.val (hd.F.mf.getD x0.sV zeroE) * maskOf a w x0.sV := by
  obtain ⟨s₀, p3, lkW, h, hn, ui, sv, hsv, c, hc, ⟨hd, claim, x0, e1, e2, e3, e4, e5⟩, hW⟩ := hw
  subst e5
  obtain ⟨uv, hu⟩ := ui
  simp only at e4
  subst e4
  refine ⟨s₀, p3, lkW, h, hd, claim, x0, hu, e1, e2, e3, hsv, ?_⟩
  have hq := hW ⟨0, Nat.zero_lt_one⟩
  unfold frontIn at hq
  rw [e1] at hq
  simp only [e2, Option.getD_some] at hq
  exact hq

end VerifiableInference.Desc.First.FillP1

#print axioms VerifiableInference.Desc.First.FillP1.wtP1_plain
