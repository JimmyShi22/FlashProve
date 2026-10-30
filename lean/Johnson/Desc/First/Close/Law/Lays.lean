-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/Lays.lean: where the closing of a link lays its open claim: into the
frame's field `rows` and into no other field. One statement and its proof, with two corollaries.

The claim that a closing leaves open (a target and coefficients on three folded rows, with the forms
on the kept members) is taken up by the next link's first block. So it matters where it lies, and
that nothing else of the frame carries a part of it.
  `closeFrame_lays`: if `closeFrame` (Johnson/Desc/First/Close/Closing.lean) says yes, the frame
    behind is the frame in front but for four fields: `rows` is what `closing` returned; `mask` is
    none; `link` is one more; `next` is "the first message of a link". The last three are fixed
    values that hang on nothing that was sent or drawn.
  `closeFrame_rows`: the field `rows` behind is what `closing` returned.
  `closeFrame_same`: two closings from one frame whose `closing` returned the same claim leave the
    same frame.

Limits. Of the frame alone: what the closing turns of the statement (the members' ledgers closed,
the group marked and emptied, the fresh mask marked as spent) is not said here. One direction.
Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.Inv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes

/-- **THE CLOSING LAYS ITS OPEN CLAIM INTO `rows` AND INTO NO OTHER FIELD.** -/
theorem closeFrame_lays {owed : Option Nat} {f f' : ReqFrame} {S S' : Statement}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} (h : closeFrame owed f S es rs = .ok (f', S')) :
    ∃ (G : ReqGroup) (rows : SingleRows), f.groups[f.link]? = some G ∧
      closing ⟨f.shape.code, f.shape.maskCode, G.k, G.h, es⟩ S f.group f.mask rs =
        .ok (rows, S') ∧
      f' = { f with rows := rows, mask := none, link := f.link + 1, next := .first } := by
  unfold closeFrame at h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨G, k1, h⟩ := ok_bind h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨p, k2, h⟩ := ok_bind h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨G, p.1, got_ok k1, k2, rfl⟩

/-- The field `rows` behind is what `closing` returned. -/
theorem closeFrame_rows {owed : Option Nat} {f f' : ReqFrame} {S S' : Statement}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} (h : closeFrame owed f S es rs = .ok (f', S')) :
    f' = { f with rows := f'.rows, mask := none, link := f.link + 1, next := .first } := by
  obtain ⟨_, _, -, -, rfl⟩ := closeFrame_lays h
  rfl

/-- Two closings from one frame that leave the same claim leave the same frame. -/
theorem closeFrame_same {o₁ o₂ : Option Nat} {f f₁ f₂ : ReqFrame} {S₁ S₂ T₁ T₂ : Statement}
    {e₁ e₂ : List Fmt.Entry} {r₁ r₂ : List Fmt.RoundView}
    (h₁ : closeFrame o₁ f S₁ e₁ r₁ = .ok (f₁, T₁)) (h₂ : closeFrame o₂ f S₂ e₂ r₂ = .ok (f₂, T₂))
    (hr : f₁.rows = f₂.rows) : f₁ = f₂ := by
  rw [closeFrame_rows h₁, closeFrame_rows h₂, hr]

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.closeFrame_lays
#print axioms VerifiableInference.Desc.First.Close.closeFrame_rows
#print axioms VerifiableInference.Desc.First.Close.closeFrame_same
