-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeMask.lean: DOES THE PLAN SEND THE MASKS AHEAD? At every shape that the
planner's sizing returns: yes. Statements and proofs; no definition.

Why. The test `shapeAt` (Johnson/Desc/Last/ShapeAt.lean) has the clause "the mask has come" at every
border; the last chain's start returns a record with a mask's number just where the shape sends the
masks ahead. So at a shape that does not, the test says no everywhere and the promise that it fills
is empty (ShapeAt.lean, limit 2). Does the real plan send them
ahead?

Main names (namespace `VerifiableInference.Desc.Last`).
  **`masksAhead_of_linSized`**: `linSized s L T codes = some (x, c)` gives `x.shape.masksAhead =
    true`: by `linSized_named` (OnBytes/Params/Fit/KeySizedParts.lean) and the text of `linFinish`,
    which writes `true` there.
  `mask_of_start`: where the start says yes, `s₀.loc.mask.isSome = S.masksAhead`: `start_mask_ahead`
    (Johnson/Desc/Third/Law/Mask.lean), read at the record that is returned.
  **`mask_at_planned`**: at `p₁₄Z s cs x` (Johnson/Desc/Third/K14BatchLinearConstraintsSecondPart.lean: the last chain's
    letters "at what the planner has sized") with x out of `linSized`: the record that the start
    returns has a mask's number.

Every "there is": none.
Limits. (1) IT TAKES AWAY ONE REASON FOR EMPTINESS AND SHOWS NO MEMBER: that the start says yes at
some records, and that the other clauses hold there, is not shown. (2) At border 0 alone: behind the
blocks the clause reads the record behind; that the blocks keep the mask's number is `Laid`'s and
the steps' matter (Johnson/Desc/Last/ShapeGives.lean). (3) That the p of a seated description IS
`p₁₄Z` at an x out of `linSized` is not shown here. A shape read from parameter bytes has whatever
flag the bytes hold. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.ShapeGives
import Johnson.Desc.Third.Law.Mask
import OnBytes.Params.Fit.KeySizedParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third VerifiableInference.Desc.Third.Law
open OnBytes.Params

/-- **Every shape that the planner's sizing of the test on the table returns sends the masks
ahead.** -/
theorem masksAhead_of_linSized {s : Setting} {L : LinLines} {T : TableSize} {codes c : Codes}
    {x : LinSized} (h : linSized s L T codes = some (x, c)) : x.shape.masksAhead = true := by
  obtain ⟨X, Y, Z, stU, stO, stW, -, -, -, -, hF⟩ := linSized_named h
  unfold linFinish at hF
  dsimp only at hF
  split at hF
  · obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hF)
    rfl
  · cases hF

/-- **The start's yes: a mask's number lies in the record that it returns just where the shape sends
the masks ahead**: `start_mask_ahead` (Johnson/Desc/Third/Law/Mask.lean), read at the record. -/
theorem mask_of_start (codes : Codes) (S : Params.LinShape) (st₁ : Statement) (book₁ : TreeBook)
    (roots₁ w₁ own₁ : Nat) (mask₁ : Option Nat) (pile₁ : List TensorRow) (o : SharedOut) (s₀ : S₃)
    (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀) :
    s₀.loc.mask.isSome = S.masksAhead := by
  obtain ⟨f, hf, hst⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ h
  obtain ⟨-, -, e0⟩ := start₃_inv _ _ _ _ hst
  obtain ⟨-, -, -, -, hm, -⟩ := firstOutFrom_inv _ _ _ _ _ _ _ _ _ hf
  subst e0
  show f.mask.isSome = S.masksAhead
  rw [hm]
  exact start_mask_ahead _ _ _ _ _ _ _ _ _ _ _ h

/-- **So at what the planner has sized, the record that the start returns has a mask's number**: at
border 0, where the record in front is that record, the clause "the mask has come" asks nothing
beyond the start's yes. -/
theorem mask_at_planned {s : Setting} {L : LinLines} {T : TableSize} {codes c cs : Codes}
    {x : LinSized} (hx : linSized s L T codes = some (x, c)) (h : Handed) (o : SharedOut) (s₀ : S₃)
    (h₀ : start₃E (p₁₄Z s cs x).codes (p₁₄Z s cs x).S h.st h.book h.roots h.w h.own h.mask h.pending
      o = .ok s₀) : s₀.loc.mask.isSome = true :=
  (mask_of_start _ _ _ _ _ _ _ _ _ _ _ h₀).trans (masksAhead_of_linSized hx)

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.masksAhead_of_linSized
#print axioms VerifiableInference.Desc.Last.mask_of_start
#print axioms VerifiableInference.Desc.Last.mask_at_planned
