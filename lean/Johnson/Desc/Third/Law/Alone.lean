-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/Alone.lean: the third test of the taking-over of Omega, handed back: Omega's
tree in the shared chain's book has one part. Theorems; no definition.

Why. `takeOver_inv` (Johnson/Desc/Third/Law/Keeps.lean) hands back the first two tests (Omega has a
place in the shared chain's book; its tree is in that book) and drops the third ("it has a tree to
itself").

Main names.
  `takeOver_alone`: the taking-over's yes gives the place q, the tree t at q.1, and
    t.parts.size = 1.
  `alone_k14Second`: the like of the block, at the border that lies in front.

Limits. The text reads q.1 alone of the place: nothing is said of q.2, nor of which message the one
part is. The proof reads the text's first three tests alone. Of the form "a yes gives". Nothing on
soundness or on hiding.
-/
import Johnson.Desc.Third.Law.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes
open Desc.Plain (DState)

namespace VerifiableInference.Desc.Third.Law

theorem need_yes {n : String} {b : Bool} {u : Unit} (h : need n b = .ok u) : b = true := by
  cases b with
  | true => rfl
  | false => cases h

/-- **The taking-over's yes: Omega's tree in the shared chain's book has one part.** -/
theorem takeOver_alone (S : Params.LinShape) (own : Nat) (o : SharedOut) (d : DState Loc₃)
    (r : Nat × DState Loc₃) (h : takeOver S own o d = .ok r) :
    ∃ q t, o.book.place[o.omega]? = some q ∧ o.book.trees[q.1]? = some t ∧ t.parts.size = 1 := by
  unfold takeOver at h
  obtain ⟨q, hq, h⟩ := ok_of_bind h
  obtain ⟨t, ht, h⟩ := ok_of_bind h
  obtain ⟨_, hn, _⟩ := ok_of_bind h
  exact ⟨q, t, some_of_named hq, some_of_named ht, by simpa using need_yes hn⟩

/-- The like of the block. -/
theorem alone_k14Second {Cl : Type} (p : P₁₄) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s')
    (x : Border) (hx : s.loc.border = some x) :
    ∃ q t, x.shared.book.place[x.shared.omega]? = some q ∧ x.shared.book.trees[q.1]? = some t ∧
      t.parts.size = 1 := by
  obtain ⟨x', a, _, _, hx', ha, _, _, _⟩ := k14Second_inv p s s' rs gs h
  have ex : x' = x := Option.some.inj (hx'.symm.trans hx)
  rw [ex] at ha
  exact takeOver_alone _ _ _ _ _ ha

end VerifiableInference.Desc.Third.Law
