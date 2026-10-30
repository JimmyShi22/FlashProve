-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/Order.lean: the yes of K14's second part of the last chain keeps
`OnBytes.Means.InOrder` (Johnson/Desc/Means/Order.lean: every group is in order, every open row has
passed the tests of the adding at its group, every sample row is on its own oracle message).
Theorems; no definition.

Main names.
  `inOrder_takeOver`: the taking-over's yes: if this chain's statement in front and the shared
    chain's statement are in order, so is the statement behind.
  `inOrder_k14Second`: the like of the block: at the border that lies in front.
Both go by the library's laws on the plain ground's calls (Johnson/Desc/Means/Page.lean):
adoptP_keeps · elsewhereP_keeps · joinP_keeps · addRowP_keeps.

Limits. That either statement in front is in order is stated by no law of these files. Of the form
"a yes gives". Nothing on soundness or on hiding.
-/
import Johnson.Desc.Third.Law.Keeps
import Johnson.Desc.Means.Page

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes
open Desc.Plain (DState)

namespace VerifiableInference.Desc.Third.Law

/-- The taking-over keeps "in order". -/
theorem inOrder_takeOver (S : Params.LinShape) (own : Nat) (o : SharedOut) (d : DState Loc₃)
    (r : Nat × DState Loc₃) (h : takeOver S own o d = .ok r) (hI : Means.InOrder d.st)
    (hO : Means.InOrder o.st) : Means.InOrder r.2.st := by
  obtain ⟨q, t, y, a, d₁, _, _, hy, ha, hm, h1, h2⟩ := takeOver_inv S own o d r h
  exact Means.joinP_keeps h2 (Means.elsewhereP_keeps h1 (Means.adoptP_keeps ha hI) hO)

/-- **K14's second part keeps "in order".** -/
theorem inOrder_k14Second {Cl : Type} (p : P₁₄) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s')
    (x : Border) (hx : s.loc.border = some x) (hI : Means.InOrder s.st)
    (hO : Means.InOrder x.shared.st) : Means.InOrder s'.st := by
  obtain ⟨x', a, dot, b, hx', ha, hd, hb, e⟩ := k14Second_inv p s s' rs gs h
  subst e
  have ex : x' = x := Option.some.inj (hx'.symm.trans hx)
  rw [ex] at ha
  show Means.InOrder b.st
  exact (Means.addRowP_keeps hb (inOrder_takeOver _ _ _ _ _ ha hI hO)).1

end VerifiableInference.Desc.Third.Law
