-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Shape/ShutChain.lean: the sub-protocol without a round "K9: the segment is
shut" (K9.shut, Johnson/Desc/First/Batch/Place.lean) against the shape of the first chain's state
(chainSh, Johnson/Desc/First/Shape/Chain.lean): one step on the shape, and two laws. General laws;
nothing is evaluated.

What the sub-protocol does. Where a link is open it marks the link's context: no link is under way;
the list of arrays has been walked; the link is closed. It asks nothing else, and reads no value.

  `closedSh L`: that marking, on the shape of a link's context.
  `shutG`: the step: a link's context is there: it is marked.
  **`shut_carries`**: the decision accepts from s to t and shutG returns u at chainSh s: then
    u = chainSh t.
  **`shut_returns`**: shutG returns at chainSh s: the decision accepts. No test on values.

Limits. shut_carries takes the step's return as a premise, though it follows from the yes (by
shut_iff and link_sh): the strong form is not stated. linkSh_closed speaks at the context's own
frame alone. The bare sub-protocol: in a seated chain it stands under the wrappers "no mark" and the
comparison of the reply. That the step returns at a shape that the chain reaches is not shown.
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Shape.Chain
import Johnson.Desc.First.Batch.Place

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape

/-- The marking, on the shape of a link's context. -/
def closedSh (L : LinkSh) : LinkSh :=
  { L with check := { L.check with inLink := false }, list := { L.list with walked := true },
           done := true }

theorem linkSh_closed (L : LinkCtx) : linkSh (closed L L.check.frame) = closedSh (linkSh L) := rfl

/-- **The step on the shape.** -/
def shutG (a : ChainSh) : Except String ChainSh :=
  match a.link with
  | some L => .ok (a.setLink (closedSh L))
  | none => .error "K9.in-a-segment"

variable {Cl : Type}

theorem shut_iff (p : Where) (piece : Nat) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (shut (Cl := Cl) p piece).decide s rs gs = .ok t ↔
      ∃ L, s.link? = some L ∧ t = s.putLink (closed L L.check.frame) := by
  show (do
    let L ← there "K9.in-a-segment" s.link?
    pure (s.putLink (closed L L.check.frame)) : Except String S) = .ok t ↔ _
  cases h : s.link? with
  | none =>
    constructor
    · intro e; exact nomatch e
    · rintro ⟨L, e, -⟩; exact nomatch e
  | some L =>
    constructor
    · intro e
      exact ⟨L, rfl, (Except.ok.inj e).symm⟩
    · rintro ⟨L', e, rfl⟩
      obtain rfl := Option.some.inj e
      rfl

theorem link_sh (s : S) : (chainSh s).link = s.link?.map linkSh := rfl

theorem shut_carries (p : Where) (piece : Nat) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (u : ChainSh)
    (h : (shut (Cl := Cl) p piece).decide s rs gs = .ok t) (hg : shutG (chainSh s) = .ok u) :
    u = chainSh t := by
  obtain ⟨L, hL, rfl⟩ := (shut_iff p piece s t rs gs).1 h
  unfold shutG at hg
  rw [link_sh, hL] at hg
  rw [chainSh_putLink, linkSh_closed]
  exact (Except.ok.inj hg).symm

theorem shut_returns (p : Where) (piece : Nat) (s : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (u : ChainSh) (hg : shutG (chainSh s) = .ok u) :
    ∃ t, (shut (Cl := Cl) p piece).decide s rs gs = .ok t := by
  unfold shutG at hg
  rw [link_sh] at hg
  cases hL : s.link? with
  | none => rw [hL] at hg; exact nomatch hg
  | some L => exact ⟨_, (shut_iff p piece s _ rs gs).2 ⟨L, hL, rfl⟩⟩

end VerifiableInference.Desc.K9.Shape

#print axioms VerifiableInference.Desc.K9.Shape.shut_iff
#print axioms VerifiableInference.Desc.K9.Shape.shut_carries
#print axioms VerifiableInference.Desc.K9.Shape.shut_returns
#print axioms VerifiableInference.Desc.K9.Shape.closedSh
#print axioms VerifiableInference.Desc.K9.Shape.linkSh_closed
#print axioms VerifiableInference.Desc.K9.Shape.shutG
#print axioms VerifiableInference.Desc.K9.Shape.link_sh
