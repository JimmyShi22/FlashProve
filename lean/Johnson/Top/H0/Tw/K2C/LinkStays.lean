-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/LinkStays.lean: the kind «the code switch»: THE SWITCH AT A LINK LEAVES THE
FRAME's SHAPE, LINK NUMBER AND GROUPS. NO BLOCK IMPORTS THIS FILE.
  yes_link_stays   p.stands = .link and a yes: s'.check.frame.shape | .link | .groups are
                   s.check.frame's
  yes_link_next    and: next = «a later message, or the closing» · moment 1 · the frame's group is
                   the fresh one's number (s.st.groups.size) · the mask is named
Why. The step that the seat joins behind a link's first switch (the link's own «opened») tests the
frame's link number against the link's: with this lemma that test speaks of the record IN FRONT of
the switch too. A frame fact. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.LinkNumbers
import Johnson.Top.H0.Tw.K2C.FrontGroup

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (sendByL8 firstFront firstBehind)

theorem yes_link_stays {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {s' : S} (hp : p.stands = .link) (h : decideWith sendByL8 p s rs gs = .ok s') :
    s'.check.frame.shape = s.check.frame.shape ∧ s'.check.frame.link = s.check.frame.link ∧
      s'.check.frame.groups = s.check.frame.groups := by
  obtain ⟨r₁, r₂, x, w, roots, S', f, mine, rfl, k⟩ := link_inv hp h
  obtain ⟨L, G, S0, g, a⟩ := (_root_.Tw.K2.firstFront_iff _ _ _).1 k.hFront
  obtain ⟨mask, bA⟩ := (_root_.Tw.K2.firstBehind_iff _ _ _ _ _ _ _).1 k.hBehind
  rw [k.hOut]
  refine ⟨?_, ?_, ?_⟩
  · show f.shape = _
    rw [bA.frame]
    show x.f.shape = _
    rw [a.out]
  · show f.link = _
    rw [bA.frame]
    show x.f.link = _
    rw [a.out]
  · show f.groups = _
    rw [bA.frame]
    show x.f.groups = _
    rw [a.out]

theorem yes_link_next {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {s' : S} (hp : p.stands = .link) (h : decideWith sendByL8 p s rs gs = .ok s') :
    s'.check.frame.next = .laterOrClose ∧ s'.check.frame.moment = 1 ∧
      s'.check.frame.group = s.st.groups.size ∧ s'.check.frame.mask.isSome = true := by
  obtain ⟨r₁, r₂, x, w, roots, S', f, mine, rfl, k⟩ := link_inv hp h
  obtain ⟨L, G, S0, g, a⟩ := (_root_.Tw.K2.firstFront_iff _ _ _).1 k.hFront
  obtain ⟨mask, bA⟩ := (_root_.Tw.K2.firstBehind_iff _ _ _ _ _ _ _).1 k.hBehind
  have hg := (firstFront_st k.hFront).2
  rw [k.hOut]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show f.next = _
    rw [bA.frame]
  · show f.moment = _
    rw [bA.frame]
    show x.f.moment = _
    rw [a.out]
  · show f.group = _
    rw [bA.frame]
    exact hg
  · show f.mask.isSome = _
    rw [bA.frame]
    rfl

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.yes_link_stays
#print axioms VerifiableInference.Desc.First.K2.yes_link_next
