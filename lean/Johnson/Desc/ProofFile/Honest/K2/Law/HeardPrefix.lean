-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/HeardPrefix.lean: the kind "the code switch" (K2): THE TWO
PREMISES ho AND hg OF `key_at_walk` AND ITS KIN (Honest/K2/Law/KeyAtWalk.lean, which this file does
not import) OUT OF PLAINER ONES: what the sender has heard is a beginning of what the later switch
has heard; the folds' challenges of the segments in front, and what their own data hang on, were
heard in front of the sender. Statements with their proofs; no definition.

  `switchAddrs_same`         two places of one lot have one look-up of addresses
  `challengesOr0_of_prefix`  the challenges at numbers below the shorter list's length read alike
  `lotOwn_of_prefix`         the own data of a segment are one at both places: ho
  `heard_of_prefix`          the folds' challenges read alike: hg

By: `ownBy_of_prefix` (Honest/K2/Law/ClosingSame.lean). `switchAddrs_same` walks `switchPlaces`'
text as `switchFront_is` (Honest/K2/Law/CarriedAsks.lean) does, for another field.

Limits. THE PLAINER PREMISES ARE PAID NOWHERE HERE: hpre (a beginning): a fact on a run · hn: each
address of an own message of the segments in front has its `heardAt` within what the sender has
heard: a fact on the filling D · hgam: each number in these segments' lists `gamma` lies below the
length of what the sender has heard: public numbers against a run's length. On texts and lists
alone: no coin, no book. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.CopyAtClosing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law

/-- Two places of one lot have one look-up of addresses. -/
theorem switchAddrs_same {Z : Pub} {G : Ground} {p₀ p : SwitchPlace} (h₀ : p₀ ∈ switchPlaces Z G)
    (h : p ∈ switchPlaces Z G) : p₀.addrs = p.addrs := by
  revert h₀ h
  unfold switchPlaces
  cases hP : P1K2.prepOf Z G with
  | none =>
    intro h₀
    simp at h₀
  | some P =>
    cases hs : spotsOf Z.cuts with
    | none =>
      intro h₀
      simp at h₀
    | some sps =>
      intro h₀ h
      simp only [List.mem_map] at h₀ h
      obtain ⟨s₀, -, rfl⟩ := h₀
      obtain ⟨s, -, rfl⟩ := h
      rfl

/-- The challenges at numbers below the shorter list's length read alike. -/
theorem challengesOr0_of_prefix {heard₀ heard : List Fmt.Drawn} (hpre : heard₀ <+: heard)
    {numbers : List Nat} (hb : ∀ g ∈ numbers, g < heard₀.length) :
    challengesOr0 heard₀ numbers = challengesOr0 heard numbers := by
  obtain ⟨t, rfl⟩ := hpre
  unfold challengesOr0
  refine List.map_congr_left fun g hg => ?_
  rw [List.head?_drop, List.head?_drop, List.getElem?_append_left (hb g hg)]

/-- **ho.** -/
theorem lotOwn_of_prefix {Z : Pub} {G : Ground} {p₀ p : SwitchPlace}
    (h₀ : p₀ ∈ switchPlaces Z G) (h : p ∈ switchPlaces Z G) (segs : List SegmentPub)
    (D : RowData) (Rd : Readers) {heard₀ heard : List Fmt.Drawn} (hpre : heard₀ <+: heard)
    (hn : ∀ s m a, s < p₀.link → p.addrs s m = some a → D.heardAt a ≤ heard₀.length) :
    ∀ i, i < (segs.take p₀.link).length →
      lotOwn segs p₀ D Rd heard₀ (0 + i) = lotOwn segs p D Rd heard (0 + i) := by
  intro i hi
  have hi' : 0 + i < p₀.link := by
    have := List.length_take_le p₀.link segs
    omega
  funext m b j
  show ownBy D Rd p₀.addrs _ heard₀ (0 + i) m b j = ownBy D Rd p.addrs _ heard (0 + i) m b j
  rw [switchAddrs_same h₀ h]
  exact (ownBy_of_prefix D Rd p.addrs _ hpre (0 + i) m (fun a ha => hn _ m a hi' ha) b j).symm

/-- **hg.** -/
theorem heard_of_prefix {heard₀ heard : List Fmt.Drawn} (hpre : heard₀ <+: heard)
    {segs : List SegmentPub} {l₀ : Nat}
    (hgam : ∀ S ∈ segs.take l₀, ∀ g ∈ S.gamma, g < heard₀.length) :
    ∀ S ∈ segs.take l₀, challengesOr0 heard₀ S.gamma = challengesOr0 heard S.gamma :=
  fun S hS => challengesOr0_of_prefix hpre (hgam S hS)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.switchAddrs_same
#print axioms ProofFile.Honest.K2.Law.challengesOr0_of_prefix
#print axioms ProofFile.Honest.K2.Law.lotOwn_of_prefix
#print axioms ProofFile.Honest.K2.Law.heard_of_prefix
