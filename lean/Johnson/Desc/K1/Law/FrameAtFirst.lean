-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/FrameAtFirst.lean: WHICH OF THE FRAME's FIELDS THE FIRST SEGMENT's OPENING
(kind K1) WRITES, at the first chain's record: the like of Johnson/Desc/K1/Law/FrameAtLater.lean
for `firstSegmentOpening`. Statements with their proofs. It names no table of joints and imports none.
  `firstOwn_frame'`: **the opening's decision**: the frame behind, as ONE WRITTEN RECORD over the
    frame in front: its group is the number that the new group was given; its moment is 1; ITS
    LIST "own" IS THE FIRST k OF THE NEW MESSAGES' NUMBERS, k the number of the segment's own
    messages at the first moment; "plain" is empty; the mask is the next number; "atStart" gains
    the rest; it awaits a later moment or the closing; EVERY OTHER FIELD (the list of kept copies
    among them) IS AS IT WAS. The walk's list "sent" is "own".
  `firstAtS_frame`: **the block at the record.** `firstAtS_own`, `firstAtS_keptBefore`: read off it.
  `ownIds_get`: the i-th of these numbers is n₀ + i.
What is not claimed. That k is the plan's count. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.Law.FrameAtLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First.Send (joinOwnP)
open VerifiableInference.Desc.First (S)

variable {Cl : Type}

/-- **The opening's decision**: the frame behind, and the walk's list "sent". -/
theorem firstOwn_frame' (P : Par) (owed : Option Nat) (c c' : ChainCheck) (d d' : DState Unit)
    (r₁ r₂ : Fmt.RoundView) (h : firstOwn P owed c d [r₁, r₂] = .ok (c', d')) :
    ∃ g mask, c'.frame =
        { c.frame with
          group := g, moment := 1
          own := #[] ++ (idsOf P d.st.oracles.size).extract 0 (c.frame.atMoment 0).length
          plain := [], mask := some mask
          atStart := c.frame.atStart ++ (idsOf P d.st.oracles.size).extract
            ((c.frame.atMoment 0).length + 1) (idsOf P d.st.oracles.size).size
          next := .laterOrClose } ∧
      c'.sent = (idsOf P d.st.oracles.size).extract 0 (c.frame.atMoment 0).length ∧
      (c.frame.atMoment 0).length < P.sent.size := by
  unfold firstOwn at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨g, d₁⟩, h1, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨ids, d₂⟩, h2, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨mask, hmask, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨f₂, d₃⟩, h3, hfin⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, hids, _⟩ := (decideSend_iff P owed d₁ d₂ r₁ r₂ ids).1 h2
  have hn := (newGroupP_book _ _ _ _ _ ((named_ok _ _ _).1 h1)).2
  have hf : f₂ = _ := joinOwnP_frame _ _ _ _ _ _ ((named_ok _ _ _).1 h3)
  have hI : ids = idsOf P d.st.oracles.size := by rw [hids, hn]; rfl
  have hlt : (c.frame.atMoment 0).length < ids.size := by
    have hm := (named_ok _ _ _).1 hmask
    by_contra hx
    rw [Array.getElem?_eq_none (by omega)] at hm
    cases hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hfin)
  subst hI
  refine ⟨g, mask, ?_, rfl, by rw [idsOf_size] at hlt; exact hlt⟩
  show ({ f₂ with next := .laterOrClose } : ReqFrame) = _
  rw [hf]

/-- **THE BLOCK AT THE RECORD.** -/
theorem firstAtS_frame (q : Params.First) (gp : GPar) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (firstSegmentOpening q gp : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    ∃ g mask, s'.check.frame =
        { s.check.frame with
          group := g, moment := 1
          own := #[] ++ (idsOf (firstPar q gp) s.st.oracles.size).extract 0
            (s.check.frame.atMoment 0).length
          plain := [], mask := some mask
          atStart := s.check.frame.atStart ++ (idsOf (firstPar q gp) s.st.oracles.size).extract
            ((s.check.frame.atMoment 0).length + 1) (idsOf (firstPar q gp) s.st.oracles.size).size
          next := .laterOrClose } ∧
      s'.check.sent = (idsOf (firstPar q gp) s.st.oracles.size).extract 0
        (s.check.frame.atMoment 0).length ∧
      (s.check.frame.atMoment 0).length < (firstPar q gp).sent.size := by
  unfold firstSegmentOpening at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨c, d'⟩, h2, h⟩ := (bind_ok _ _ _).1 h
  obtain rfl := Except.ok.inj h
  exact firstOwn_frame' _ _ _ c _ d' r₁ r₂ h2

/-- The list "own" behind. -/
theorem firstAtS_own (q : Params.First) (gp : GPar) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (firstSegmentOpening q gp : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    s'.check.frame.own = (idsOf (firstPar q gp) s.st.oracles.size).extract 0
      (s.check.frame.atMoment 0).length := by
  obtain ⟨g, mask, e, _, _⟩ := firstAtS_frame q gp s s' r₁ r₂ gs h
  rw [e]
  exact Array.empty_append

/-- The list of kept copies is as it was. -/
theorem firstAtS_keptBefore (q : Params.First) (gp : GPar) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (firstSegmentOpening q gp : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    s'.check.frame.keptBefore = s.check.frame.keptBefore := by
  obtain ⟨g, mask, e, _, _⟩ := firstAtS_frame q gp s s' r₁ r₂ gs h
  rw [e]

/-- The i-th of the first k numbers. -/
theorem ownIds_get (P : Par) (n₀ k i : Nat) (hk : k ≤ P.sent.size) (hi : i < k) :
    ((idsOf P n₀).extract 0 k)[i]? = some (n₀ + i) := by
  have e := idsOf_get P n₀ i (by omega)
  rw [Array.getElem?_eq_getElem (by rw [idsOf_size]; omega)] at e
  rw [Array.getElem?_extract_of_lt (by rw [idsOf_size]; omega)]
  simpa using e

end VerifiableInference.Desc.K1
