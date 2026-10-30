-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/FrameRenumbered.lean: the maker of a code switch's frame feels no number of a
message: at two statements, two carried rows and two targets with one public side BY PLACE, the two
frames are one but for g's number and the kept members' old and new numbers. Theorems.

  `places_bare`, `rowBits_bare`: the places of the rest and a table's row bits hang on the target's
     shape and its cut for the rest.
  `alike_get`: what `Alike` (FrameRenumber.lean) says at one place.
  `frame_guard`: where the maker returns a frame there is one new number for each kept member.
  `frame_renumber`: the maker's value at (S, old, T, g, anew) is `renumber` of its value at
     (S₀, old₀, T₀, g₀, anew₀).
Limits: nothing on fronts here (FrameOne.lean). Nothing on soundness.

-/
import Johnson.Top.H0.K2Hands.FrameRenumber

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes

theorem rowBits_bare {T T₀ : SwitchTarget} (t1 : T.shape = T₀.shape) (p : Part) :
    switchRowBits T p = switchRowBits T₀ p := by
  unfold switchRowBits
  rw [t1]

theorem places_bare {cs cs₀ : Codes} (hc : cs = cs₀) {T T₀ : SwitchTarget}
    (t1 : T.shape = T₀.shape) (t3 : T.rest = T₀.rest) :
    SwitchPlaces.make cs T = SwitchPlaces.make cs₀ T₀ := by
  subst hc
  have e : ∀ p, switchRowLength cs T p = switchRowLength cs T₀ p := by
    intro p
    cases p <;> simp [switchRowLength, t1]
  unfold SwitchPlaces.make
  simp only [t1, t3, e, rowBits_bare t1]

theorem alike_length {S S₀ : Statement} {ks ks₀ : List ℕ} (h : Alike S S₀ ks ks₀) :
    ks.length = ks₀.length := List.Forall₂.length_eq h

theorem alike_get {S S₀ : Statement} {ks ks₀ : List ℕ} (h : Alike S S₀ ks ks₀) (i : ℕ)
    (hi : i < ks.length) (hi₀ : i < ks₀.length) :
    (S.oracles[ks[i]]?).map (·.shape) = (S₀.oracles[ks₀[i]]?).map (·.shape) :=
  (List.forall₂_iff_get.1 h).2 i hi hi₀

/-- The maker's own guard: one new message for each kept member. -/
theorem frame_guard {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : ℕ} {anew : Array ℕ}
    {W : SwitchFrame} (h : switchFrame S old T g anew = some W) :
    anew.size = (switchKept old).size := by
  unfold switchFrame at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨_, _, _, _, _, _, _, hg, _⟩ := h
  by_contra hn
  simp [guard, hn] at hg

/-- **THE MAKER FEELS NO NUMBER.** -/
theorem frame_renumber {S S₀ : Statement} {old old₀ : SingleRows} {T T₀ : SwitchTarget}
    {g g₀ : ℕ} {anew anew₀ : Array ℕ} {W₀ : SwitchFrame}
    (h : switchFrame S₀ old₀ T₀ g₀ anew₀ = some W₀) (hc : S.codes = S₀.codes)
    (h1 : old.code = old₀.code) (h2 : old.maskCode = old₀.maskCode)
    (h3 : old.masks = old₀.masks) (h4 : old.keptRows = old₀.keptRows)
    (hk : Alike S S₀ (switchKept old).toList (switchKept old₀).toList)
    (t1 : T.shape = T₀.shape) (t2 : T.main = T₀.main) (t3 : T.rest = T₀.rest)
    (hg : (S.oracles[g]?).map (·.shape) = (S₀.oracles[g₀]?).map (·.shape))
    (ha : anew.size = (switchKept old).size) :
    switchFrame S old T g anew = some (renumber W₀ g (switchKept old) anew) := by
  have hP := parts_alike hc h1 h2 h3 h4 hk
  have hpl := places_bare hc t1 t3
  have hn : (switchKept old).size = (switchKept old₀).size := by
    have := alike_length hk
    simpa using this
  unfold switchFrame at h ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h ⊢
  obtain ⟨code, e1, zk, e2, nc, e3, u, -, rfl⟩ := h
  refine ⟨code, by rw [hc, h1]; exact e1, zk, by rw [hc, h2]; exact e2, nc,
    by rw [hc, t1]; exact e3, (), by simp [guard, ha], ?_⟩
  unfold renumber
  simp only [hP, hpl, h3, t2, t3, rowBits_bare t1, tableBits_at hc hg, SwitchFrame.mk.injEq,
    true_and, and_true]
  refine List.ext_getElem? fun i => ?_
  simp only [List.getElem?_map, List.getElem?_mapIdx, hn]
  by_cases hi : i < (switchKept old₀).size
  · have hi' : i < (switchKept old).size := by rw [hn]; exact hi
    have e := alike_get hk i (by simpa using hi') (by simpa using hi)
    have a1 : (switchKept old).getD i noId = (switchKept old).toList[i]'(by simpa using hi') := by
      simp [Array.getD, hi']
    have a2 : (switchKept old₀).getD i noId =
        (switchKept old₀).toList[i]'(by simpa using hi) := by
      simp [Array.getD, hi]
    rw [List.getElem?_range hi]
    simp only [Option.map_some, Option.some.injEq, KeptPlace.mk.injEq, true_and, and_true]
    rw [a1, a2]
    exact ⟨by rw [shape_at e], rowBits_at e _, padOf_at hc e⟩
  · rw [List.getElem?_eq_none (by simpa using hi)]
    rfl

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.frame_renumber
