-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/KeySizes.lean: how many coordinates the points have that a hearing of
the kind "lookup" leaves for the parts' keys: as many as the part's keys have bits; and there is one
point for each part.

Main names:
  levels_size: a run of n levels adds n coordinates to the point.
  keys_size: keysG: the point of part q has as many coordinates as the part's number says.
  messages_keys, heard_keys: a run of messagesG, and a hearing, that returns: g.keys has a member a
    part, and the sizes.

Limits. Sizes alone.

-/
import Johnson.Desc.First.Look.KeyLaw.Out

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Slice OnBytes.K.Kc
open OnBytes.Model (Fork Aff)
open First.Prod (Carried turn level layBack)

/-- A run of n levels adds n coordinates to the point. -/
theorem levels_size (more : ℕ) (orders : ℕ → List ℕ) : ∀ (n l : ℕ) (cf cf' : Carried)
    (F G : Fork) (t u : Tape),
    ((List.range' l n).foldlM (m := Fl) (fun s i => turn (orders (more + i)) s (more + i)) cf) F t =
      some (cf', G, u) →
    cf.point.size = more + l → cf'.point.size = more + l + n := by
  intro n
  induction n with
  | zero =>
    intro l cf cf' F G t u h hz
    cases pure_some h
    exact hz
  | succ n ih =>
    intro l cf cf' F G t u h hz
    rw [List.range'_succ, List.foldlM_cons] at h
    replace h := bind_some h
    obtain ⟨cf1, G1, u1, h1, h⟩ := h
    unfold turn at h1
    replace h1 := bind_some h1
    obtain ⟨o, G2, u2, h2, h1⟩ := h1
    cases pure_some h1
    unfold level at h2
    replace h2 := bind_some h2
    obtain ⟨w, G3, u3, h3, h2⟩ := h2
    replace h2 := bind_some h2
    obtain ⟨xi, G4, u4, h4, h2⟩ := h2
    cases pure_some h2
    have := ih (l + 1) _ cf' _ G _ u h (by
      show (#[xi] ++ layBack (more + l) (orders (more + l)) (w.challenges.take (more + l))).size =
        _
      rw [Array.size_append, layBack_size]
      show 1 + (more + l) = _
      omega)
    omega

/-- **The parts' key trees: the points' sizes.** -/
theorem keys_size (f : Face) : ∀ (vs : List ℕ) (i : ℕ) (Cs' : List Aff) (rows : Array Aff)
    (F G : Fork) (t u : Tape) (res : Array Aff × List (Array E × Aff)),
    keysG f (vs.zipIdx i) Cs' rows F t = some (res, G, u) →
    ∀ q < res.2.length, (res.2.getD q (#[], {})).1.size = vs.getD q 0 := by
  intro vs
  induction vs with
  | nil =>
    intro i Cs' rows F G t u res h
    have h' : (pure (rows, []) : Fl (Array Aff × List (Array E × Aff))) F t = some (res, G, u) := by
      cases Cs' <;> exact h
    cases pure_some h'
    exact fun q hq => (by cases hq)
  | cons v vs ih =>
    intro i Cs' rows F G t u res h
    cases Cs' with
    | nil =>
      have h' : (pure (rows, []) : Fl (Array Aff × List (Array E × Aff))) F t = some (res, G, u) :=
          h
      cases pure_some h'
      exact fun q hq => (by cases hq)
    | cons C Cs' =>
      rw [List.zipIdx_cons] at h
      unfold keysG at h
      replace h := bind_some h
      obtain ⟨k, G1, u1, h1, h⟩ := h
      replace h := bind_some h
      obtain ⟨y, G2, u2, h2, h⟩ := h
      cases pure_some h
      unfold First.Prod.run at h1
      rw [List.range_eq_range'] at h1
      have e1 := levels_size 0 (f.orders i) v 0 _ k F G1 t u1 h1 rfl
      have r2 := ih (i + 1) Cs' k.rows G1 _ u1 _ y h2
      intro q hq
      cases q with
      | zero =>
        show k.point.size = v
        omega
      | succ q => exact r2 q (by simpa using hq)

/-- A run of messagesG that returns: there is a point and a form for each part, and the point of
part q has as many coordinates as the part's number says. -/
theorem messages_keys {f : Face} {F G : Fork} {t u : Tape} {g : HeardG} (hs : f.shifted = false)
    (h : messagesG f F t = some (g, G, u)) :
    g.keys.length = f.parts.length ∧
      ∀ q < f.parts.length, (g.keys.getD q (#[], {})).1.size = f.parts.getD q 0 := by
  unfold messagesG at h
  rw [hs] at h
  replace h := bind_some h
  obtain ⟨slot0, F0, t0, e0, h⟩ := h
  replace e0 := slot_some e0
  obtain ⟨rfl, rfl, rfl⟩ := e0
  replace h := bind_some h
  obtain ⟨w1, F1, t1, e1, h⟩ := h
  replace e1 := owe_some e1
  obtain ⟨rfl, rfl⟩ := e1
  replace h := bind_some h
  obtain ⟨w2, F2, t2, e2, h⟩ := h
  replace e2 := owe_some e2
  obtain ⟨rfl, rfl⟩ := e2
  replace h := bind_some h
  obtain ⟨w3, F3, t3, e3, h⟩ := h
  replace e3 := owe_some e3
  obtain ⟨rfl, rfl⟩ := e3
  replace h := bind_some h
  obtain ⟨theta, F4, t4, e4, h⟩ := h
  cases pure_some e4
  replace h := bind_some h
  obtain ⟨alpha, F5, t5, e5, h⟩ := h
  replace h := bind_some h
  obtain ⟨⟨rows1, sZ, sG⟩, F6, t6, e6, h⟩ := h
  replace h := bind_some h
  obtain ⟨⟨rows2, roots⟩, F7, t7, e7, h⟩ := h
  replace h := bind_some h
  obtain ⟨x3, F8, t8, e8, h⟩ := h
  replace h := bind_some h
  obtain ⟨⟨rows3, keys⟩, F9, t9, e9, h⟩ := h
  replace h := bind_some h
  obtain ⟨_, F10, t10, e10, h⟩ := h
  replace e10 := must_some e10
  obtain ⟨hk, rfl, rfl⟩ := e10
  replace h := bind_some h
  obtain ⟨table, F11, t11, e11, h⟩ := h
  replace h := bind_some h
  obtain ⟨_, F12, t12, e12, h⟩ := h
  replace e12 := must_some e12
  obtain ⟨-, rfl, rfl⟩ := e12
  replace h := bind_some h
  obtain ⟨lv0, F13, t13, e13, h⟩ := h
  replace h := bind_some h
  obtain ⟨⟨zb0, lv⟩, F14, t14, e14, h⟩ := h
  replace h := bind_some h
  obtain ⟨x5, F15, t15, e15, h⟩ := h
  replace h := bind_some h
  obtain ⟨bits, F16, t16, e16, h⟩ := h
  replace h := bind_some h
  obtain ⟨sl, F17, t17, e17, h⟩ := h
  replace e17 := slot_some e17
  obtain ⟨rfl, rfl, rfl⟩ := e17
  replace h := bind_some h
  obtain ⟨_, F18, t18, e18, h⟩ := h
  replace e18 := must_some e18
  obtain ⟨hmust, rfl, rfl⟩ := e18
  cases pure_some h
  have hk' : keys.length = f.parts.length := by simpa using hk
  refine ⟨hk', fun q hq => ?_⟩
  exact keys_size f f.parts 0 roots rows2 _ _ _ _ _ e9 q (by rw [hk']; exact hq)

/-- **A hearing that returns.** -/
theorem heard_keys {f : Face} {es : List Fmt.Entry} {F G : Fork} {rs : List Fmt.RoundView} {g : HeardG}
    (hs : f.shifted = false) (h : hearE f es F rs = some (g, G)) :
    g.keys.length = f.parts.length ∧
      ∀ q < f.parts.length, (g.keys.getD q (#[], {})).1.size = f.parts.getD q 0 := by
  obtain ⟨-, t, -, hm⟩ := hearE_inv h
  exact messages_keys hs hm

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.levels_size
#print axioms VerifiableInference.Desc.K3.KeyLaw.keys_size
#print axioms VerifiableInference.Desc.K3.KeyLaw.heard_keys
