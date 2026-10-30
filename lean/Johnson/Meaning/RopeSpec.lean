-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/RopeSpec.lean: ropeTable's entries are pairList's words: the bridge from the
verifier's routine, which writes into an array, to the list recursion of
Johnson/Meaning/RopeLists.lean.

Main theorems.
  tokens_spec: what ropeTokens does to an array: the two words of pair i for the tokens t to
    t + n - 1 are tokList's; entries of other pairs and of earlier tokens stay.
  pairs_spec: the same for ropePairs and pairList.
  table_spec: entry t half + i of ropeTable is the first word, entry (T + t) half + i the second
    word, of member t of member i of pairList.
General in all numbers. Nothing is evaluated here.
-/
import Johnson.Meaning.RopeLists

set_option autoImplicit false

namespace Meaning.Rope

open OnBytes.Model.Layer (fxOne roundD cosSin turn ropeWord rootLoop ropeTokens ropePairs ropeTable)
open OnBytes (ceilLog2)

/-- The entry that a write changes. -/
theorem getD_set_self (a : Array Nat) {j : Nat} (hj : j < a.size) (v d : Nat) :
    (a.setIfInBounds j v).getD j d = v := by
  simp [Array.getD, hj]

/-- Another entry. -/
theorem getD_set_ne (a : Array Nat) {j k : Nat} (h : j ≠ k) (v d : Nat) :
    (a.setIfInBounds j v).getD k d = a.getD k d := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne h]

/-- Two places of one pair are one place only at one token. -/
theorem idx_ne {half i q q' : Nat} (hh : 0 < half) (h : q ≠ q') : q * half + i ≠ q' * half + i :=
  fun e => h (Nat.eq_of_mul_eq_mul_right hh (Nat.add_right_cancel e))

/-- The pair of a place. -/
theorem idx_mod {half i : Nat} (hi : i < half) (q : Nat) : (q * half + i) % half = i := by
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]

/-- A place of token q lies in an array of Q half entries, if q < Q. -/
theorem idx_lt {half i q Q : Nat} (hi : i < half) (hq : q < Q) : q * half + i < Q * half := by
  have h1 : (q + 1) * half ≤ Q * half := Nat.mul_le_mul_right _ hq
  rw [Nat.succ_mul] at h1
  omega

/-- What ropeTokens does to an array of 2 T half entries. -/
theorem tokens_spec (cs T half i : Nat) (p : Nat × Nat) (pf : Nat) (r : Int × Int) (hi : i < half) :
    ∀ (n t : Nat) (c s : Int) (a : Array Nat), a.size = 2 * T * half → t + n ≤ T →
      (ropeTokens cs T half i p pf r n t c s a).size = 2 * T * half ∧
      (∀ k, k < n →
        (ropeTokens cs T half i p pf r n t c s a).getD ((t + k) * half + i) 0 =
          ((tokList cs p pf r n t c s).getD k (0, 0)).1 ∧
        (ropeTokens cs T half i p pf r n t c s a).getD ((T + (t + k)) * half + i) 0 =
          ((tokList cs p pf r n t c s).getD k (0, 0)).2) ∧
      (∀ j, j % half ≠ i → (ropeTokens cs T half i p pf r n t c s a).getD j 0 = a.getD j 0) ∧
      (∀ q, q < t →
        (ropeTokens cs T half i p pf r n t c s a).getD (q * half + i) 0 =
          a.getD (q * half + i) 0 ∧
        (ropeTokens cs T half i p pf r n t c s a).getD ((T + q) * half + i) 0 =
          a.getD ((T + q) * half + i) 0)
  | 0, t, c, s, a, hs, _ =>
    ⟨hs, fun k hk => absurd hk (Nat.not_lt_zero k), fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩
  | n + 1, t, c, s, a, hs, ht => by
    have hh : 0 < half := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
    generalize hw1 : ropeWord cs (turn c s (cosSin
      (((roundD (t * p.1) p.2).1 * fxOne / (roundD (t * p.1) p.2).2 : Nat) -
        (t * pf : Nat) : Int))).1
      = w1
    generalize hw2 : ropeWord cs (turn c s (cosSin
      (((roundD (t * p.1) p.2).1 * fxOne / (roundD (t * p.1) p.2).2 : Nat) -
        (t * pf : Nat) : Int))).2
      = w2
    have eR : ropeTokens cs T half i p pf r (n + 1) t c s a =
        ropeTokens cs T half i p pf r n (t + 1) (turn c s r).1 (turn c s r).2
          ((a.setIfInBounds (t * half + i) w1).setIfInBounds ((T + t) * half + i) w2) := by
      rw [← hw1, ← hw2]
      rfl
    have eL : tokList cs p pf r (n + 1) t c s =
        (w1, w2) :: tokList cs p pf r n (t + 1) (turn c s r).1 (turn c s r).2 := by
      rw [← hw1, ← hw2]
      rfl
    rw [eR, eL]
    generalize ha' : (a.setIfInBounds (t * half + i) w1).setIfInBounds ((T + t) * half + i) w2 = a'
    have hs' : a'.size = 2 * T * half := by
      rw [← ha']
      simpa using hs
    obtain ⟨i1, i2, i3, i4⟩ := tokens_spec cs T half i p pf r hi n (t + 1) (turn c s r).1
      (turn c s r).2 a' hs' (by omega)
    have b1 : t * half + i < a.size := by
      rw [hs]
      exact idx_lt hi (by omega)
    have b2 : (T + t) * half + i < (a.setIfInBounds (t * half + i) w1).size := by
      rw [Array.size_setIfInBounds, hs]
      exact idx_lt hi (by omega)
    -- what the two writes do
    have g1 : a'.getD (t * half + i) 0 = w1 := by
      rw [← ha', getD_set_ne _ (idx_ne hh (by omega)), getD_set_self _ b1]
    have g2 : a'.getD ((T + t) * half + i) 0 = w2 := by
      rw [← ha', getD_set_self _ b2]
    have g3 : ∀ j, j ≠ t * half + i → j ≠ (T + t) * half + i → a'.getD j 0 = a.getD j 0 := by
      intro j h1 h2
      rw [← ha', getD_set_ne _ (Ne.symm h2), getD_set_ne _ (Ne.symm h1)]
    refine ⟨i1, fun k hk => ?_, fun j hj => ?_, fun q hq => ?_⟩
    · cases k with
      | zero =>
        obtain ⟨x1, x2⟩ := i4 t (Nat.lt_succ_self t)
        simp only [Nat.add_zero]
        rw [x1, x2, g1, g2]
        exact ⟨rfl, rfl⟩
      | succ k =>
        have e : t + (k + 1) = t + 1 + k := by omega
        rw [e]
        exact i2 k (by omega)
    · rw [i3 j hj]
      exact g3 j (fun e => hj (by rw [e]; exact idx_mod hi t))
        (fun e => hj (by rw [e]; exact idx_mod hi (T + t)))
    · obtain ⟨x1, x2⟩ := i4 q (by omega)
      rw [x1, x2]
      exact ⟨g3 _ (idx_ne hh (by omega)) (idx_ne hh (by omega)),
        g3 _ (idx_ne hh (by omega)) (idx_ne hh (by omega))⟩

/-- What ropePairs does to an array of 2 T half entries. -/
theorem pairs_spec (cs T half u : Nat) :
    ∀ (n i x : Nat) (a : Array Nat), a.size = 2 * T * half → i + n ≤ half →
      (ropePairs cs T half u n i x a).size = 2 * T * half ∧
      (∀ m, m < n → ∀ t, t < T →
        (ropePairs cs T half u n i x a).getD (t * half + (i + m)) 0 =
          (((pairList cs T u n x).getD m []).getD t (0, 0)).1 ∧
        (ropePairs cs T half u n i x a).getD ((T + t) * half + (i + m)) 0 =
          (((pairList cs T u n x).getD m []).getD t (0, 0)).2) ∧
      (∀ j, j % half < i → (ropePairs cs T half u n i x a).getD j 0 = a.getD j 0)
  | 0, i, x, a, hs, _ => ⟨hs, fun m hm => absurd hm (Nat.not_lt_zero m), fun _ _ => rfl⟩
  | n + 1, i, x, a, hs, hn => by
    have hi : i < half := by omega
    have eR : ropePairs cs T half u (n + 1) i x a =
        ropePairs cs T half u n (i + 1) (x * u / fxOne)
          (ropeTokens cs T half i (roundD x fxOne)
            ((roundD x fxOne).1 * fxOne / (roundD x fxOne).2)
            (cosSin ((roundD x fxOne).1 * fxOne / (roundD x fxOne).2 : Nat)) T 0 fxOne 0 a) := rfl
    have eL : pairList cs T u (n + 1) x =
        tokList cs (roundD x fxOne) ((roundD x fxOne).1 * fxOne / (roundD x fxOne).2)
          (cosSin ((roundD x fxOne).1 * fxOne / (roundD x fxOne).2 : Nat)) T 0 fxOne 0 ::
          pairList cs T u n (x * u / fxOne) := rfl
    rw [eR, eL]
    obtain ⟨k1, k2, k3, -⟩ := tokens_spec cs T half i (roundD x fxOne)
      ((roundD x fxOne).1 * fxOne / (roundD x fxOne).2)
      (cosSin ((roundD x fxOne).1 * fxOne / (roundD x fxOne).2 : Nat)) hi T 0 fxOne 0 a hs
      (by omega)
    obtain ⟨i1, i2, i3⟩ := pairs_spec cs T half u n (i + 1) (x * u / fxOne) _ k1 (by omega)
    refine ⟨i1, fun m hm t ht => ?_, fun j hj => ?_⟩
    · cases m with
      | zero =>
        have y := k2 t ht
        simp only [Nat.zero_add] at y
        simp only [Nat.add_zero]
        rw [i3 _ (by rw [idx_mod hi t]; omega), i3 _ (by rw [idx_mod hi (T + t)]; omega)]
        exact y
      | succ m =>
        have e : i + (m + 1) = i + 1 + m := by omega
        rw [e]
        exact i2 m (by omega) t ht
    · rw [i3 j (by omega)]
      exact k3 j (by omega)

/-- THE BRIDGE. Entry t half + i of the verifier's rotary table is the first word, and entry
(T + t) half + i the second word, of member t of member i of pairList. -/
theorem table_spec (cs theta0 dh lt : Nat) {t i : Nat} (ht : t < 2 ^ lt) (hi : i < dh / 2) :
    (ropeTable cs theta0 dh lt).getD (t * (dh / 2) + i) 0 =
      (((pairList cs (2 ^ lt) (uOf theta0 (dh / 2)) (dh / 2) fxOne).getD i []).getD t (0, 0)).1 ∧
    (ropeTable cs theta0 dh lt).getD ((2 ^ lt + t) * (dh / 2) + i) 0 =
      (((pairList cs (2 ^ lt) (uOf theta0 (dh / 2)) (dh / 2) fxOne).getD i []).getD t
        (0, 0)).2 := by
  have e : ropeTable cs theta0 dh lt = ropePairs cs (2 ^ lt) (dh / 2) (uOf theta0 (dh / 2)) (dh / 2)
      0 fxOne (Array.replicate (2 * 2 ^ lt * (dh / 2)) 0) := rfl
  obtain ⟨-, h2, -⟩ := pairs_spec cs (2 ^ lt) (dh / 2) (uOf theta0 (dh / 2)) (dh / 2) 0 fxOne
    (Array.replicate (2 * 2 ^ lt * (dh / 2)) 0) (by simp) (by omega)
  have y := h2 i hi t ht
  simp only [Nat.zero_add] at y
  rw [e]
  exact y

#print axioms tokens_spec
#print axioms pairs_spec
#print axioms table_spec

end Meaning.Rope
