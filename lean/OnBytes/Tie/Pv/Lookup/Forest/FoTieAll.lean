-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoTieAll.lean.
The tie of a sub-proof's lookup: the byte-level verifier's whole loop of steps, read into a
commutative ring, is the flat function's.

States, for every reading ρ of the byte-level field:
  stepEvs_rds: the six calls of a step are three rounds.
  tieLoop_is: if the first n steps (n at most 31) return, then a list of calls leads from the run's
    first context to its last (Evs); it is a row of rounds on which the flat function takes its n
    steps; the state left is a later one, in which the steps' own slots, and no others, are newly
    filled and nothing else is turned (Fo.Stretch); Fo.TieInv holds of what the steps returned; and
    each round sends and draws as many as tieSizes says.
Premises: the state fits (Sized), and its first free slot is base; the public factor reads as the
flat function's; the flat function's places of each step's masks lie from the step's first slot on
(Fo.LedAt).

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoTieInv
import OnBytes.Tie.Pv.Lookup.Forest.FoRds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun

theorem stepEvs_rds (mu eps : E) (sent : Array E) (beta : E) (n : ℕ) (v : Array E) :
    Rds (stepEvs mu eps sent beta n v) :=
  .sum mu _ eps (.readNZ 3 sent _ beta (.values n v _ .nil))

/-- How many scalars each round of step j sends, and how many elements it draws. -/
def tieSizes (j : ℕ) : List (ℕ × ℕ) := [(1, 1), (3, 1), (if j = 0 then 3 else 2, 0)]

theorem tieOff_succ (n : ℕ) : tieOff n + (1 + (3 + if n = 0 then 3 else 2)) = tieOff (n + 1) := by
  cases n with
  | zero => rfl
  | succ m =>
    simp only [tieOff, Nat.succ_ne_zero, if_false]
    omega

section
variable {K : Type} [CommRing K] (ρ : Reading K) (N : Nums Pl K) (lam : K) (base : ℕ)

/-- The first n steps of the tie. -/
theorem tieLoop_is (a : E) (ha : ρ.val a = fac N lam)
    (hLed : ∀ j, j < 31 → LedAt (N.ledTie j) (base + tieOff j) [3] (if j = 0 then 3 else 2))
    (F0 : Fork) (c0 : Ctx) (hF0 : Sized F0) (hb : F0.next = base) :
    ∀ n, n ≤ 31 → ∀ (s : Forest.TieStep) (F : Fork) (c : Ctx),
      ((List.range n).foldlM (Forest.tieStep a) {}) F0 c0 = .ok ((s, F), c) →
      ∃ l scs, Evs l c0 c ∧ Rds l ∧ (∀ rest, tieGo n 0 0 (flEv ρ l ++ rest) = (scs, rest)) ∧
        Later F0 F ∧ Same (took F0 (tieOff n)) F ∧
        (∀ j, Filled F j ↔ Filled F0 j ∨ (base ≤ j ∧ j < base + tieOff n)) ∧
        TieInv ρ N lam base n s F scs ∧ Stretch F0 F (tieOff n) ∧
        (flEv ρ l).map (fun r => (r.1.length, r.2.length)) = (List.range n).flatMap tieSizes
  | 0, _, s, F, c, h => by
    obtain ⟨e1, rfl⟩ := Prod.mk.inj ((foldlM_nil_ok _ _ _ _ _).1 h)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
    exact ⟨[], [], rfl, .nil, fun _ => rfl, Later.refl _, rfl,
      fun j => ⟨Or.inl, fun hj => hj.elim id fun hh => absurd hh.2 (by simp [tieOff]; omega)⟩,
      tieInv_zero ρ N lam base _ hF0 hb, Stretch.refl _, rfl⟩
  | n + 1, hn, s', G, c', h => by
    rw [List.range_succ, List.foldlM_append, bind_ok] at h
    obtain ⟨s, F, c, h1, h2⟩ := h
    obtain ⟨s2, F2, c2, h3, h4⟩ := (foldlM_cons_ok _ _ _ _ _ _ _).1 h2
    obtain ⟨e1, rfl⟩ := Prod.mk.inj ((foldlM_nil_ok _ _ _ _ _).1 h4)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
    obtain ⟨l, scs, i1, i2, i3, i4, i5, i6, inv, i7, i8⟩ :=
      tieLoop_is a ha hLed F0 c0 hF0 hb n (by omega) s F c h1
    obtain ⟨mu, eps, sent, beta, v, sc, j1, j2, j3, j4, j5, inv', j6, j7, j8⟩ :=
      tieStep_is ρ N lam base a ha n (hLed n (by omega)) s s' F G c c' scs inv h3
    refine ⟨l ++ stepEvs mu eps sent beta (if n = 0 then 3 else 2) v, scs ++ [sc],
      Evs.append i1 j1, i2.append (stepEvs_rds _ _ _ _ _ _), fun rest => ?_, i4.trans j3, ?_, ?_,
      inv', ?_, ?_⟩
    rotate_right 2
    · rw [← tieOff_succ]
      exact i7.trans ⟨j4, j5, j6⟩
    · rw [flEv_app ρ (i2.closed ρ), List.map_append, i8, List.range_succ, List.flatMap_append,
        stepEvs_flat]
      simp [OnBytes.PscTie.flH, OnBytes.PscTie.flR, tieSizes, j7, j8]
    · rw [flEv_app ρ (i2.closed ρ), List.append_assoc, tieGo_snoc, i3, j2]
    · have := (same_took i5 (1 + (3 + if n = 0 then 3 else 2))).trans j4
      rwa [took_took, tieOff_succ] at this
    · intro j
      rw [j5, i6, inv.next, ← tieOff_succ]
      constructor
      · rintro ((hj | hj) | hj)
        · exact Or.inl hj
        · exact Or.inr ⟨hj.1, by omega⟩
        · exact Or.inr ⟨by omega, by omega⟩
      · rintro (hj | hj)
        · exact Or.inl (Or.inl hj)
        · by_cases hlt : j < base + tieOff n
          · exact Or.inl (Or.inr ⟨hj.1, hlt⟩)
          · exact Or.inr ⟨by omega, by omega⟩

end
end Fo
