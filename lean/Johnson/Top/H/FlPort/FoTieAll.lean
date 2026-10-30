-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoTieAll.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoTieAll.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  tieLoop_is
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  Filled, Later, Later.refl, LedAt, Same, Sized, Stretch, Stretch.refl, TieInv, flEv, flEv_app,
  same_took, stepEvs, stepEvs_flat, stepEvs_rds, tieGo_snoc, tieInv_zero, tieOff, tieOff_succ,
  tieSizes, took, took_took
The comments on the declarations are the library's, under the same swap: where they say "run" or
"view", read: on a tape.

Limits. What is proved here is proved of the flat functions alone, and a flat function tests less of
the plan than the program's routine (the paragraph "Not claimed" in the head of
OnBytes/K/Kc/Flat.lean). Nothing is said where a function refuses. A tie: it has no error term. If
the source file turns, this copy does not follow by itself. In the list of names a use by dot
notation on a hypothesis is not seen, and a short name may stand once too often. That no routine
in a context is reached from a statement or a proof here is meant, and is not shown in this
library.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoTieAll
import Johnson.Top.H.FlPort.Kit
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun
import Johnson.Top.H.FlPort.FoTieRun
import Johnson.Top.H.FlPort.FoRds
import Johnson.Top.H.FlPort.FoHeard
import Johnson.Top.H.FlPort.PscRounds
import Johnson.Top.H.FlPort.FoTieInv

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV OnBytes OnBytes.Model OnBytes.PscRun

section
variable {K : Type} [CommRing K] (ρ : Reading K) (N : Nums Pl K) (lam : K) (base : ℕ)

/-- The first n steps of the tie. -/
theorem tieLoop_is (a : E) (ha : ρ.val a = fac N lam)
    (hLed : ∀ j, j < 31 → LedAt (N.ledTie j) (base + tieOff j) [3] (if j = 0 then 3 else 2))
    (F0 : Fork) (c0 : Tape) (hF0 : Sized F0) (hb : F0.next = base) :
    ∀ n, n ≤ 31 → ∀ (s : Forest.TieStep) (F : Fork) (c : Tape),
      ((List.range n).foldlM (lkTieStep a) {}) F0 c0 = .ok ((s, F), c) →
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

end Fo.Tp
