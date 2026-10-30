-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoTieNums.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoTieNums.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  tie_nums, point_five
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  Filled, FormIs, Later, RowIs, Same, Sized, Stretch, fTie_off, flEv, ledAt_tie, numsF, rhoT,
  tieOff, tieSizes, tieTrace, took
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
import OnBytes.Tie.Pv.Lookup.Forest.FoTieNums
import Johnson.Top.H.FlPort.Kit
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun
import Johnson.Top.H.FlPort.FoTieRun
import Johnson.Top.H.FlPort.FoRds
import Johnson.Top.H.FlPort.FoHeard
import Johnson.Top.H.FlPort.PscRounds
import Johnson.Top.H.FlPort.FoTieEnd
import Johnson.Top.H.FlPort.FoTieAll
import Johnson.Top.H.FlPort.FoTieInv

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV OnBytes OnBytes.Model OnBytes.PscRun Cb.Fo.Walk

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- What lkTie returns, at the flat function's numbers of a shape. -/
theorem tie_nums (h : Forest.Shape) (lm : ℕ) (θ lam : K) (a : E) (F0 G : Fork) (c0 c' : Tape)
    (ha : ρ.val a = fac (numsF h lm F0.next θ) lam) (hF0 : Sized F0) (T : Forest.Tie)
    (hr : lkTie a F0 c0 = .ok ((T, G), c')) :
    ∃ l scs c1 pt, Evs l c0 c1 ∧ Rds l ∧ Evs [.point .lkpPlanes 5 pt] c1 c' ∧
      (∀ rest, tieGo 31 0 0 (flEv ρ (l ++ [.point .lkpPlanes 5 pt]) ++ rest) =
        (scs, ([], rdA ρ pt) :: rest)) ∧
      Later F0 G ∧ Sized G ∧ Same (took F0 (tieOff 31)) G ∧
      (∀ j, Filled G j ↔ Filled F0 j ∨ (F0.next ≤ j ∧ j < F0.next + tieOff 31)) ∧
      T.rows.size = 31 ∧
      (∀ i, i < 31 → RowIs ρ G (T.rows.getD i {})
        ((tieRowsR (numsF h lm F0.next θ) lam scs.reverse).reverse.getD i ⟨[], 0⟩)) ∧
      T.sZ = F0.next + 4 ∧
      FormIs ρ G (Aff.slot T.sZ) (tK (tieTrace lam scs (rdA ρ pt)))
        (fK (numsF h lm F0.next θ) (tieTrace lam scs (rdA ρ pt))) ∧
      rdA ρ T.rhoT = (rdA ρ pt).reverse ∧
      (pt.size = 5 → FormIs ρ G T.cT (tgT0 (numsF h lm F0.next θ) (tieTrace lam scs (rdA ρ pt)))
        (incT0 (numsF h lm F0.next θ) (tieTrace lam scs (rdA ρ pt)))) ∧
      Stretch F0 G (tieOff 31) ∧
      (flEv ρ l).map (fun r => (r.1.length, r.2.length)) = (List.range 31).flatMap tieSizes :=
  tie_is ρ (numsF h lm F0.next θ) lam F0.next a ha rfl rfl
    (fun j hj => by
      rw [← fTie_off h j (by omega)]
      exact ledAt_tie h F0.next j hj)
    F0 G c0 c' hF0 rfl T hr

/-- On a view the point that joins the planes' roots has five elements. -/
theorem point_five {l : List Ev} {c0 c1 c' : Tape} {pt : Array E} (hc : Clean c0) (h1 : Evs l c0 c1)
    (hl : Rds l) (h2 : Evs [.point .lkpPlanes 5 pt] c1 c') : pt.size = 5 := by
  obtain ⟨_, ht, _⟩ := rds_took Reading.gl hl hc h1
  obtain ⟨_, _, _, _, hs⟩ := round_point _ _ _ _ _ ht.2.1 h2
  exact hs

end

end Fo.Tp
