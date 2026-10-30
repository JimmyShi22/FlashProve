-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoTieNums.lean.
The tie of a sub-proof's lookup, at the flat function's own numbers of a shape.

States:
  fTie_off: the ledger's first slot of step j of the tie is the number of slots that the steps
    before it take.
  tie_nums: Fo.tie_is at the numbers Fo.numsF h lm jLK θ, jLK the first free slot before the run. Of
    its premises these are left: the state fits, and the public factor reads as the flat function's.
  point_five: on a view with no message open, behind a row of rounds, the point has five elements:
    so there the clause of tie_nums on the start form of the table side holds without its premise.
Limits: for a dry run nothing is said on the number of elements of the point.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoTieEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun Cb.Fo.Walk

theorem fTie_off (h : Forest.Shape) : ∀ j, j ≤ 31 → (FoNums.S h).fTie j = tieOff j
  | 0, _ => rfl
  | j + 1, hj => by
    rw [first_tie h j (by omega), fTie_off h j (by omega), ← tieOff_succ]
    show tieOff j + (1 + 0 * _ + 3 + (if j = 0 then 3 else 2)) = _
    omega

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- What Forest.tie returns, at the flat function's numbers of a shape. -/
theorem tie_nums (h : Forest.Shape) (lm : ℕ) (θ lam : K) (a : E) (F0 G : Fork) (c0 c' : Ctx)
    (ha : ρ.val a = fac (numsF h lm F0.next θ) lam) (hF0 : Sized F0) (T : Forest.Tie)
    (hr : Forest.tie a F0 c0 = .ok ((T, G), c')) :
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
theorem point_five {l : List Ev} {c0 c1 c' : Ctx} {pt : Array E} (hc : Clean c0) (h1 : Evs l c0 c1)
    (hl : Rds l) (h2 : Evs [.point .lkpPlanes 5 pt] c1 c') : pt.size = 5 := by
  obtain ⟨_, ht, _⟩ := rds_took Reading.gl hl hc h1
  obtain ⟨_, _, _, _, hs⟩ := round_point _ _ _ _ _ ht.2.1 h2
  exact hs

end
end Fo
