-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/SumTotalExt.lean: CONDITIONAL.

What is here. At the three product levels of the feed-forward layers' rounds the total of the job's
cube reads as the library's multilinear extension (`Blocks.ext`), at the level's point, of the
product of the two tables' entries. And the squares' point, coordinate by coordinate. Statements and
proofs.

  `level_total_ext`, `sq_total_ext`   **the total as an extension**
  `squares_total_ext`, `gated_total_ext`, `gated2_total_ext`   at the row's own jobs
  `pt_append_left`, `pt_append_right`, `squares_pt_first`, `squares_pt_half`,
     `squares_pt_last`   the squares' point: the point on the norms' numbers; the reading of the
     word for 1/2 for each bit of a feature; the token point

Limits. The one premise: the point has as many coordinates as the level has variables (where a cube
fits it has: `fits_way`, SumPoints.lean). At every reading into a field. THE TABLES' ENTRIES STAND
AS READINGS OF THE HONEST PARTS' OWN WORDS: that they are the library's terms at the committed cells
is not said here; nor that a verifier's start form is worth this extension. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SumLevels
import Johnson.Desc.ProofFile.Honest.K4.Law.SumPoints

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE oneE invE)
open OnBytes.Model (Reading orderRange ofNat)
open OnBytes.Model.Layer (downFrom normsStart)
open OnBytes.Road (pt)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## 1 The total as an extension -/

/-- **A product level of two tables.** -/
theorem level_total_ext (mu : ℕ) (order : List ℕ) (rho : Array E) (t : Tab × Tab)
    (hs : rho.size = mu) :
    ρ.val (levelJob mu order rho t).cube.total =
      Blocks.ext mu (fun X => ρ.val (t.1.getD X zeroE) * ρ.val (t.2.getD X zeroE)) (pt ρ rho) := by
  rw [total_ext ρ (levelJob mu order rho t).cube rho rfl hs]
  refine Blocks.ext_congr (fun X _ => ?_) _
  rw [termsAt_read]
  show ρ.val oneE * (ρ.val (t.1.getD X zeroE) * ρ.val (t.2.getD X zeroE)) + 0 = _
  rw [ρ.one, one_mul, add_zero]

/-- **The squares' job, of its table.** -/
theorem sq_total_ext (mu : ℕ) (rho : Array E) (t : Tab) (hs : rho.size = mu) :
    ρ.val (sqJobOf mu rho t).cube.total =
      Blocks.ext mu (fun X => ρ.val (t.getD X zeroE) * ρ.val (t.getD X zeroE)) (pt ρ rho) := by
  rw [total_ext ρ (sqJobOf mu rho t).cube rho rfl hs]
  refine Blocks.ext_congr (fun X _ => ?_) _
  rw [termsAt_read]
  show ρ.val oneE * (ρ.val (t.getD X zeroE) * ρ.val (t.getD X zeroE)) + 0 = _
  rw [ρ.one, one_mul, add_zero]

/-! ## 2 At the row's own jobs -/

/-- The squares: where the maker returns. -/
theorem squares_total_ext (Q : K4Pub) (w : K4In) (p : Pts) (j : Job)
    (hj : jobSquares Q w p = some j) :
    ρ.val j.cube.total =
      Blocks.ext Q.P.rd.muV (fun X => ρ.val ((squaresTab Q w p.gp).getD X zeroE) *
        ρ.val ((squaresTab Q w p.gp).getD X zeroE))
        (pt ρ (normsStart Q.P.y 0 p.gp p.rhoI p.PV).2) := by
  rw [jobSquares_eq] at hj
  split at hj
  · rename_i hf
    obtain rfl := Option.some.inj hj
    exact sq_total_ext ρ _ _ _ (fits_way _ hf _ rfl)
  · cases hj

/-- The first gated product: where the cube fits. -/
theorem gated_total_ext (Q : K4Pub) (p : Pts) (t : Tab × Tab)
    (hfit : (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
      (downFrom p.rs (Q.P.y.h.ll + Q.P.y.lPf) ++ ztOf Q p) t).cube.fits = true) :
    ρ.val (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
      (downFrom p.rs (Q.P.y.h.ll + Q.P.y.lPf) ++ ztOf Q p) t).cube.total =
      Blocks.ext Q.P.rd.muH (fun X => ρ.val (t.1.getD X zeroE) * ρ.val (t.2.getD X zeroE))
        (pt ρ (downFrom p.rs (Q.P.y.h.ll + Q.P.y.lPf) ++ ztOf Q p)) :=
  level_total_ext ρ _ _ _ t (fits_way _ hfit _ rfl)

/-- The second gated product: where the cube fits. -/
theorem gated2_total_ext (Q : K4Pub) (p : Pts) (t : Tab × Tab)
    (hfit : (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
      (p.rhoM ++ downFrom p.rs Q.P.y.lfe ++ p.rt) t).cube.fits = true) :
    ρ.val (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
      (p.rhoM ++ downFrom p.rs Q.P.y.lfe ++ p.rt) t).cube.total =
      Blocks.ext Q.P.rd.muH2 (fun X => ρ.val (t.1.getD X zeroE) * ρ.val (t.2.getD X zeroE))
        (pt ρ (p.rhoM ++ downFrom p.rs Q.P.y.lfe ++ p.rt)) :=
  level_total_ext ρ _ _ _ t (fits_way _ hfit _ rfl)

/-! ## 3 The squares' point -/

/-- A point laid in front of another: its own coordinates. -/
theorem pt_append_left (a b : Array E) (j : ℕ) (h : j < a.size) : pt ρ (a ++ b) j = pt ρ a j := by
  unfold pt
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_append_left h]

/-- The other's. -/
theorem pt_append_right (a b : Array E) (j : ℕ) : pt ρ (a ++ b) (a.size + j) = pt ρ b j := by
  unfold pt
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- The squares' point begins with the point on the norms' numbers. -/
theorem squares_pt_first (y : OnBytes.Model.Layer.Lay) (sW : ℕ) (gp rhoI PV : Array E) (j : ℕ)
    (h : j < rhoI.size) : pt ρ (normsStart y sW gp rhoI PV).2 j = pt ρ rhoI j := by
  show pt ρ (rhoI ++ Array.replicate y.lPd (invE (ofNat 2)) ++ PV) j = _
  rw [pt_append_left ρ _ _ j (by rw [Array.size_append]; omega), pt_append_left ρ _ _ j h]

/-- Then the reading of the word for 1/2 for each bit of a feature; that it is 1/2 in K is not said
here. -/
theorem squares_pt_half (y : OnBytes.Model.Layer.Lay) (sW : ℕ) (gp rhoI PV : Array E) (j : ℕ)
    (h : j < y.lPd) :
    pt ρ (normsStart y sW gp rhoI PV).2 (rhoI.size + j) = ρ.val (invE (ofNat 2)) := by
  show pt ρ (rhoI ++ Array.replicate y.lPd (invE (ofNat 2)) ++ PV) (rhoI.size + j) = _
  rw [pt_append_left ρ _ _ _ (by rw [Array.size_append, Array.size_replicate]; omega),
    pt_append_right]
  unfold pt
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, if_pos h]
  rfl

/-- Then the token point. -/
theorem squares_pt_last (y : OnBytes.Model.Layer.Lay) (sW : ℕ) (gp rhoI PV : Array E) (j : ℕ) :
    pt ρ (normsStart y sW gp rhoI PV).2 (rhoI.size + y.lPd + j) = pt ρ PV j := by
  show pt ρ (rhoI ++ Array.replicate y.lPd (invE (ofNat 2)) ++ PV) (rhoI.size + y.lPd + j) = _
  have e : rhoI.size + y.lPd =
      (rhoI ++ Array.replicate y.lPd (invE (ofNat 2))).size := by
    rw [Array.size_append, Array.size_replicate]
  rw [e, pt_append_right]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.level_total_ext
#print axioms ProofFile.Honest.K4.sq_total_ext
#print axioms ProofFile.Honest.K4.squares_total_ext
#print axioms ProofFile.Honest.K4.gated_total_ext
#print axioms ProofFile.Honest.K4.gated2_total_ext
#print axioms ProofFile.Honest.K4.pt_append_left
#print axioms ProofFile.Honest.K4.pt_append_right
#print axioms ProofFile.Honest.K4.squares_pt_first
#print axioms ProofFile.Honest.K4.squares_pt_half
#print axioms ProofFile.Honest.K4.squares_pt_last
