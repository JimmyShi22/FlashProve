-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/PlanesWeight.lean: THE SMALLNESS TEST: BEHIND THE ADDING OF ALL THE SEGMENT's
CLAIMS, THE VALUE OF A WEIGHT ON A COLUMN ON WHICH AT MOST ONE PLAIN CLAIM BEARS, AND NO TIE AND NO
READ: that claim's own power of the batching element times what the claim lays there. And so the
weights on the three virtual rows of the bits' array: each of the three claims on the planes has one
run over all the array's columns. None of the library's goals.

  `OneOn fr k8 bk t r i k c`   of the plain claims, number k lays c on the entry, every other lays 0
  **`Added8.weight_one`**   what a yes of the batching block opens (Added8,
                   Johnson/Desc/K8/Honest/Added8.lean) · the row begins at column 0 in the ledger in
                   front · OffAt tl t r (no tie, no read: Johnson/Desc/K8/Honest/WeightAt.lean) · k
                   < fr.length + 4 · OneOn ⊢ the value of the weight = θ ^ k * c
  `PlaneOff fr k8 bk tl e x`   no plain claim but number fr.length + 1 + e bears on column x of
                   virtual row e of the bits' array
  `plane_claim`   which claim that number is: the library's `four8` at 1 + e (`take_four`,
                   Johnson/Desc/First/Batch/Law/K8Four.lean)
  **`Added8.weight_plane0`**, **`_plane1`**, **`_plane2`**   x < tl.bzColumns ⊢ the value of the
                   weight on column x of row 0 | 1 | 2 = θ ^ (fr.length + 1 | 2 | 3) * the run's
                   factor * the run's weight at x
Limits. IMPLICATIONS: `Added8`, `OffAt` at the bits' array and `PlaneOff` ARE PAID BY NOBODY HERE;
at row 0, besides, that the form of the lookup's last sumcheck names no entry of the bits' array. By
values alone: nothing on words, nothing on the test.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.Added8
import Johnson.Desc.K8.Honest.PlanesLiveOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- Of the plain claims, number k lays c on the entry; every other lays 0. -/
def OneOn (fr k8 bk : List Claim) (t r i k : Nat) (c : Cb.Gl.E) : Prop :=
  (∀ (j : Nat) (cl : Claim), (fr ++ k8.take 4)[j]? = some cl →
      coefOn cl t r i = if j = k then c else 0) ∧
    ∀ (j : Nat) (cl : Claim), bk[j]? = some cl → coefOn cl t r i = 0

section
variable {tl tl' : HTailF2} {funs : Array HFun} {Y G F₁ F₂ : Fork} {fr k8 bk : List Claim}
  {n₀ : Nat}

/-- **The weight on an entry on which one plain claim bears, and no tie and no read.** -/
theorem Added8.weight_one (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) (t r i k : Nat)
    (c : Cb.Gl.E) (h0 : ((Y.trees.getD t {}).rows.getD r {}).L0 = 0) (hO : OffAt tl t r)
    (hk : k < fr.length + 4) (h1 : OneOn fr k8 bk t r i k c) :
    Reading.gl.val ((weightsOf G t r).getD i zeroE) = Reading.gl.val Y.theta ^ k * c := by
  obtain ⟨-, -, -, -, -, hk8, -⟩ := k8_cut A.eq
  have hw := plain_weight (fun j => if j = k then c else 0) tl tl' funs Y G F₁ F₂ fr k8 bk n₀
    t r i fr.length bk.length (K9L.addList_older _ Y G A.add) A.zero A.n0 A.sz A.eq A.th A.pl
    A.frame rfl rfl (fun j cl hj => ⟨A.plainA j cl hj, h1.1 j cl hj⟩)
    (fun j cl hj => ⟨A.plainB j cl hj, by
      rw [h1.2 j cl hj]
      exact (if_neg (by omega)).symm⟩) hO
  have h0G : ((G.trees.getD t {}).rows.getD r {}).L0 = 0 := by
    rw [L0_of_shape, shape_of_frame _ _ A.core.2.2.1, ← L0_of_shape]
    exact h0
  rw [← total_oneAt Reading.gl G t r i h0G, hw]
  unfold plainTerms
  rw [termsSum_append, termsSum_fromOn, termsSum_fromOn,
    runSum_pick _ (fr.length + 4) k hk (fun d _ hd => by rw [if_neg hd, mul_zero]),
    K9L.runSum_congr _ (fun _ => (0 : Cb.Gl.E)) _ _ (fun j hj _ => by
      rw [if_neg (by omega), mul_zero]), runSum_zero, add_zero, if_pos rfl]

/-- No plain claim but number fr.length + 1 + e bears on column x of row e of the bits' array. -/
def PlaneOff (fr k8 bk : List Claim) (tl : HTailF2) (e x : Nat) : Prop :=
  (∀ (j : Nat) (cl : Claim), (fr ++ k8.take 4)[j]? = some cl → j ≠ fr.length + 1 + e →
      coefOn cl tl.ix.BZ e x = 0) ∧
    ∀ (j : Nat) (cl : Claim), bk[j]? = some cl → coefOn cl tl.ix.BZ e x = 0

/-- Which claim that number is. -/
theorem plane_claim (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) {g : Forest.Heard}
    (hg : tl.heard = some g) (e : Nat) :
    (fr ++ k8.take 4)[fr.length + 1 + e]? = (K9L.four8 tl g)[1 + e]? := by
  obtain ⟨g', -, hg', h4, -⟩ := K9L.take_four A.eq
  obtain rfl : g' = g := Option.some.inj (hg'.symm.trans hg)
  rw [h4, List.getElem?_append_right (by omega)]
  congr 1
  omega

/-- From "no other" and the claim's own coefficient to `OneOn`. -/
theorem oneOn_plane (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) {g : Forest.Heard}
    (hg : tl.heard = some g) (e x : Nat) (cl₀ : Claim) (hc : (K9L.four8 tl g)[1 + e]? = some cl₀)
    (hP : PlaneOff fr k8 bk tl e x) :
    OneOn fr k8 bk tl.ix.BZ e x (fr.length + 1 + e) (coefOn cl₀ tl.ix.BZ e x) := by
  refine ⟨fun j cl hj => ?_, hP.2⟩
  by_cases ej : j = fr.length + 1 + e
  · rw [if_pos ej]
    rw [ej, plane_claim A hg e, hc] at hj
    rw [Option.some.inj hj]
  · rw [if_neg ej]
    exact hP.1 j cl hj ej

/-- **Row 0.** -/
theorem Added8.weight_plane0 (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) {g : Forest.Heard}
    (hg : tl.heard = some g) (x : Nat) (hx : x < tl.bzColumns)
    (h0 : ((Y.trees.getD tl.ix.BZ {}).rows.getD 0 {}).L0 = 0) (hO : OffAt tl tl.ix.BZ 0)
    (hfree : ∀ y ∈ (g.leaves.rowForm oneE {}).ents.toList, y.tree ≠ tl.ix.BZ)
    (hP : PlaneOff fr k8 bk tl 0 x) :
    Reading.gl.val ((weightsOf G tl.ix.BZ 0).getD x zeroE) =
      Reading.gl.val Y.theta ^ (fr.length + 1 + 0) *
        (Reading.gl.val (mulE g.leaves.eps g.leavesA) * Reading.gl.val
          ((eqTab (g.zb0.extract 5 (5 + tl.f9.kT + tl.f9.cK))).getD x zeroE)) := by
  have hc := coef_one_run
    { form := g.leaves.rowForm oneE {},
      runs := #[Fo.bzRun tl 0 (mulE g.leaves.eps g.leavesA)
        (eqTab (g.zb0.extract 5 (5 + tl.f9.kT + tl.f9.cK)))] }
    (Fo.bzRun tl 0 (mulE g.leaves.eps g.leavesA)
      (eqTab (g.zb0.extract 5 (5 + tl.f9.kT + tl.f9.cK)))) tl.ix.BZ 0 x rfl rfl rfl rfl rfl hx
    (fun y hy h => hfree y hy h.1)
  rw [A.weight_one tl.ix.BZ 0 x _ _ h0 hO (by omega)
    (oneOn_plane A hg 0 x _ (four8_one tl g) hP), coefOn_eq, hc]
  rfl

/-- **Row 1.** -/
theorem Added8.weight_plane1 (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) {g : Forest.Heard}
    (hg : tl.heard = some g) (x : Nat) (hx : x < tl.bzColumns)
    (h0 : ((Y.trees.getD tl.ix.BZ {}).rows.getD 1 {}).L0 = 0) (hO : OffAt tl tl.ix.BZ 1)
    (hP : PlaneOff fr k8 bk tl 1 x) :
    Reading.gl.val ((weightsOf G tl.ix.BZ 1).getD x zeroE) =
      Reading.gl.val Y.theta ^ (fr.length + 1 + 1) *
        (Reading.gl.val (subE zeroE oneE) * Reading.gl.val
          ((eqTab (g.zb1.extract 5 (5 + tl.f9.kT + tl.f9.cK))).getD x zeroE)) := by
  have hc := coef_one_run
    { form := Aff.slot g.sBit,
      runs := #[Fo.bzRun tl 1 (subE zeroE oneE)
        (eqTab (g.zb1.extract 5 (5 + tl.f9.kT + tl.f9.cK)))] }
    (Fo.bzRun tl 1 (subE zeroE oneE)
      (eqTab (g.zb1.extract 5 (5 + tl.f9.kT + tl.f9.cK)))) tl.ix.BZ 1 x rfl rfl rfl rfl rfl hx
    (fun y hy _ => by simp [Aff.slot] at hy)
  rw [A.weight_one tl.ix.BZ 1 x _ _ h0 hO (by omega)
    (oneOn_plane A hg 1 x _ (four8_two tl g) hP), coefOn_eq, hc]
  rfl

/-- **Row 2.** -/
theorem Added8.weight_plane2 (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) {g : Forest.Heard}
    (hg : tl.heard = some g) (x : Nat) (hx : x < tl.bzColumns)
    (h0 : ((Y.trees.getD tl.ix.BZ {}).rows.getD 2 {}).L0 = 0) (hO : OffAt tl tl.ix.BZ 2)
    (hP : PlaneOff fr k8 bk tl 2 x) :
    Reading.gl.val ((weightsOf G tl.ix.BZ 2).getD x zeroE) =
      Reading.gl.val Y.theta ^ (fr.length + 1 + 2) *
        (Reading.gl.val oneE * Reading.gl.val ((Fo.pinW tl).getD x zeroE)) := by
  have hc := coef_one_run
    { form := Aff.ofConst (subE zeroE (ofNat (2 ^ tl.f9.v - tl.f9.padding))),
      runs := #[Fo.bzRun tl 2 oneE (Fo.pinW tl)] }
    (Fo.bzRun tl 2 oneE (Fo.pinW tl)) tl.ix.BZ 2 x rfl rfl rfl rfl rfl hx
    (fun y hy _ => by simp [Aff.ofConst] at hy)
  rw [A.weight_one tl.ix.BZ 2 x _ _ h0 hO (by omega)
    (oneOn_plane A hg 2 x _ (four8_three tl g) hP), coefOn_eq, hc]
  rfl

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.weight_one
#print axioms VerifiableInference.Desc.First.K8.Honest.plane_claim
#print axioms VerifiableInference.Desc.First.K8.Honest.oneOn_plane
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.weight_plane0
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.weight_plane1
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.weight_plane2
