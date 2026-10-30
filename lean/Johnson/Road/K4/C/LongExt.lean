-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/LongExt.lean: CONDITIONAL.

Not shown here. That the verifier's placed panels meet `PanelsFit`
(Johnson/Road/K4/C/LongPlaces.lean): a hypothesis on public numbers here; shown in
Johnson/Road/K4/C/PanelsFitOf.lean at the panels that the honest side's maker returns; there too it
is shown that every such panel's pass is 0 or 1, which is a hypothesis here. That there are as many
pairs of sides as panels, and lam challenges: hypotheses on sizes. In the verifier's letters
besides: the verifier's own test on a panel's place (eqIndexOK), at each panel. Nothing on what a
panel's sides hold, and no form of the verifier's. Nothing here is evaluated at an example. No
property is claimed.

THE LONG VECTORS' EXTENSION AND THEIR INNER PRODUCT ARE SUMS OVER THE PANELS. The batched sumcheck
of the sub-protocol K4 sums SA[n] SB[n] over the 2 ^ lam places of two long vectors, which are made
of panels (longTabs, Johnson/Desc/K4/Honest/Stack.lean). Here, read in the field: the multilinear
extension of a long vector at a point is the sum over the panels of (the equality weight of the
panel's stretch) times the sum over its rows and columns of (the row's weight)(the column's
weight)(the side's entry); and the sum of the products of the two vectors' entries is the sum over
the panels, rows and columns of the products of the two sides' entries. THE ORDER: rs holds the
challenges by bit (rs[t] for bit t), as the verifier keeps them; the cube's point is that array
reversed.

  eqR_point      the weight over all bits is the kernel at the reversed array.
  eqR_place      the weight of a panel's place is the product of three.
  zipped, sum_long   the panels with their sides; a sum over the places of both vectors together.
  long_ext_fst, long_ext_snd   **the extension of a long vector**, in the library's weights.
  long_under_fst, long_under_snd   **the same in the verifier's letters.**
  panelDot, long_total   **the sum of the products.**
  sum_two_passes, long_total_pass   the same, split by the pass.
-/
import Johnson.Road.K4.C.LongPlaces
import Johnson.Road.K4.C.StackEnds
import Johnson.Road.FormsKeysEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (SBlk)
open OnBytes.Desc.First.K4.Honest (Tab fillAt longTabs StackData)

/-- The weight over all lam bits is the library's kernel at the challenges in the rounds' order. -/
theorem eqR_point (rs : Array E) {lam : ℕ} (hr : rs.size = lam) (n : ℕ) :
    Blocks.eqN lam 0 (pt Reading.gl rs.reverse) n = eqR Reading.gl rs 0 lam n := by
  have e := eqN_rev Reading.gl rs (lo := 0) (hi := lam) (Nat.le_of_eq hr.symm) n
  rw [Nat.sub_zero] at e
  rw [← e]
  have e2 : rs.extract 0 lam = rs := by
    rw [← hr]
    exact Array.extract_size
  rw [e2]

/-- **The weight of a panel's place**: of the stretch, of the row, of the column. -/
theorem eqR_place {lam : ℕ} {b : SBlk} (h : PanelFit lam b) (hw : b.w ≤ lam) (rs : Array E)
    {i yv : ℕ} (hi : i < b.ni) (hy : yv < b.ny) :
    eqR Reading.gl rs 0 lam (panelPlace b i yv) =
      eqR Reading.gl rs b.w lam (b.off / 2 ^ b.w) *
        (eqR Reading.gl rs b.wy b.w i * eqR Reading.gl rs 0 b.wy yv) := by
  have h1 : yv < 2 ^ (b.wy - 0) := Nat.lt_of_lt_of_le hy h.ny_le
  have h2 : i < 2 ^ (b.w - b.wy) := Nat.lt_of_lt_of_le hi h.ni_le
  have e : 2 ^ b.w = 2 ^ (b.w - b.wy) * 2 ^ b.wy := by
    rw [← Nat.pow_add, Nat.sub_add_cancel h.wy_le]
  have h3 : i * 2 ^ (b.wy - 0) + yv < 2 ^ (b.w - 0) := by
    rw [Nat.sub_zero, Nat.sub_zero] at *
    have h4 : (i + 1) * 2 ^ b.wy ≤ 2 ^ b.w := by
      rw [e]
      exact Nat.mul_le_mul_right _ h2
    rw [Nat.succ_mul] at h4
    omega
  have ep : panelPlace b i yv = b.off / 2 ^ b.w * 2 ^ (b.w - 0) + (i * 2 ^ (b.wy - 0) + yv) := by
    unfold panelPlace
    rw [Nat.sub_zero, Nat.sub_zero, Nat.div_mul_cancel h.dvd, Nat.add_assoc]
  rw [ep, eqR_split Reading.gl rs (Nat.zero_le _) hw _ h3,
    eqR_split Reading.gl rs (Nat.zero_le _) h.wy_le _ h1]

/-! ## The long vectors in longTabs' own letters -/

/-- A list's sum, split by a number that is 0 or 1 at each member. -/
theorem sum_two_passes {α : Type} : ∀ (l : List (SBlk × α)) (f : SBlk × α → Cb.Gl.E),
    (∀ x ∈ l, x.1.claim = 0 ∨ x.1.claim = 1) →
    (l.map f).sum = ((l.filter fun x => x.1.claim == 0).map f).sum +
      ((l.filter fun x => x.1.claim == 1).map f).sum
  | [], _, _ => by simp
  | x :: l, f, h => by
    have ih := sum_two_passes l f fun y hy => h y (List.mem_cons_of_mem _ hy)
    rcases h x List.mem_cons_self with e | e
    · rw [List.filter_cons_of_pos (by rw [e]; rfl), List.filter_cons_of_neg (by rw [e]; decide),
        List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih, add_assoc]
    · rw [List.filter_cons_of_neg (by rw [e]; decide), List.filter_cons_of_pos (by rw [e]; rfl),
        List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih]
      ring

/-- The panels, each with its two sides. -/
def zipped (bl : Array SBlk) (sides : Array (Array E × Array E)) :
    List (SBlk × Array E × Array E) := bl.toList.zip sides.toList

theorem zipped_panels {bl : Array SBlk} {sides : Array (Array E × Array E)}
    (hs : sides.size = bl.size) : (zipped bl sides).map (·.1) = bl.toList :=
  List.map_fst_zip (by rw [Array.length_toList, Array.length_toList, hs])

section
variable {lam : ℕ} {bl : Array SBlk} {sides : Array (Array E × Array E)}
  (hP : PanelsFit lam bl.toList) (hs : sides.size = bl.size)
include hP hs

/-- **A sum over the places of the two long vectors together.** -/
theorem sum_long {M : Type} [AddCommMonoid M] (G : ℕ → E → E → M)
    (hG : ∀ n, G n zeroE zeroE = 0) :
    ∑ n ∈ range (2 ^ lam), G n ((longTabs lam bl sides).1.getD n zeroE)
        ((longTabs lam bl sides).2.getD n zeroE) =
      ((zipped bl sides).map fun x => ∑ i ∈ range x.1.ni, ∑ yv ∈ range x.1.ny,
        G (panelPlace x.1 i yv) (x.2.1.getD (i * x.1.ny + yv) zeroE)
          (x.2.2.getD (i * x.1.ny + yv) zeroE)).sum := by
  rw [longTabs_fst, longTabs_snd]
  exact sum_lay2 (zipped bl sides) (by rw [zipped_panels hs]; exact hP) G hG

/-- A panel of the zipped list fits. -/
theorem zipped_fit {x : SBlk × Array E × Array E} (hx : x ∈ zipped bl sides) :
    PanelFit lam x.1 :=
  hP.each x.1 (zipped_panels hs ▸ List.mem_map_of_mem hx)

/-- One panel's term, with the place's weight cut in three. -/
theorem term_split (rs : Array E) {x : SBlk × Array E × Array E} (hx : x ∈ zipped bl sides)
    (f : ℕ → Cb.Gl.E) :
    ∑ i ∈ range x.1.ni, ∑ yv ∈ range x.1.ny,
        eqR Reading.gl rs 0 lam (panelPlace x.1 i yv) * f (i * x.1.ny + yv) =
      eqR Reading.gl rs x.1.w lam (x.1.off / 2 ^ x.1.w) *
        ∑ i ∈ range x.1.ni, eqR Reading.gl rs x.1.wy x.1.w i *
          ∑ yv ∈ range x.1.ny, eqR Reading.gl rs 0 x.1.wy yv * f (i * x.1.ny + yv) := by
  have hf := zipped_fit hP hs hx
  rw [Finset.mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine sum_congr rfl fun yv hy => ?_
  rw [eqR_place hf hf.w_le rs (mem_range.1 hi) (mem_range.1 hy)]
  ring

/-- **THE EXTENSION OF THE FIRST LONG VECTOR IS THE SUM OVER THE PANELS**, in the library's weights.
rs: the challenges by bit. -/
theorem long_ext_fst (rs : Array E) (hr : rs.size = lam) :
    Blocks.ext lam (fun n => Reading.gl.val ((longTabs lam bl sides).1.getD n zeroE))
        (pt Reading.gl rs.reverse) =
      ((zipped bl sides).map fun x => eqR Reading.gl rs x.1.w lam (x.1.off / 2 ^ x.1.w) *
        ∑ i ∈ range x.1.ni, eqR Reading.gl rs x.1.wy x.1.w i *
          ∑ yv ∈ range x.1.ny, eqR Reading.gl rs 0 x.1.wy yv *
            Reading.gl.val (x.2.1.getD (i * x.1.ny + yv) zeroE)).sum := by
  unfold Blocks.ext
  simp only [eqR_point rs hr]
  rw [sum_long hP hs (fun n a _ => eqR Reading.gl rs 0 lam n * Reading.gl.val a) fun n => by
    beta_reduce
    rw [Reading.gl.zero, mul_zero]]
  exact congrArg List.sum (List.map_congr_left fun x hx =>
    term_split hP hs rs hx fun j => Reading.gl.val (x.2.1.getD j zeroE))

/-- The same for the second long vector. -/
theorem long_ext_snd (rs : Array E) (hr : rs.size = lam) :
    Blocks.ext lam (fun n => Reading.gl.val ((longTabs lam bl sides).2.getD n zeroE))
        (pt Reading.gl rs.reverse) =
      ((zipped bl sides).map fun x => eqR Reading.gl rs x.1.w lam (x.1.off / 2 ^ x.1.w) *
        ∑ i ∈ range x.1.ni, eqR Reading.gl rs x.1.wy x.1.w i *
          ∑ yv ∈ range x.1.ny, eqR Reading.gl rs 0 x.1.wy yv *
            Reading.gl.val (x.2.2.getD (i * x.1.ny + yv) zeroE)).sum := by
  unfold Blocks.ext
  simp only [eqR_point rs hr]
  rw [sum_long hP hs (fun n _ a => eqR Reading.gl rs 0 lam n * Reading.gl.val a) fun n => by
    beta_reduce
    rw [Reading.gl.zero, mul_zero]]
  exact congrArg List.sum (List.map_congr_left fun x hx =>
    term_split hP hs rs hx fun j => Reading.gl.val (x.2.2.getD j zeroE))

/-- One panel's term in the verifier's letters: the weight of the stretch as the verifier computes
it, times the double loop under the verifier's two tables of weights. -/
theorem term_under (rs : Array E) (hr : rs.size = lam) {x : SBlk × Array E × Array E}
    (hx : x ∈ zipped bl sides)
    (hok : eqIndexOK (rs.extract x.1.w lam) (x.1.off / 2 ^ x.1.w) = true) (s : Array E) :
    eqR Reading.gl rs x.1.w lam (x.1.off / 2 ^ x.1.w) *
        ∑ i ∈ range x.1.ni, eqR Reading.gl rs x.1.wy x.1.w i *
          ∑ yv ∈ range x.1.ny, eqR Reading.gl rs 0 x.1.wy yv *
            Reading.gl.val (s.getD (i * x.1.ny + yv) zeroE) =
      Reading.gl.val (eqLowAt rs x.1.w lam (x.1.off / 2 ^ x.1.w)) *
        Reading.gl.val (StackData.under (eqLow rs x.1.wy x.1.w) (eqLow rs 0 x.1.wy) x.1.ni x.1.ny
          fun i yv => s.getD (i * x.1.ny + yv) zeroE) := by
  have hf := zipped_fit hP hs hx
  have hw : x.1.w ≤ rs.size := by
    rw [hr]
    exact hf.w_le
  have hA : Reading.gl.val (eqLowAt rs x.1.w lam (x.1.off / 2 ^ x.1.w)) =
      eqR Reading.gl rs x.1.w lam (x.1.off / 2 ^ x.1.w) :=
    eqLowAt_value Reading.gl rs (Nat.le_of_eq hr.symm) hok
  have hI : ∀ i < x.1.ni, Reading.gl.val ((eqLow rs x.1.wy x.1.w).getD i zeroE) =
      eqR Reading.gl rs x.1.wy x.1.w i := fun i hi =>
    eqLow_value Reading.gl rs hw (Nat.lt_of_lt_of_le hi hf.ni_le)
  have hY : ∀ yv < x.1.ny, Reading.gl.val ((eqLow rs 0 x.1.wy).getD yv zeroE) =
      eqR Reading.gl rs 0 x.1.wy yv := fun yv hy =>
    eqLow_value Reading.gl rs (Nat.le_trans hf.wy_le hw)
      (show yv < 2 ^ (x.1.wy - 0) by
        rw [Nat.sub_zero]
        exact Nat.lt_of_lt_of_le hy hf.ny_le)
  have e1 : ∑ i ∈ range x.1.ni, Reading.gl.val ((eqLow rs x.1.wy x.1.w).getD i zeroE) *
        ∑ yv ∈ range x.1.ny, Reading.gl.val ((eqLow rs 0 x.1.wy).getD yv zeroE) *
          Reading.gl.val (s.getD (i * x.1.ny + yv) zeroE) =
      ∑ i ∈ range x.1.ni, eqR Reading.gl rs x.1.wy x.1.w i *
        ∑ yv ∈ range x.1.ny, eqR Reading.gl rs 0 x.1.wy yv *
          Reading.gl.val (s.getD (i * x.1.ny + yv) zeroE) := by
    refine sum_congr rfl fun i hi => ?_
    rw [hI i (mem_range.1 hi)]
    exact congrArg (fun t => eqR Reading.gl rs x.1.wy x.1.w i * t)
      (sum_congr rfl fun yv hy => by rw [hY yv (mem_range.1 hy)])
  rw [hA, under_read]
  exact congrArg (fun t => eqR Reading.gl rs x.1.w lam (x.1.off / 2 ^ x.1.w) * t) e1.symm

/-- **THE SAME IN THE VERIFIER's LETTERS**, under the verifier's own test on each panel's place. -/
theorem long_under_fst (rs : Array E) (hr : rs.size = lam)
    (hok : ∀ b ∈ bl.toList, eqIndexOK (rs.extract b.w lam) (b.off / 2 ^ b.w) = true) :
    Blocks.ext lam (fun n => Reading.gl.val ((longTabs lam bl sides).1.getD n zeroE))
        (pt Reading.gl rs.reverse) =
      ((zipped bl sides).map fun x =>
        Reading.gl.val (eqLowAt rs x.1.w lam (x.1.off / 2 ^ x.1.w)) *
          Reading.gl.val (StackData.under (eqLow rs x.1.wy x.1.w) (eqLow rs 0 x.1.wy) x.1.ni
            x.1.ny fun i yv => x.2.1.getD (i * x.1.ny + yv) zeroE)).sum := by
  rw [long_ext_fst hP hs rs hr]
  exact congrArg List.sum (List.map_congr_left fun x hx => term_under hP hs rs hr hx
    (hok x.1 (zipped_panels hs ▸ List.mem_map_of_mem hx)) x.2.1)

theorem long_under_snd (rs : Array E) (hr : rs.size = lam)
    (hok : ∀ b ∈ bl.toList, eqIndexOK (rs.extract b.w lam) (b.off / 2 ^ b.w) = true) :
    Blocks.ext lam (fun n => Reading.gl.val ((longTabs lam bl sides).2.getD n zeroE))
        (pt Reading.gl rs.reverse) =
      ((zipped bl sides).map fun x =>
        Reading.gl.val (eqLowAt rs x.1.w lam (x.1.off / 2 ^ x.1.w)) *
          Reading.gl.val (StackData.under (eqLow rs x.1.wy x.1.w) (eqLow rs 0 x.1.wy) x.1.ni
            x.1.ny fun i yv => x.2.2.getD (i * x.1.ny + yv) zeroE)).sum := by
  rw [long_ext_snd hP hs rs hr]
  exact congrArg List.sum (List.map_congr_left fun x hx => term_under hP hs rs hr hx
    (hok x.1 (zipped_panels hs ▸ List.mem_map_of_mem hx)) x.2.2)

/-- One panel's inner product: one index over rows times columns. -/
def panelDot (x : SBlk × Array E × Array E) : Cb.Gl.E :=
  ∑ j ∈ range (x.1.ni * x.1.ny),
    Reading.gl.val (x.2.1.getD j zeroE) * Reading.gl.val (x.2.2.getD j zeroE)

/-- **THE SUM OF THE PRODUCTS OF THE TWO LONG VECTORS' ENTRIES IS THE SUM OVER THE PANELS.** -/
theorem long_total :
    ∑ n ∈ range (2 ^ lam), Reading.gl.val ((longTabs lam bl sides).1.getD n zeroE) *
        Reading.gl.val ((longTabs lam bl sides).2.getD n zeroE) =
      ((zipped bl sides).map panelDot).sum := by
  rw [sum_long hP hs (fun _ a c => Reading.gl.val a * Reading.gl.val c) fun _ => by
    beta_reduce
    rw [Reading.gl.zero, mul_zero]]
  refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
  unfold panelDot
  rw [sum_grid]

/-- **The same, split by the pass**, where every panel's pass is 0 or 1. -/
theorem long_total_pass (hc : ∀ b ∈ bl.toList, b.claim = 0 ∨ b.claim = 1) :
    ∑ n ∈ range (2 ^ lam), Reading.gl.val ((longTabs lam bl sides).1.getD n zeroE) *
        Reading.gl.val ((longTabs lam bl sides).2.getD n zeroE) =
      (((zipped bl sides).filter fun x => x.1.claim == 0).map panelDot).sum +
        (((zipped bl sides).filter fun x => x.1.claim == 1).map panelDot).sum := by
  rw [long_total hP hs]
  exact sum_two_passes (zipped bl sides) panelDot fun x hx =>
    hc x.1 (zipped_panels hs ▸ List.mem_map_of_mem hx)

end

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.eqR_point
#print axioms OnBytes.Road.K4.C.eqR_place
#print axioms OnBytes.Road.K4.C.sum_two_passes
#print axioms OnBytes.Road.K4.C.zipped_panels
#print axioms OnBytes.Road.K4.C.sum_long
#print axioms OnBytes.Road.K4.C.zipped_fit
#print axioms OnBytes.Road.K4.C.term_split
#print axioms OnBytes.Road.K4.C.long_ext_fst
#print axioms OnBytes.Road.K4.C.long_ext_snd
#print axioms OnBytes.Road.K4.C.term_under
#print axioms OnBytes.Road.K4.C.long_under_fst
#print axioms OnBytes.Road.K4.C.long_under_snd
#print axioms OnBytes.Road.K4.C.long_total
#print axioms OnBytes.Road.K4.C.long_total_pass
