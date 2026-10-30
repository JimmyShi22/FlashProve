-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoR5Ends.lean.
The layer of the table's leaves and the test on bits: from a run of the byte-level routine to the
flat function's trace and end values.

The flat function makes its trace stage by stage; its last two stages are two calls of `TwV.takeSc`.
This file gives these two calls, in the very form in which the trace is put together, at the rounds
that a run of the byte-level routine's lines made (`R5D.evs`,
OnBytes/Tie/Pv/Lookup/Forest/FoR5Run.lean), and then the end values
that are read off them.

The orders. In the byte-level routine round j of the leaves' sumcheck reads place j of the array
that holds the table's point, and round j of the bits' sumcheck reads place j of the fresh point
reversed. An array holds a point with the top coordinate first. So both sumchecks bind the
coordinates from the last to the first: the list of `FoNums.placeOf`.

 * `inRounds_place`: at that order, a point by coordinate is read in the order of the rounds by
   reversing it.
 * `R5D.cls`, `R5D.bitsSc`: what the two sumchecks leave, read.
 * `r5_h4`, `r5_h5`: the two calls of `takeSc`. Premises: the run's facts (`FitsA`, the sizes), that
   the array of the table's point is the point by coordinate reversed, and that the fresh point has
   m coordinates (a run on a view gives that); and that the order of the record N of numbers (oE,
   oB) is the list of `FoNums.placeOf`.
 * `r5_zb0`, `r5_zb1`: the two arrays of challenges that the routine returns are the two points by
   coordinate, reversed.
 * `leaves_eps`, `leaves_r`, `leaves_first`, `leaves_target`, `leaves_start`, `leaves_vars`,
   `leaves_flags`: the fields of the state of the leaves' sumcheck that the routine returns.
 * `slotsOf_zdL`, `slotsOf_zdB`, `sBit_eq`, `firstB_eq`: the slots in closed form: the leaves take 1
   + (m + d), the bits 1 + 2 m + 2 + 1; the shown value's slot is the last. Premises: d ≤ m; for
   `sBit_eq` also that the fresh point has m coordinates.
No statement here has a run as its premise: D is any record of the type R5D. That a run of the eight
lines gives a record with these facts is leavesBits_ok
(OnBytes/Tie/Pv/Lookup/Forest/FoR5Run.lean).

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoR5Flat
import OnBytes.Tie.Pv.Lookup.Forest.FoPts

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie

section
variable {K : Type} [CommRing K] (ρ : Reading K)

theorem inRounds_place (m : ℕ) (pt : List K) (h : pt.length = m) :
    inRounds ((List.range m).map (FoNums.placeOf m)) pt = pt.reverse := by
  unfold inRounds FoNums.placeOf
  refine List.ext_getElem (by simp [h]) fun i h1 h2 => ?_
  have hi : i < m := by simpa using h1
  simp only [List.getElem_map, List.getElem_range, List.getElem_reverse]
  rw [List.getD_eq_getElem _ _ (by omega)]
  congr 1
  omega

private theorem range_getD (xs : List K) (m : ℕ) (h : xs.length = m) :
    ((List.range m).map fun i => xs.getD i 0) = xs := by
  refine List.ext_getElem (by simp [h]) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range]
  exact List.getD_eq_getElem _ _ h2

private theorem range_getD_take (xs : List K) (y : K) (m : ℕ) (h : xs.length = m) :
    ((List.range m).map fun i => (xs ++ [y]).getD i 0) = xs := by
  refine List.ext_getElem (by simp [h]) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left h2]

theorem zdL_map (m d : ℕ) (rho : Array E) (h : rho.size = m) :
    ((zdL m d rho).map fun p => ρ.val p.1) = rdA ρ rho := by
  unfold zdL zdOf rdA
  refine List.ext_getElem (by simp [h]) fun i h1 h2 => ?_
  have hi : i < rho.size := by simpa using h2
  simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]

theorem zdB_map (ptZ : Array E) : ((zdB ptZ).map fun p => ρ.val p.1) = (rdA ρ ptZ).reverse := by
  simp [zdB, zdOf, rdA, List.map_reverse, Function.comp_def]

theorem fitsA_length : ∀ {zd : List (E × ℕ)} {rs : List (Array E × E)}, FitsA zd rs →
    rs.length = zd.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => congrArg (· + 1) (fitsA_length h.2)
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem zdL_length (m d : ℕ) (rho : Array E) : (zdL m d rho).length = m := by simp [zdL, zdOf]
theorem zdB_length (ptZ : Array E) : (zdB ptZ).length = ptZ.size := by simp [zdB, zdOf]

variable (D : R5D) (m d : ℕ) (rho : Array E)

/-- What the leaves' sumcheck leaves, read. -/
def R5D.cls (C : Aff) (first : ℕ) : Sc K :=
  ⟨ρ.val D.epsL, D.rsL.map fun r => ρ.val r.2, ρ.val (D.leaves m d rho C first).claim, []⟩

/-- What the bits' sumcheck leaves, read. -/
def R5D.bitsSc (first : ℕ) : Sc K :=
  ⟨ρ.val D.epsB, (D.rsB.map fun r => ρ.val r.2) ++ [ρ.val D.beta],
    ρ.val (D.bits2 m d rho first).claim, rdA ρ D.v⟩

/-- The trace's stage of the leaves. -/
theorem r5_h4 {P : Type} (N : Nums P K) (hE : N.oE = (List.range m).map (FoNums.placeOf m))
    (pt : List K) (hpt : rdA ρ rho = pt.reverse) (hs : rho.size = m)
    (hL : FitsA (zdL m d rho) D.rsL) (hB : FitsA (zdB D.ptZ) D.rsB) (C : Aff) (first : ℕ)
    (l : List Ev) :
    takeSc (flEv ρ (D.evs m d rho ++ l)) (ρ.val D.tgL) (inRounds N.oE pt) false =
      (D.cls ρ m d rho C first, ([], rdA ρ D.ptZ) ::
        (flH ρ D.muB D.epsB D.rsB' (some D.v.toList) ++ flEv ρ l)) := by
  have hl : pt.length = m := by
    have := congrArg List.length hpt
    simpa [rdA, hs] using this.symm
  rw [hE, inRounds_place m pt hl, ← hpt, ← zdL_map ρ m d rho hs, flEv_evs ρ D m d rho hL hB l]
  exact r5_leaves ρ D m d rho hL C first _

/-- The trace's stage of the bits. -/
theorem r5_h5 {P : Type} (N : Nums P K) (hO : N.oB = (List.range m).map (FoNums.placeOf m))
    (hZ : D.ptZ.size = m) (hB : FitsA (zdB D.ptZ) D.rsB) (hY : D.sentY.size = 2) (first : ℕ)
    (rest : Rounds K) :
    takeSc (flH ρ D.muB D.epsB D.rsB' (some D.v.toList) ++ rest) 0
        (inRounds N.oB (rdA ρ D.ptZ) ++ [0]) true = (D.bitsSc ρ m d rho first, rest) := by
  rw [hO, inRounds_place m _ (by simp [rdA, hZ]), ← zdB_map]
  exact r5_bits ρ D m d rho hB hY first rest

/-- The leaves' challenges, as the routine returns them: the point by coordinate, reversed. -/
theorem r5_zb0 (hL : FitsA (zdL m d rho) D.rsL) (C : Aff) (first : ℕ) :
    rdA ρ (D.rsL.map (·.2)).toArray =
      (byVar ((List.range m).map (FoNums.placeOf m)) (D.cls ρ m d rho C first).xs).reverse := by
  rw [back_place, range_getD _ m (by
    show (D.rsL.map fun r => ρ.val r.2).length = m
    rw [List.length_map, fitsA_length hL, zdL_length])]
  simp [rdA, R5D.cls]

/-- The bits' challenges, as the routine returns them. -/
theorem r5_zb1 (hZ : D.ptZ.size = m) (hB : FitsA (zdB D.ptZ) D.rsB) (first : ℕ) :
    rdA ρ (D.rsB.map (·.2)).toArray =
      (byVar ((List.range m).map (FoNums.placeOf m)) (D.bitsSc ρ m d rho first).xs).reverse := by
  rw [back_place]
  show _ = (List.range m).map fun i => ((D.rsB.map fun r => ρ.val r.2) ++ [ρ.val D.beta]).getD i 0
  rw [range_getD_take _ _ m (by rw [List.length_map, fitsA_length hB, zdB_length, hZ])]
  simp [rdA]

end

/-! ### the state of the leaves' sumcheck -/
section
variable (D : R5D) (m d : ℕ) (rho : Array E) (C : Aff) (first : ℕ)

theorem leaves_eps : (D.leaves m d rho C first).eps = D.epsL := rfl
theorem leaves_target : (D.leaves m d rho C first).target = D.tgL := rfl
theorem leaves_start : (D.leaves m d rho C first).start = C := rfl
theorem leaves_first : (D.leaves m d rho C first).first = first := rfl
theorem leaves_flags : (D.leaves m d rho C first).started = true ∧
    (D.leaves m d rho C first).ended = false ∧ (D.leaves m d rho C first).rowMade = false :=
  ⟨rfl, rfl, rfl⟩
theorem leaves_r : (D.leaves m d rho C first).r = (D.rsL.map (·.2)).toArray := by
  simp [R5D.leaves, after]
theorem leaves_vars : (D.leaves m d rho C first).vars.toList =
    (zdL m d rho).map fun p => OnBytes.Psc.Weight.equality p.1 p.2 := by
  simp [R5D.leaves, after, eqW]

/-! ### the slots -/

private theorem sum_ite (d : ℕ) : ∀ m, d ≤ m →
    ((List.range m).map fun j => if j < d then 2 else 1).sum = m + d
  | 0, h => by
    obtain rfl : d = 0 := by omega
    rfl
  | m + 1, h => by
    rw [List.range_succ, List.map_append, List.sum_append]
    by_cases hd : d ≤ m
    · rw [sum_ite d m hd]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [if_neg (by omega)]
      omega
    · obtain rfl : d = m + 1 := by omega
      have e : ((List.range m).map fun j => if j < m + 1 then 2 else 1) =
          (List.range m).map fun _ => 2 :=
        List.map_congr_left fun j hj => if_pos (by have := List.mem_range.1 hj; omega)
      rw [e]
      simp
      omega

theorem slotsOf_zdL (h : d ≤ m) : slotsOf (zdL m d rho) = m + d := by
  have e : ((zdL m d rho).map fun p => p.2 - 1) =
      (List.range m).map fun j => if j < d then 2 else 1 := by
    simp only [zdL, zdOf, List.map_map]
    refine List.map_congr_left fun j _ => ?_
    simp [roundValues]
  unfold slotsOf
  rw [e, sum_ite d m h]

theorem slotsOf_zdB (ptZ : Array E) : slotsOf (zdB ptZ) = 2 * ptZ.size := by
  have e : ((zdB ptZ).map fun p => p.2 - 1) = List.replicate ptZ.size 2 := by
    refine List.ext_getElem (by simp [zdB, zdOf]) fun i h1 h2 => ?_
    simp [zdB, zdOf, roundValues]
  unfold slotsOf
  rw [e]
  simp
  omega

theorem firstB_eq (h : d ≤ m) : firstB m d rho first = first + (1 + (m + d)) := by
  unfold firstB
  rw [slotsOf_zdL m d rho h]
  omega

theorem sBit_eq (h : d ≤ m) (hZ : D.ptZ.size = m) :
    D.sBit m d rho first = first + (1 + (m + d)) + (1 + (2 * m + 2)) := by
  unfold R5D.sBit
  rw [firstB_eq m d rho first h, slotsOf_zdB, hZ]
  omega

end
end Fo
