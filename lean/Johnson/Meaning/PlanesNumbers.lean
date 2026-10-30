-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/PlanesNumbers.lean: the two public premises of Johnson/Meaning/PlanesHost.lean, as
theorems.

`k4_host_planes` asks of the list of matrices: the planes' matrix has its rows in one block of
2^lmb, and at least the planes' columns. At the list that the layers' public record holds for the
group (tailsOf, OnBytes/Model/LayerPlan.lean) both hold.

Main theorems (namespace `Meaning.Planes`).
  `tails_b`: in the list of every group below NGr the matrix at the place (matIx y).iB has 2^lmb
      rows and y.kbm columns.
  `cols_le_kbm`: where the layers' three claims on the planes are there, the planes' columns are at
      most v.y.kbm: the layers' text gives a form for a column only below kbm, and it has given one
      for every column.
  `k4_numbers`: so both premises hold at (P.tails.getD g {}).mats, if P.tails = tailsOf P.y and
      g < P.y.NGr.
  `k4_host_planes_at`: `k4_host_planes` at that list, without the two premises.

Limits. P.tails = tailsOf P.y is a premise: Pub.of (LayerPlan.lean:79) and the public record's maker
(VerifyPublic.lean:172) lay it so, by reading. g < P.y.NGr too.
-/
import Johnson.Meaning.PlanesHost

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Planes
open Finset
open Cb Cb.Fo Cb.Fo.NumsEq TwV
open OnBytes OnBytes.Model Fo
open Cb.Fo.Pin
open OnBytes.Model.Layer (Env Lay Pub Own HPlan2 matIx tailsOf)
open OnBytes.K.Kc
open OnBytes.Road.Rows (planeCol)

/-- The planes' matrix in the list of a group's matrices. -/
theorem tails_b (y : Lay) (g : ℕ) (hg : g < y.NGr) :
    (((tailsOf y).getD g {}).mats.getD (matIx y).iB {}).m = 2 ^ y.h.lmb ∧
      (((tailsOf y).getD g {}).mats.getD (matIx y).iB {}).k = y.kbm := by
  unfold tailsOf
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, hg, if_true,
    Option.map_some, Option.getD_some, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_zipIdx]
  have e : (matIx y).iB = y.parts.getD 0 0 + y.parts.getD 1 0 + 1 := rfl
  rw [e]
  simp [List.getElem?_append, Array.getD_eq_getD_getElem?]
  generalize y.parts[0]?.getD 0 = a
  generalize y.parts[1]?.getD 0 = b
  have e1 : ¬ a + b + 1 < a := by omega
  have e2 : ¬ a + b + 1 - a < b := by omega
  have e3 : a + b + 1 - a - b = 1 := by omega
  rw [if_neg e1, if_neg e2, e3]
  constructor <;>
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some,
      Function.comp_apply, Option.getD_some]
    split <;> rfl

theorem cols_le_kbm {v : Env} {fo : Forest.Heard} {pp : Aff × List Aff}
    (hq : Desc.First.K4.planesParts v fo = some pp) :
    planeCols fo.shape v.y.h.lmb ≤ v.y.kbm := by
  obtain ⟨tB0, _, _, _, _, _, hc⟩ := forms_there hq
  by_contra hlt
  have hk : v.y.kbm < planeCols fo.shape v.y.h.lmb := Nat.lt_of_not_le hlt
  obtain ⟨⟨b, hb⟩, _, _⟩ := hc v.y.kbm hk
  unfold planeCol at hb
  rw [if_neg (Nat.lt_irrefl _)] at hb
  cases hb

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- **Both public premises, at the group's own list of matrices.** -/
theorem k4_numbers {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (hh : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t'))
    {pp : Aff × List Aff} (hq : Desc.First.K4.planesParts o.v o.H.fo = some pp)
    (hT : P.tails = tailsOf P.y) (hg : g < P.y.NGr) :
    ((P.tails.getD g {}).mats.getD (matIx o.v.y).iB {}).m / 2 ^ o.v.y.h.lmb = 1 ∧
      planeCols o.H.fo.shape o.v.y.h.lmb ≤
        ((P.tails.getD g {}).mats.getD (matIx o.v.y).iB {}).k := by
  obtain ⟨ey, _, _⟩ := hear_tables hh
  have hb := tails_b P.y g hg
  rw [← hT, ← ey] at hb
  refine ⟨?_, ?_⟩
  · rw [hb.1]
    exact Nat.div_self (Nat.two_pow_pos _)
  · rw [hb.2]
    exact cols_le_kbm hq

/-- `k4_host_planes` at the group's own list of matrices, without the two public premises. -/
theorem k4_host_planes_at {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (hh : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t'))
    {pp : Aff × List Aff} (hq : Desc.First.K4.planesParts o.v o.H.fo = some pp)
    (hT : P.tails = tailsOf P.y) (hg : g < P.y.NGr)
    (zb0 zb1 : List K) (hz0 : rdL ρ o.H.fo.zb0 = zb0) (hz1 : rdL ρ o.H.fo.zb1 = zb1)
    (cellM : ℕ → ℕ → ℕ → K) (ν : _root_.Fo.Pl → K)
    (h4 : ∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
      cellM (matIx o.v.y).iB r c = ν (.cell r c))
    (W : World K)
    (hA : ReadsAll ρ (P.tails.getD g {}).mats o.funs W.entry o.v.iU3 o.v.K3 cellM) :
    ∃ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
      o.v.tabAt "b-pin" = some tP ∧
      K3HostPlanes o.H.fo.shape o.v.y.h.lmb zb0 zb1 ν (fun f => f.value ρ W)
        (k4Bit o.v tB0 tB1) (k4Pin o.v tP) :=
  k4_host_planes ρ hh hq zb0 zb1 hz0 hz1 _ cellM ν (k4_numbers hh hq hT hg).1
    (k4_numbers hh hq hT hg).2 h4 W hA

end

#print axioms tails_b
#print axioms cols_le_kbm
#print axioms k4_numbers
#print axioms k4_host_planes_at

end Meaning.Planes
