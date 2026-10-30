-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/PlanesTie.lean: the three claims of a feed-forward segment's lookup that read the
planes of its counts: the list in the layers' own text is the library's list.

The layers' own text (OnBytes/Desc/First/K4/Claims.lean) makes these three claims in two pieces:
`planesParts v fo` gives what is kept in the own claim of the leaves' sumcheck, and the second and
third claim; OnBytes/Desc/First/K4/Plain.lean lays the own claim in front. The library has the three
as one list, `planesL v fo` (OnBytes/Tie/Pv/Led/LedWalkPlanes.lean), and shows there that the
routine `Layer.claimsPlanes` adds just that list (`walks_claimsPlanes`).

Main theorems (namespace `Meaning.Planes`).
  `planesParts_eq`: the three forms made from `planesParts` are `planesL` where the lookup's test on
      the planes' number of rows (`Forest.planeCols`) passes, and nothing where it fails.
  `planesParts_planesL`: where `planesParts` is there, so is `planesL`, the same three forms.
  `planesL_planesParts`: the converse, where the test passes.
  `front_planesL`: `front_library` (Johnson/Road/K4/FrontLaw.lean) with the planes' three forms as
      the library's list.
  `frontWith_planesL`: both runs that the layers' block may state (`formsFrontWith rows`) end in the
      library's three forms and, in the first group, the library's claim on the embedding.
  `planes_rowsIn`: so in such a run each of the three names entries of the one array of reads alone,
      if the start form of the leaves' sumcheck does, by the library's `rowsIn_planesL`.

Limits. Equations between lists of forms. Nothing on what a form is worth, on a draw, on soundness.
Nothing on who adds the list to the one equation. The routine `Layer.claimsPlanes` makes the test
inside its run and `planesL` does not hold it, so the two lists part where the test fails.
-/
import Johnson.Road.K4.FrontLaw
import OnBytes.Tie.Pv.Led.LedWalkPlanes
import OnBytes.Tie.Pv.Led.LedRowsPlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Planes
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env Lay Heard Pub Own)
open OnBytes.Road.Rows (planesL planesAtO countO planeFormsO planeCol)

/-- The planes' value at a point: the two texts give one form. -/
theorem planesAt_eq (g : Forest.Heard) (lm e : Nat) (bit : Nat → Nat → Option Aff) :
    Desc.First.K4.planesAt g lm e bit = planesAtO g lm e bit := by
  unfold Desc.First.K4.planesAt planesAtO
  dsimp only
  congr 1
  funext f col
  cases bit e col <;> rfl

/-- The sum of the counts: the two texts give one form. -/
theorem count_eq (g : Forest.Heard) (lm : Nat) (pin : Nat → Option Aff) :
    ((List.range (g.shape.NC * 2 ^ (g.shape.kT + 5 - lm))).foldlM
      (fun (f : Aff) c => (pin c).map fun x => f + x)
      (Aff.ofConst (negE (ofF (2 ^ g.shape.v - g.shape.padding).toUInt64)))) = countO g lm pin := by
  unfold countO
  congr 1
  funext f col
  cases pin col <;> rfl

/-- **The three forms of the layers' own text are the library's list**, where the lookup's test on
the planes' number of rows passes; where it fails the layers' own text gives nothing. -/
theorem planesParts_eq (v : Env) (fo : Forest.Heard) :
    ((Desc.First.K4.planesParts v fo).map fun pp => fo.leaves.rowForm oneE pp.1 :: pp.2) =
      if (Forest.planeCols fo.shape v.y.h.lmb).toBool then planesL v fo else none := by
  change ((v.tabAt "b-bits-0").bind fun tB0 => (v.tabAt "b-bits-1").bind fun tB1 =>
    (v.tabAt "b-pin").bind fun tP =>
    (Desc.First.K4.need (Forest.planeCols fo.shape v.y.h.lmb).toBool).bind fun _ =>
    (Desc.First.K4.planesAt fo v.y.h.lmb 0
      (fun e x => planeCol v (if e == 0 then tB0 else tB1) x)).bind fun at0 =>
    (Desc.First.K4.planesAt fo v.y.h.lmb 1
      (fun e x => planeCol v (if e == 0 then tB0 else tB1) x)).bind fun at1 =>
    ((List.range (fo.shape.NC * 2 ^ (fo.shape.kT + 5 - v.y.h.lmb))).foldlM
      (fun (f : Aff) c => (planeCol v tP c).map fun x => f + x)
      (Aff.ofConst (negE (ofF (2 ^ fo.shape.v - fo.shape.padding).toUInt64)))).bind fun count =>
    some (Aff.scale at0 fo.leavesA, [Aff.slot fo.sBit - at1, count])).map
      (fun pp => fo.leaves.rowForm oneE pp.1 :: pp.2) = _
  simp only [planesAt_eq, count_eq]
  unfold planesL planeFormsO
  cases v.tabAt "b-bits-0" with
  | none => simp
  | some tB0 =>
  cases v.tabAt "b-bits-1" with
  | none => simp
  | some tB1 =>
  cases v.tabAt "b-pin" with
  | none => simp
  | some tP =>
  cases (Forest.planeCols fo.shape v.y.h.lmb).toBool with
  | false => simp [Desc.First.K4.need]
  | true =>
  simp only [Desc.First.K4.need, if_true, Option.bind_some]
  cases planesAtO fo v.y.h.lmb 0 (fun e x => planeCol v (if e == 0 then tB0 else tB1) x) with
  | none => simp
  | some at0 =>
  cases planesAtO fo v.y.h.lmb 1 (fun e x => planeCol v (if e == 0 then tB0 else tB1) x) with
  | none => simp
  | some at1 =>
  cases countO fo v.y.h.lmb (planeCol v tP) with
  | none => simp
  | some count => simp

theorem planesParts_planesL {v : Env} {fo : Forest.Heard} {pp : Aff × List Aff}
    (h : Desc.First.K4.planesParts v fo = some pp) :
    planesL v fo = some (fo.leaves.rowForm oneE pp.1 :: pp.2) := by
  have e := planesParts_eq v fo
  rw [h] at e
  by_cases c : (Forest.planeCols fo.shape v.y.h.lmb).toBool = true
  · rw [if_pos c] at e
    exact e.symm
  · rw [if_neg c] at e
    cases e

theorem planesL_planesParts {v : Env} {fo : Forest.Heard} {l : List Aff}
    (c : (Forest.planeCols fo.shape v.y.h.lmb).toBool = true) (h : planesL v fo = some l) :
    ∃ pp, Desc.First.K4.planesParts v fo = some pp ∧
      l = fo.leaves.rowForm oneE pp.1 :: pp.2 := by
  have e := planesParts_eq v fo
  rw [if_pos c, h] at e
  obtain ⟨pp, hp, hl⟩ := Option.map_eq_some_iff.mp e
  exact ⟨pp, hp, hl.symm⟩

/-- The library's list has three forms. -/
theorem planesL_length {v : Env} {fo : Forest.Heard} {l : List Aff} (h : planesL v fo = some l) :
    l.length = 3 := by
  unfold planesL planeFormsO at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨rows, h3, e⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h3⟩ := Option.bind_eq_some_iff.mp h3
  obtain ⟨_, _, h3⟩ := Option.bind_eq_some_iff.mp h3
  obtain ⟨_, _, h3⟩ := Option.bind_eq_some_iff.mp h3
  obtain rfl := Option.some.inj h3
  obtain rfl := Option.some.inj e
  rfl

/-- `front_library` with the planes' three forms as the library's list. -/
theorem front_planesL {P : Pub} {g : Nat} {o : Own} {F G : Fork} {fs : Array Aff}
    (hp : o.v.y.h.p3 = true) (h : Desc.First.K4.formsFront P g o F = some (fs, G)) :
    ∃ sh tT l2 g46 l7 l89 l10 lP l12,
      ((Array.range (4 * P.y.NI)).mapM fun i => F.shown (o.H.tV.sEnd + i)) = some sh ∧
      o.H.tT = some tT ∧
      Road.normsL P o.v o.H = some l2 ∧ Desc.First.K4.rowsForms o.v o.H = some g46 ∧
      Road.Rows.termsL o.v tT.sEnd = some l7 ∧ Road.Rows.gatedL P o.v o.hd o.hd2 = some l89 ∧
      Road.oneHotL o.v = some l10 ∧ planesL o.v o.H.fo = some lP ∧
      (if g == 0 then Road.embL o.v o.H o.sVE else some []) = some l12 ∧
      fs.toList = o.H.fo.rows.toList ++ l2 ++
        [Road.rowBatchForm P.y o.H,
          o.H.tV.p.rowForm (Desc.First.K4.rowsSummand P.y o.H sh) {}] ++ g46 ++ l7 ++ l89 ++ l10 ++
        lP ++ l12 := by
  obtain ⟨sh, pp, tT, l2, g46, l7, l89, l10, l12, a1, a2, a3, a4, a5, a6, a7, a8, a9, e⟩ :=
    Road.K4.front_library hp h
  refine ⟨sh, tT, l2, g46, l7, l89, l10, _, l12, a1, a3, a4, a5, a6, a7, a8,
    planesParts_planesL a2, a9, ?_⟩
  rw [e]

/-- The same for both runs that the layers' block may state (with the lookup's own rows in front, or
without), and without the premise on routed experts: the run's list ends in the library's three
forms on the planes and, in the first group, the library's claim on the embedding. -/
theorem frontWith_planesL {rows : Bool} {P : Pub} {g : Nat} {o : Own} {F G : Fork}
    {fs : Array Aff} (h : Desc.First.K4.formsFrontWith rows P g o F = some (fs, G)) :
    ∃ pre lP l12, planesL o.v o.H.fo = some lP ∧ lP.length = 3 ∧
      (if g == 0 then Road.embL o.v o.H o.sVE else some []) = some l12 ∧
      fs.toList = pre ++ lP ++ l12 := by
  obtain ⟨sh, pp, l, _, _, _, a2, a3, a4, _, _, _⟩ := Desc.First.K4.formsFrontWith_some h
  obtain ⟨g2, g46, g7, g89, g10, g11, g12, _, _, _, _, _, b6, b7, e⟩ :=
    Desc.First.K4.front_some a3
  rw [a2] at b6
  cases b6
  rw [Road.K4.embeddingForm_embL] at b7
  have aP := planesParts_planesL a2
  refine ⟨(if rows then o.H.fo.rows.toList else []) ++ g2 ++
    [Desc.First.K4.rowBatchForm P.y o.H,
      o.H.tV.p.rowForm (Desc.First.K4.rowsSummand P.y o.H sh) {}] ++ g46 ++ g7 ++ g89 ++ g10,
    _, g12, aP, planesL_length aP, b7, ?_⟩
  rw [a4, e]

/-- In such a run each of the three forms is among the run's forms, and each names entries of the
array of reads alone, if the start form of the leaves' sumcheck does. -/
theorem planes_rowsIn {rows : Bool} {P : Pub} {g : Nat} {o : Own} {F G : Fork} {fs : Array Aff}
    (h : Desc.First.K4.formsFrontWith rows P g o F = some (fs, G))
    (hs : Road.Rows.RowsIn (fun a _ => a = o.v.iU3) o.H.fo.leaves.start) :
    ∃ lP, planesL o.v o.H.fo = some lP ∧ (∀ f ∈ lP, f ∈ fs.toList) ∧
      ∀ f ∈ lP, Road.Rows.RowsIn (fun a _ => a = o.v.iU3) f := by
  obtain ⟨_, lP, _, aP, _, _, e⟩ := frontWith_planesL h
  refine ⟨lP, aP, fun f hf => ?_, Road.Rows.rowsIn_planesL hs aP⟩
  rw [e]
  simp [hf]

#print axioms planesParts_eq
#print axioms planesParts_planesL
#print axioms planesL_planesParts
#print axioms front_planesL
#print axioms frontWith_planesL
#print axioms planes_rowsIn

end Meaning.Planes
