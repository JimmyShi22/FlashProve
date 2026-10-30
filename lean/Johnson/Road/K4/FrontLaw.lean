-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/FrontLaw.lean: the whole list of claims of the layers' own rounds, in one statement,
in the library's lists.

  `front_library`: where the run `formsFront` (OnBytes/Desc/First/K4/Plain.lean) returns, with
      routed
      experts, its list of forms is, in this order: the lookup's own rows; the library's normsL; its
      rowBatchForm; the own claim of the row products' sumcheck (its rowForm at K4's summand on the
      shown values); K4's groups 4 to 6; the library's termsL, gatedL, oneHotL; the own claim of the
      lookup's leaves' sumcheck; the two further claims on the planes; and, in the first group, the
      library's embL.
  `back_library`: the run `formsBack` returns the batched sumcheck's own claim, the library's two
      claims on the sides' hidden values, and the merge's own claim (its rowForm).

So every theorem of Johnson/Road/ on what a form of these lists is worth speaks of K4's own text.

Limits. An identity of lists of forms: nothing on what a form is worth, on a draw, on soundness.
Groups 4 to 6 stay K4's own list (`rowsForms`): K4 makes them by the norm's row's formulas
(OnBytes/Desc/First/P6), the library by ledCarry5 and ledLines5, and the two are not compared as
lists here. The planes' claims stay K4's too. No theorem on a run of the program `verify-on-bytes`
is called.
-/
import Johnson.Road.K4.ListsTie2
import OnBytes.Desc.First.K4.ClaimsLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env Lay Heard Pub Own)

theorem termsForms_tT {v : Env} {H : Heard} {l : List Aff}
    (h : Desc.First.K4.termsForms v H = some l) : ∃ tT, H.tT = some tT := by
  unfold Desc.First.K4.termsForms at h
  obtain ⟨tT, e, _⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨tT, e⟩

theorem front_library {P : Pub} {g : Nat} {o : Own} {F G : Fork} {fs : Array Aff}
    (hp : o.v.y.h.p3 = true) (h : Desc.First.K4.formsFront P g o F = some (fs, G)) :
    ∃ sh pp tT l2 g46 l7 l89 l10 l12,
      ((Array.range (4 * P.y.NI)).mapM fun i => F.shown (o.H.tV.sEnd + i)) = some sh ∧
      Desc.First.K4.planesParts o.v o.H.fo = some pp ∧ o.H.tT = some tT ∧
      Road.normsL P o.v o.H = some l2 ∧ Desc.First.K4.rowsForms o.v o.H = some g46 ∧
      Rows.termsL o.v tT.sEnd = some l7 ∧ Rows.gatedL P o.v o.hd o.hd2 = some l89 ∧
      Road.oneHotL o.v = some l10 ∧
      (if g == 0 then Road.embL o.v o.H o.sVE else some []) = some l12 ∧
      fs.toList = o.H.fo.rows.toList ++ l2 ++
        [Road.rowBatchForm P.y o.H,
          o.H.tV.p.rowForm (Desc.First.K4.rowsSummand P.y o.H sh) {}] ++ g46 ++ l7 ++ l89 ++ l10 ++
        o.H.fo.leaves.rowForm oneE pp.1 :: pp.2 ++ l12 := by
  obtain ⟨sh, pp, l, _, _, a1, a2, a3, a4, _, _, _⟩ := Desc.First.K4.formsFrontWith_some h
  obtain ⟨g2, g46, g7, g89, g10, g11, g12, b1, b2, b3, b4, b5, b6, b7, e⟩ :=
    Desc.First.K4.front_some a3
  obtain ⟨tT, hT⟩ := termsForms_tT b3
  rw [a2] at b6
  cases b6
  rw [embeddingForm_embL] at b7
  rw [oneHotForms_oneHotL o.v hp] at b5
  refine ⟨sh, pp, tT, g2, g46, g7, g89, g10, g12, a1, a2, hT, normsForms_normsL b1, b2,
    termsForms_termsL hT hp b3, gatedForms_gatedL b4, b5, b7, ?_⟩
  rw [a4, e, ← rowBatchForm_eq]
  simp

theorem back_library {o : Own} {F G : Fork} {fs : Array Aff}
    (h : Desc.First.K4.formsBack o F = some (fs, G)) :
    fs.toList = [o.K.rowS, Aff.slot o.K.sA0 - o.K.fin.Alin, Aff.slot o.K.sB0 - o.K.fin.Blin,
      o.wo.toWsMerged.p.rowForm o.wo.toWsMerged.fvp {}] := by
  obtain ⟨_, e, _, _⟩ := Desc.First.K4.formsBack_some h
  rw [e]
  rfl

#print axioms front_library
#print axioms back_library

end OnBytes.Road.K4
