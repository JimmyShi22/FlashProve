-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/Reads/CoveredWith.lean: Covered.lean's STATEMENT ON THE RUN "front", AT EITHER FORM
OF THE RUN: `formsFrontWith rows` (OnBytes/Desc/First/K4/Plain.lean): with the lookup's own claims
listed (rows = true: `formsFront`, of which Covered.lean and FrontLaw.lean speak) AND WITHOUT THEM
(rows = false: `formsFrontNoRows`: THE RUN THAT RIDES where the lookup's block states its own
claims). Every entry that a form of the list names lies in the array of reads, inside one of the
families of tables (`InTab`, TermsEnts.lean). Statements and proofs.

  `front_libraryWith`: `front_library` (Johnson/Road/K4/FrontLaw.lean) at either form: the list in
    the library's lists, with the lookup's own rows in front if rows = true, none else. ITS SCRIPT
    IS `front_library`'s (whose two laws beneath, `formsFrontWith_some` and `front_some`, are
    general in rows).
  `front_coveredWith`: `front_covered` at either form: THE PREMISE hK3 ON THE LOOKUP's OWN CLAIMS IS
    ASKED WHERE rows = true ALONE. Its script is `front_covered`'s.
  `p3_of_hear`: where K4's hearing returns o, o.v.y.h.p3 = true (the hearing has asked `covers`,
    whose second clause it is; o.v.y is P.y: `env_of_hear`).
  **`front_coveredWith_heard`**: behind the hearing: all forms of `formsFrontWith rows` are `InTab
    o.v`, under hlv (the lookup's leaves' sumcheck's start form) and, where rows = true, hK3.

Limits. hlv, and hK3 where it is asked, speak of what the lookup returned: paid nowhere here. Those
of Covered.lean. Nothing on soundness.
-/
import Johnson.Road.K4.Reads.Covered
import Johnson.Road.K4.NormWordsOfHear
import OnBytes.Desc.First.K4.HearCalls

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env Lay Heard Pub Own)

/-- The whole list of the run "front", at either form, in the library's lists. -/
theorem front_libraryWith {rows : Bool} {P : Pub} {g : Nat} {o : Own} {F G : Fork}
    {fs : Array Aff} (hp : o.v.y.h.p3 = true)
    (h : Desc.First.K4.formsFrontWith rows P g o F = some (fs, G)) :
    ∃ sh pp tT l2 g46 l7 l89 l10 l12,
      ((Array.range (4 * P.y.NI)).mapM fun i => F.shown (o.H.tV.sEnd + i)) = some sh ∧
      Desc.First.K4.planesParts o.v o.H.fo = some pp ∧ o.H.tT = some tT ∧
      Road.normsL P o.v o.H = some l2 ∧ Desc.First.K4.rowsForms o.v o.H = some g46 ∧
      Rows.termsL o.v tT.sEnd = some l7 ∧ Rows.gatedL P o.v o.hd o.hd2 = some l89 ∧
      Road.oneHotL o.v = some l10 ∧
      (if g == 0 then Road.embL o.v o.H o.sVE else some []) = some l12 ∧
      fs.toList = (if rows then o.H.fo.rows.toList else []) ++ l2 ++
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

end OnBytes.Road.K4

namespace OnBytes.Desc.First.K4.Reads

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env Lay Heard Pub Own HPlan2)

/-- **The run "front", at either form.** -/
theorem front_coveredWith {rows : Bool} {P : Pub} {g : Nat} {o : Own} {F G : Fork}
    {fs : Array Aff} (hp : o.v.y.h.p3 = true)
    (h : formsFrontWith rows P g o F = some (fs, G))
    (hK3 : rows = true → ∀ f ∈ o.H.fo.rows.toList, InTab o.v f)
    (hw : InTab o.v o.H.wpl.row)
    (htV : InTab o.v o.H.tV.p.start)
    (hhd : InTab o.v o.hd.row)
    (hhd2 : ∀ x, o.hd2 = some x → InTab o.v x.row)
    (hlv : InTab o.v o.H.fo.leaves.start) :
    ∀ f ∈ fs.toList, InTab o.v f := by
  obtain ⟨sh, pp, tT, l2, g46, l7, l89, l10, l12, _, hpp, _, h2, h46, h7, h89, h10, h12, e⟩ :=
    OnBytes.Road.K4.front_libraryWith hp h
  obtain ⟨hp1, hp2⟩ := planesParts_in hpp
  intro f hf
  rw [e] at hf
  rcases List.mem_append.mp hf with hf | hf
  · rcases List.mem_append.mp hf with hf | hf
    · rcases List.mem_append.mp hf with hf | hf
      · rcases List.mem_append.mp hf with hf | hf
        · rcases List.mem_append.mp hf with hf | hf
          · rcases List.mem_append.mp hf with hf | hf
            · rcases List.mem_append.mp hf with hf | hf
              · rcases List.mem_append.mp hf with hf | hf
                · cases rows with
                  | true => exact hK3 rfl f hf
                  | false => cases hf
                · exact entsIn_normsL h2 hw f hf
              · rcases List.mem_cons.mp hf with rfl | hf
                · exact entsIn_rowBatch _ _
                rcases List.mem_cons.mp hf with rfl | hf
                · exact entsIn_rowForm _ _ htV entsIn_empty
                cases hf
            · exact rowsForms_in h46 f hf
          · exact termsL_rows h7 f hf
        · exact entsIn_gatedL h89 hhd hhd2 f hf
      · exact entsIn_oneHotL h10 f hf
    · rcases List.mem_cons.mp hf with rfl | hf
      · exact entsIn_rowForm _ _ hlv hp1
      · exact hp2 f hf
  · split at h12
    · exact entsIn_embL h12 f hf
    · cases h12
      cases hf

variable {P : Pub} {hpl : HPlan2} {g : Nat} {fo : Forest.Heard} {F0 G0 : Fork}
  {t u : OnBytes.K.Kc.Tape} {o : Own}

/-- Behind the hearing the layout has routed experts. -/
theorem p3_of_hear (hh : hearFl P hpl g fo F0 t = some (o, G0, u)) : o.v.y.h.p3 = true := by
  have hc := (hear_calls hh).1
  unfold covers at hc
  simp only [Bool.and_eq_true] at hc
  rw [(OnBytes.Road.K4.env_of_hear hh).1]
  exact hc.1.1.1.2

/-- **The run "front", at either form, behind the hearing.** -/
theorem front_coveredWith_heard {rows : Bool} {F G : Fork} {fs : Array Aff}
    (hh : hearFl P hpl g fo F0 t = some (o, G0, u))
    (h : formsFrontWith rows P g o F = some (fs, G))
    (hK3 : rows = true → ∀ f ∈ o.H.fo.rows.toList, InTab o.v f)
    (hlv : InTab o.v o.H.fo.leaves.start) :
    ∀ f ∈ fs.toList, InTab o.v f := by
  obtain ⟨a1, a2, a3, a4, _⟩ := hear_starts hh (inTab o.v)
  exact front_coveredWith (p3_of_hear hh) h hK3 a1 a2 a3 a4 hlv

end OnBytes.Desc.First.K4.Reads

#print axioms OnBytes.Road.K4.front_libraryWith
#print axioms OnBytes.Desc.First.K4.Reads.front_coveredWith
#print axioms OnBytes.Desc.First.K4.Reads.front_coveredWith_heard
