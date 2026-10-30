-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/ListsTie2.lean: two more plain lists of claims of the layers' own rounds
(OnBytes/Desc/First/K4/Claims.lean) are the library's lists.

  `termsForms_termsL`: with routed experts, where K4's group 7 is there, the library's termsL
      (Johnson/Road/Rows/LayerEnds3S.lean) is there, the same list.
  `endsForms_endsL`, `gatedForms_gatedL`: where K4's groups 8 and 9 are there, the library's gatedL
      (Johnson/Road/Rows/GatedClaims.lean) is there, the same list.

Limits. As Johnson/Road/K4/ListsTie.lean: equations between lists of forms; no theorem on a run of
the program `verify-on-bytes` is called.
-/
import Johnson.Road.K4.ListsTie
import Johnson.Road.Rows.LayerEnds3S
import Johnson.Road.Rows.GatedClaims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env Lay Heard Pub)

/-- A list of one-member lists, laid end to end. -/
theorem mapM_flat {α : Type} (f : α → Option Aff) (g : α → Aff → Aff) (xs : List α) :
    (xs.mapM fun a => (f a).bind fun s => some [g a s]).map List.flatten =
      xs.mapM fun a => (f a).map (g a) := by
  have e := mapM_singletons (fun a => (f a).map (g a)) xs
  have e2 : (fun a => ((f a).map (g a)).bind fun s => some [s]) =
      fun a => (f a).bind fun s => some [g a s] := by
    funext a
    cases f a <;> rfl
  rw [e2] at e
  exact e

theorem termsForms_termsL {v : Env} {H : Heard} {tT : Tsc} {l : List Aff} (hT : H.tT = some tT)
    (hp : v.y.h.p3 = true) (h : Desc.First.K4.termsForms v H = some l) :
    Rows.termsL v tT.sEnd = some l := by
  unfold Desc.First.K4.termsForms at h
  obtain ⟨tT', e, h⟩ := Option.bind_eq_some_iff.mp h
  rw [hT] at e
  cases e
  obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
  have hl : l = a ++ b ++ c := (Option.some.inj h).symm
  have A : ((List.range (v.y.NN * v.y.Lam)).mapM fun i =>
      (v.rowR "rt" i).bind fun f => some [Aff.slot (tT.sEnd + i) - f]).map List.flatten =
      some a := (mapM_flat _ _ _).trans ha
  have B : ((List.range v.y.LamM).mapM fun lm =>
      (v.shA "sc" "rt" lm 0).bind fun f =>
        some [Aff.slot (tT.sEnd + v.y.NN * v.y.Lam + lm) - f]).map List.flatten = some b :=
    (mapM_flat _ _ _).trans hb
  have C : ((List.range (v.y.LamM * v.y.h.NE)).mapM fun x =>
      (v.shA "sel" "rt" (x / v.y.h.NE) (x % v.y.h.NE)).bind fun f =>
        some [Aff.slot (tT.sEnd + v.y.NN * v.y.Lam + v.y.LamM + x) - f]).map List.flatten =
      some c := (mapM_flat _ _ _).trans hc
  unfold Rows.termsL
  rw [if_pos hp, A, B, C, hl]
  simp [Road.appL]

theorem endsForms_endsL {v : Env} {o : Level} {e : Array E} {t rows blocks stride : Nat}
    {lamOf : Nat → Nat} {first : Nat} {l : List Aff}
    (h : Desc.First.K4.endsForms v o e t rows blocks stride lamOf first = some l) :
    Rows.endsL v o e t rows blocks stride lamOf first = some l := by
  unfold Desc.First.K4.endsForms at h
  obtain ⟨ts, a1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tu, a2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨aS, a3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨aU, a4, h⟩ := Option.bind_eq_some_iff.mp h
  have a3' : Rows.endForm v t ts e rows blocks stride lamOf first = some aS := a3
  have a4' : Rows.endForm v t tu e rows blocks stride lamOf first = some aU := a4
  have hl : l = [Aff.slot o.sL + aS, Aff.slot o.sR + aU] := (Option.some.inj h).symm
  unfold Rows.endsL
  rw [a1, a2, hl]
  simp [a3', a4', Road.appL]

theorem gatedForms_gatedL {P : Pub} {v : Env} {hd : Level} {hd2 : Option Level} {l : List Aff}
    (h : Desc.First.K4.gatedForms P v hd hd2 = some l) : Rows.gatedL P v hd hd2 = some l := by
  unfold Desc.First.K4.gatedForms at h
  obtain ⟨e, a1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨t, a2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨a, a3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨o, a4, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨e2, a5, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨t2, a6, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b, a7, h⟩ := Option.bind_eq_some_iff.mp h
  have hl : l = hd.row :: a ++ o.row :: b := (Option.some.inj h).symm
  have a3' := endsForms_endsL a3
  have a7' := endsForms_endsL a7
  subst a4
  have g2 : Rows.gatedL2 P v (some o) = some (o.row :: b) := by
    simp [Rows.gatedL2, a5, a6, a7', Road.appL]
  unfold Rows.gatedL
  rw [a1, a2, hl]
  simp [a3', g2, Road.appL]

end OnBytes.Road.K4
