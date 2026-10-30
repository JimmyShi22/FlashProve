-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/ListsTie.lean: the plain lists of claims of the layers' own rounds
(OnBytes/Desc/First/K4/Claims.lean) are the library's lists.

Johnson/Road/FormsKeysClaims.lean has five lists of forms as plain functions of what was heard
(normsL, rowBatchForm, ledgerL, oneHotL, embL), and Johnson/Road/FormsKeysIdnW.lean and
FormsKeysIdnL.lean show what these forms are worth in a world. This file ties four of K4's plain
functions to them, so that each theorem ON THE LISTS speaks of K4's own text. No theorem on a run of
`verify-on-bytes` (that file's adds_…) is called here, or meant to be called through this tie.

  `normsForms_normsL`: where K4's group 2 is there, the library's normsL is there, the same list.
  `rowBatchForm_eq`: K4's first claim of group 3 is the library's form.
  `oneHotForms_oneHotL`: with routed experts, K4's group 10 is the library's oneHotL.
  `embeddingForm_embL`: K4's group 12 is the library's embL.

Limits. Equations between lists of forms: nothing on what a form is worth, on a draw, on soundness.
normsForms asks one public condition more than normsL (three numbers of the layout's tensors agree),
so the first tie goes one way. Groups 4 to 6 are not tied here: K4 makes them by the norm's row's
formulas (OnBytes/Desc/First/P6), the library by ledCarry5 and ledLines5.
-/
import Johnson.Road.FormsKeysClaims
import OnBytes.Desc.First.K4.Claims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env Lay Heard Pub)

theorem rowBatchForm_eq (y : Lay) (H : Heard) :
    Desc.First.K4.rowBatchForm y H = Road.rowBatchForm y H := rfl

theorem need_some {b : Bool} {u : Unit} (h : Desc.First.K4.need b = some u) : b = true := by
  unfold Desc.First.K4.need at h
  cases b with
  | true => rfl
  | false => simp at h

theorem normsForms_normsL {P : Pub} {v : Env} {H : Heard} {l : List Aff}
    (h : Desc.First.K4.normsForms P v H = some l) : Road.normsL P v H = some l := by
  unfold Desc.First.K4.normsForms at h
  obtain ⟨txs, a1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tI, a2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tA, a3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨e, a4, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨sum, a5, h⟩ := Option.bind_eq_some_iff.mp h
  have a5' : Road.normsSum P.y v tI tA txs e H.gp = some sum := a5
  have hl : l = [H.wpl.row, Aff.slot H.wpl.sL - Aff.slot H.wpl.sR, Aff.slot H.wpl.sL + sum] :=
    (Option.some.inj h).symm
  subst hl
  unfold Road.normsL
  rw [a1]
  simp only [Option.bind_some, a2, a3, a4, a5', Road.appL, Option.map_some, List.cons_append,
    List.nil_append]

theorem embeddingForm_embL (v : Env) (H : Heard) (sVE : Nat) :
    (Desc.First.K4.embeddingForm v H sVE).map ([·]) = Road.embL v H sVE := by
  have e : Desc.First.K4.embeddingForm v H sVE =
      (v.tabAt "xbI@Z_E").bind fun t => (Road.embSum v t H.tkh).bind fun s =>
        some ((Aff.slot sVE).scale (negE oneE) + s) := rfl
  rw [e]
  unfold Road.embL
  cases v.tabAt "xbI@Z_E" with
  | none => rfl
  | some t =>
    cases h : Road.embSum v t H.tkh with
    | none => simp [h]
    | some s => simp [h]

theorem mapM_singletons {α : Type} (f : α → Option Aff) : ∀ xs : List α,
    (xs.mapM fun a => (f a).bind fun s => some [s]).map List.flatten = xs.mapM f
  | [] => rfl
  | a :: xs => by
    have ih := mapM_singletons f xs
    rw [List.mapM_cons, List.mapM_cons]
    cases h1 : f a with
    | none => rfl
    | some s =>
      simp only [Option.bind_some, bind, pure]
      cases h2 : xs.mapM f with
      | none =>
        rw [h2] at ih
        cases h3 : (xs.mapM fun a => (f a).bind fun s => some [s]) with
        | none => rfl
        | some L => rw [h3] at ih; simp at ih
      | some r =>
        rw [h2] at ih
        cases h3 : (xs.mapM fun a => (f a).bind fun s => some [s]) with
        | none => rw [h3] at ih; simp at ih
        | some L =>
          rw [h3] at ih
          simp only [Option.map_some, Option.some.injEq] at ih
          simp [ih]

theorem oneHotForms_oneHotL (v : Env) (hp : v.y.h.p3 = true) :
    Desc.First.K4.oneHotForms v = Road.oneHotL v := by
  unfold Desc.First.K4.oneHotForms Road.oneHotL
  rw [if_pos hp]
  have e := mapM_singletons
    (fun lm => (Road.hotSum v lm).map fun s => Aff.ofConst (negE oneE) + s) (List.range v.y.LamM)
  have e2 : (fun lm => ((Road.hotSum v lm).map fun s => Aff.ofConst (negE oneE) + s).bind
      fun s => some [s]) = fun lm => (Road.hotSum v lm).bind fun s =>
        some [Aff.ofConst (negE oneE) + s] := by
    funext lm
    cases Road.hotSum v lm <;> rfl
  rw [e2] at e
  rw [e]
  rfl

end OnBytes.Road.K4
