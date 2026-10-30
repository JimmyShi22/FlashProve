-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/JoinTie.lean: the start form of the batched sumcheck, as K4's own text makes it, is
the library's plain function `startOf`.

Johnson/Road/FormsKeysStart.lean writes the last lines of the routine Layer.joinStart as a plain
function `startOf H om parts` of what was heard, the two weights and the calls' factors, and the
theorems on what the start form is worth (Johnson/Road/FormsKeysWhole.lean, FormsKeysCaller.lean,
Rows/LayerEnds34.lean) speak of that function. Here: where K4's own `joinStart`
(OnBytes/Desc/First/K4/Hear.lean), run over the plain engine, returns a form, it is `startOf` at the
factors that the layout's own plain functions give; the ledger and the rounds are as they were; and
its two public tests have passed.

  `flNeed_some`: a value that is there.
  `joinStart_startOf`: the law.

Limits. An identity on data: nothing on what the form is worth, on a draw, on soundness. If the
plain functions' text (OnBytes/K/Kc/Flat.lean) turns, this law is owed anew. No theorem on a run of
the program `verify-on-bytes` is called.
-/
import OnBytes.Desc.First.K4.HearLaws
import Johnson.Road.FormsKeysStart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Env Heard aff0)
open OnBytes.Desc.First.K4 (engFl andThen_some must_some)

theorem flNeed_some {α : Type} {x : Option α} {a : α} {F G : Fork} {t u : Tape}
    (h : Fl.need x F t = some (a, G, u)) : x = some a ∧ G = F ∧ u = t := by
  unfold Fl.need at h
  obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  exact ⟨by rw [hb, e.1], e.2.1.symm, e.2.2.symm⟩

theorem joinStart_startOf {v : Env} {H : Heard} {om : Array E} {C : Aff} {F F' : Fork}
    {t t' : Tape} (h : Desc.First.K4.joinStart engFl v H om F t = some (C, F', t')) :
    ∃ weighed parts laid tT,
      v.y.calls.mapM v.weighedOf = some weighed ∧
      ((v.y.calls.zip weighed).toList.zipIdx.mapM fun x =>
        v.joinPart H.fo.alpha H.fo.theta x.2 x.1.1 x.1.2) = some parts ∧
      (parts.length == H.fo.shape.calls.size && H.fo.e.size == H.fo.shape.calls.size) = true ∧
      weighed.toList.zipIdx.foldlM (fun laid x => v.laidOf x.2 x.1 laid)
        (Forest.noPub H.fo.shape) = some laid ∧
      (laid == H.fo.shape.pub) = true ∧ H.tT = some tT ∧
      C = startOf H om parts ∧ F' = F ∧ t' = t := by
  have h' : Fl.andThen (Fl.need (v.y.calls.mapM v.weighedOf)) (fun weighed =>
      Fl.andThen (Fl.need ((v.y.calls.zip weighed).toList.zipIdx.mapM fun x =>
        v.joinPart H.fo.alpha H.fo.theta x.2 x.1.1 x.1.2)) (fun parts =>
      Fl.andThen (Fl.must (parts.length == H.fo.shape.calls.size &&
        H.fo.e.size == H.fo.shape.calls.size)) (fun _ =>
      Fl.andThen (Fl.need (weighed.toList.zipIdx.foldlM (fun laid x => v.laidOf x.2 x.1 laid)
        (Forest.noPub H.fo.shape))) (fun laid =>
      Fl.andThen (Fl.must (laid == H.fo.shape.pub)) (fun _ =>
      Fl.andThen (Fl.need H.tT) (fun tT =>
      Fl.ret (((parts.zipIdx.foldl (fun (a : Aff) x => a.addMul x.1 (H.fo.e.getD x.2 zeroE)) aff0 +
          Aff.ofConst ((List.range (2 ^ H.fo.shape.rK - H.fo.shape.NT)).foldl
            (fun a t => addE a (mulE ((eqTab H.fo.zy).getD (H.fo.shape.NT + t) zeroE)
              (subE H.fo.alpha (H.fo.padKey 0)))) zeroE)) -
          Aff.slot tT.sCl - H.fo.cEnd).addMul H.KT (om.getD 1 zeroE)))))))) F t =
      some (C, F', t') := h
  obtain ⟨weighed, F1, t1, a1, h1⟩ := andThen_some h'
  obtain ⟨parts, F2, t2, a2, h2⟩ := andThen_some h1
  obtain ⟨_, F3, t3, a3, h3⟩ := andThen_some h2
  obtain ⟨laid, F4, t4, a4, h4⟩ := andThen_some h3
  obtain ⟨_, F5, t5, a5, h5⟩ := andThen_some h4
  obtain ⟨tT, F6, t6, a6, h6⟩ := andThen_some h5
  obtain ⟨b1, rfl, rfl⟩ := flNeed_some a1
  obtain ⟨b2, rfl, rfl⟩ := flNeed_some a2
  obtain ⟨b3, rfl, rfl⟩ := must_some a3
  obtain ⟨b4, rfl, rfl⟩ := flNeed_some a4
  obtain ⟨b5, rfl, rfl⟩ := must_some a5
  obtain ⟨b6, rfl, rfl⟩ := flNeed_some a6
  unfold Fl.ret at h6
  simp only [Option.some.injEq, Prod.mk.injEq] at h6
  obtain ⟨eC, eF, et⟩ := h6
  refine ⟨weighed, parts, laid, tT, b1, b2, b3, b4, b5, b6, ?_, eF.symm, et.symm⟩
  rw [← eC]
  unfold startOf padOf
  simp only [b6, Option.isSome_some, if_true]

#print axioms joinStart_startOf

end OnBytes.Road.K4
