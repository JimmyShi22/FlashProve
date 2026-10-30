-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/OwnFirst.lean: THE JOINT AT K4's TEXT IN THE FIRST GROUP: what the chain of the
first sub-proof's own rounds (`LayOwnFirst.ch`, Cb/Pv/Lay/Own.lean: three points in front) puts out
at the image of the written transcript is, by name, the statement `TailH.z7` of the words on the
tape. Statements and proofs. The twin of OwnView.lean's `own_val_z7` and OwnJoint.lean's `k4_val`.

  `own_val_z7F`: under `TailM.Ok`, `TailWords` at the cut behind the three points, the three points'
    words and `TailH.Claims`: `(A.ch.val Ex (x, y) (((ownFirstM A dT dA dB W).mapsR Ex).view τ)).1 =
    D.z7 (((x, the token point), the second point), the third point)`.
  `k4_valF`: the same at the data `tailT W (ksOf P hp) (((t0.drop 1).drop 1).drop 1) nz a`, if t0 is
    the flat tape of τ: the three points are what the tape's first three rounds drew.

NO NEW ARGUMENT: `ChM.val_view` (ChView.lean), `point_view`, `trs_eq` (OwnView.lean), `own_run_z7F`
(TailRun.lean), `tailT_is` (TailTape.lean).

Limits. Those of OwnView.lean and OwnJoint.lean. The hearing does not occur here: OwnRecsG.lean's
`own_callsG` names its calls on the cuts of `t0.drop (k0 g)`, and k0 g = 3 in the first group. The
embedding's claim is not spoken of. Nothing on soundness.
-/
import Johnson.Road.K4.OwnJoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open Iop Cb TWhole Cb.Pv.Lay Cb.Pv.Att
open OnBytes OnBytes.K.Kc OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.Desc.First.K4
open OnBytes.Model.Layer (Pub HPlan2)
open OnBytes.Tie.Pv.Lay.Eng (TailH ownTrsF)
open OnBytes.Desc.First.P1 (gl NzT Adds7 tailT tailT_is TailM TailR TailWords ownFirstM KeepsWords
  IsTape drawnOf drawnE point_view trs_eq own_run_z7F ChM.val_view)
open _root_.Run (ckP)

variable {M X : Type}

/-- **What the first sub-proof's chain puts out at the image of a written transcript, by name.** -/
theorem own_val_z7F (Ex : ExtSpec) (A : LayOwnFirst GE M X) (dT dA dB : RDT) {R : TailR}
    {W : TailM A.tail R} (ok : W.Ok)
    (τ : Tr (uLT (ckP .two) ([dT] ++ ([dA] ++ ([dB] ++ R.all))))) {pT pA pB : List E}
    {D : TailH gl A.tail}
    (hT : pT = drawnE dT (Maps.trL [dT] ([dA] ++ ([dB] ++ R.all)) τ).2.1)
    (hA : pA = drawnE dA (Maps.trL [dA] ([dB] ++ R.all)
      (Maps.trR [dT] ([dA] ++ ([dB] ++ R.all)) τ)).2.1)
    (hB : pB = drawnE dB (Maps.trL [dB] R.all (Maps.trR [dA] ([dB] ++ R.all)
      (Maps.trR [dT] ([dA] ++ ([dB] ++ R.all)) τ))).2.1)
    (h : TailWords W (Maps.trR [dB] R.all (Maps.trR [dA] ([dB] ++ R.all)
      (Maps.trR [dT] ([dA] ++ ([dB] ++ R.all)) τ))) D) (x : X) (y : Ex.Str)
    (hc : D.Claims (((x, Johnson.L5.Layers.rd gl A.gT pT), Johnson.L5.Layers.rd gl A.gA pA),
      Johnson.L5.Layers.rd gl A.gB pB)) :
    (A.ch.val Ex (x, y) (((ownFirstM A dT dA dB W).mapsR Ex).view τ)).1 =
      D.z7 (((x, Johnson.L5.Layers.rd gl A.gT pT), Johnson.L5.Layers.rd gl A.gA pA),
        Johnson.L5.Layers.rd gl A.gB pB) := by
  rw [ChM.val_view]
  have e : (ownFirstM A dT dA dB W).trs τ = ownTrsF A pT pA pB D :=
    congrArg₂ Prod.mk ((point_view A.gT dT _).trans (by rw [← hT]))
      (congrArg₂ Prod.mk ((point_view A.gA dA _).trans (by rw [← hA]))
        (congrArg₂ Prod.mk ((point_view A.gB dB _).trans (by rw [← hB])) (trs_eq ok h)))
  show A.ch.run x ((ownFirstM A dT dA dB W).trs τ) = _
  rw [e]
  exact own_run_z7F A pT pA pB D x hc

/-- **The same in the words of K4's tape.** -/
theorem k4_valF (Ex : ExtSpec) (A : LayOwnFirst GE M X) (dT dA dB : RDT) {R : TailR}
    {W : TailM A.tail R} (ok : W.Ok) {P : Pub} {hp : HPlan2} (hk : (ksOf P hp).Fit R)
    {f : Fmt.RoundView → Fmt.RoundView} (hf : KeepsWords f)
    (τ : Tr (uLT (ckP .two) ([dT] ++ ([dA] ++ ([dB] ++ R.all))))) {t0 : Tape}
    (ht : IsTape f ([dT] ++ ([dA] ++ ([dB] ++ R.all))) τ t0)
    (nz : NzT A.tail (ksOf P hp) (((t0.drop 1).drop 1).drop 1)) (a : Adds7 A.tail) (x : X)
    (y : Ex.Str)
    (hc : (tailT W (ksOf P hp) (((t0.drop 1).drop 1).drop 1) nz a).Claims
      (((x, Johnson.L5.Layers.rd gl A.gT (drawnOf t0)),
        Johnson.L5.Layers.rd gl A.gA (drawnOf (t0.drop 1))),
        Johnson.L5.Layers.rd gl A.gB (drawnOf ((t0.drop 1).drop 1)))) :
    (A.ch.val Ex (x, y) (((ownFirstM A dT dA dB W).mapsR Ex).view τ)).1 =
      (tailT W (ksOf P hp) (((t0.drop 1).drop 1).drop 1) nz a).z7
        (((x, Johnson.L5.Layers.rd gl A.gT (drawnOf t0)),
          Johnson.L5.Layers.rd gl A.gA (drawnOf (t0.drop 1))),
          Johnson.L5.Layers.rd gl A.gB (drawnOf ((t0.drop 1).drop 1))) :=
  own_val_z7F Ex A dT dA dB ok τ (ht.one hf).2.2 (ht.right.one hf).2.2
    (ht.right.right.one hf).2.2 (tailT_is hf W hk ht.right.right.right nz a) x y hc

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.own_val_z7F
#print axioms OnBytes.Road.K4.k4_valF
