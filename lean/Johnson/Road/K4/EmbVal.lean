-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/EmbVal.lean: the record EmbAsks (Johnson/Road/K4/EmbFirst.lean) at a hearing in the
first group (embAsks_of_hear, Johnson/Road/K4/EmbJoin.lean), AT THE STATEMENT IN FRONT THAT THE TAPE
MAKES: a first statement x with the readings of what the tape's first three rounds drew; and so at
what the first sub-proof's chain puts out at the image of a written transcript.

  `embAsks_at_pts`: embAsks_of_hear at that statement in front. Its two premises on the second and
    the third point hold there by definition, and are asked no more.
  `drop_k0`: in the first group the tape behind k0 g rounds is the tape behind three rounds, one by
    one: the hearing's laws write the first, k4_valF the second.
  `embAsks_at_ptsT`: embAsks_at_pts at any tape that is the tape behind k0 g rounds.
  `embAsks_at_val`: EmbAsks at the first component of `Pf.ownF.toOwn.ch.val` at the image of a
    written transcript whose flat tape is t0: by k4_valF (Johnson/Road/K4/OwnFirst.lean), which
    names that output: TailH.z7, at this triple of points, of the data read off the tape behind
    three rounds.
Limits. All other premises of embAsks_of_hear stay: see EmbJoin.lean's Limits. embAsks_at_val asks
k4_valF's premises beside them: the numbering is lawful (W'.Ok); the sumchecks' numbers of rounds
fit (Ks.Fit); f keeps words; t0 is the flat tape of the transcript; the letters' claims hold at the
statements that the stages find (TailH.Claims). One direction: from a return. Nothing on soundness
or on hiding.


-/
import Johnson.Road.K4.EmbJoin
import Johnson.Road.K4.OwnFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Fork Level Tsc)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard)
open OnBytes.Desc.First.P1 (gl NzT Adds7 TailM TailR tailT drawnOf ownFirstM KeepsWords IsTape)
open OnBytes.Desc.First.K4 (k0 hear engFl)
open Inst.Model (Scl)
open _root_.Run (ckP)

/-- In the first group: behind k0 g rounds is behind three rounds, one by one. -/
theorem drop_k0 {g : ℕ} (hg : (g == 0) = true) (t : Tape) :
    t.drop (k0 g) = ((t.drop 1).drop 1).drop 1 := by
  have e : k0 g = 3 := by
    unfold k0
    rw [if_pos hg]
  rw [e]
  match t with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | _ :: _ :: _ :: _ => rfl

variable [scl : Scl] {M X : Type} (Pf : FullFPar Cb.Gl.E M X) {R : TailR} (W' : TailM (tailW Pf) R)
  {P : Pub} {hp : HPlan2} {g : ℕ} {fo : OnBytes.Model.Forest.Heard} {o : Own} {F G : Fork}
  {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc} {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork}
  {u5 : Tape}

/-- **EmbAsks at a hearing in the first group, at the statement in front that the tape makes.** -/
theorem embAsks_at_pts (Xp : Rows.Pub34 Cb.Gl.E)
    (Ld : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (hg : (g == 0) = true) (h : hear engFl P hp g fo F t0 = some (o, G, u))
    (nz : NzT (tailW Pf) (ksOf P hp) (t0.drop (k0 g))) (a : Adds7 (tailW Pf)) (x : X) {Hl : Fork}
    (lH : Fo.Later G5 Hl) (mask : ℕ → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E) (m : M)
    (hρ : Xp.ρ = gl) (hH : Xp.H = o.H) (nl5 : P.y.xb.nl = 5) (hnb : P.y.h.d / P.y.S2 = Pf.nb)
    (hls : P.y.ls = Pf.ls) (hgB : P.y.lPd - P.y.ls = Pf.gB) (hlt : P.y.h.lt = Pf.D.lT)
    (hy : Pf.msg m Pf.mkE = mask o.sVE) :
    EmbAsks Pf Xp (Hl.worldOf gl mask entry) o
      ((k4TailG W' P hp g t0 nz a).z7
        (((x, Johnson.L5.Layers.rd gl Pf.D.lT (drawnOf t0)),
          Johnson.L5.Layers.rd gl (Pf.ls + Pf.D.lT) (drawnOf (t0.drop 1))),
          Johnson.L5.Layers.rd gl Pf.gB (drawnOf ((t0.drop 1).drop 1)))) m :=
  embAsks_of_hear Pf W' Xp Ld hg h nz a _ lH mask entry m hρ hH nl5 hnb hls hgB hlt rfl rfl hy

/-- The same at any tape that is the tape behind k0 g rounds. -/
theorem embAsks_at_ptsT (Xp : Rows.Pub34 Cb.Gl.E)
    (Ld : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (hg : (g == 0) = true) (h : hear engFl P hp g fo F t0 = some (o, G, u)) {tb : Tape}
    (e : t0.drop (k0 g) = tb) (nz : NzT (tailW Pf) (ksOf P hp) tb) (a : Adds7 (tailW Pf)) (x : X)
    {Hl : Fork} (lH : Fo.Later G5 Hl) (mask : ℕ → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E) (m : M)
    (hρ : Xp.ρ = gl) (hH : Xp.H = o.H) (nl5 : P.y.xb.nl = 5) (hnb : P.y.h.d / P.y.S2 = Pf.nb)
    (hls : P.y.ls = Pf.ls) (hgB : P.y.lPd - P.y.ls = Pf.gB) (hlt : P.y.h.lt = Pf.D.lT)
    (hy : Pf.msg m Pf.mkE = mask o.sVE) :
    EmbAsks Pf Xp (Hl.worldOf gl mask entry) o
      ((tailT W' (ksOf P hp) tb nz a).z7
        (((x, Johnson.L5.Layers.rd gl Pf.D.lT (drawnOf t0)),
          Johnson.L5.Layers.rd gl (Pf.ls + Pf.D.lT) (drawnOf (t0.drop 1))),
          Johnson.L5.Layers.rd gl Pf.gB (drawnOf ((t0.drop 1).drop 1)))) m := by
  subst e
  exact embAsks_at_pts Pf W' Xp Ld hg h nz a x lH mask entry m hρ hH nl5 hnb hls hgB hlt hy

/-- **EmbAsks at what the first sub-proof's chain puts out at a written transcript's image.** -/
theorem embAsks_at_val (Ex : ExtSpec) (dT dA dB : RDT) (ok : W'.Ok) (hk : (ksOf P hp).Fit R)
    {f : Fmt.RoundView → Fmt.RoundView} (hf : KeepsWords f)
    (τ : Tr (uLT (ckP .two) ([dT] ++ ([dA] ++ ([dB] ++ R.all)))))
    (ht : IsTape f ([dT] ++ ([dA] ++ ([dB] ++ R.all))) τ t0) (Xp : Rows.Pub34 Cb.Gl.E)
    (Ld : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (hg : (g == 0) = true) (h : hear engFl P hp g fo F t0 = some (o, G, u))
    (nz : NzT (tailW Pf) (ksOf P hp) (((t0.drop 1).drop 1).drop 1)) (a : Adds7 (tailW Pf)) (x : X)
    (y : Ex.Str)
    (hc : (tailT W' (ksOf P hp) (((t0.drop 1).drop 1).drop 1) nz a).Claims
      (((x, Johnson.L5.Layers.rd gl Pf.D.lT (drawnOf t0)),
        Johnson.L5.Layers.rd gl (Pf.ls + Pf.D.lT) (drawnOf (t0.drop 1))),
        Johnson.L5.Layers.rd gl Pf.gB (drawnOf ((t0.drop 1).drop 1))))
    {Hl : Fork} (lH : Fo.Later G5 Hl) (mask : ℕ → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E) (m : M)
    (hρ : Xp.ρ = gl) (hH : Xp.H = o.H) (nl5 : P.y.xb.nl = 5) (hnb : P.y.h.d / P.y.S2 = Pf.nb)
    (hls : P.y.ls = Pf.ls) (hgB : P.y.lPd - P.y.ls = Pf.gB) (hlt : P.y.h.lt = Pf.D.lT)
    (hy : Pf.msg m Pf.mkE = mask o.sVE) :
    EmbAsks Pf Xp (Hl.worldOf gl mask entry) o
      (Pf.ownF.toOwn.ch.val Ex (x, y)
        (((ownFirstM Pf.ownF.toOwn dT dA dB W').mapsR Ex).view τ)).1 m := by
  rw [k4_valF Ex Pf.ownF.toOwn dT dA dB ok hk hf τ ht nz a x y hc]
  exact embAsks_at_ptsT Pf W' Xp Ld hg h (drop_k0 hg t0) nz a x lH mask entry m hρ hH nl5 hnb hls
    hgB hlt hy

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.drop_k0
#print axioms OnBytes.Road.K4.embAsks_at_pts
#print axioms OnBytes.Road.K4.embAsks_at_ptsT
#print axioms OnBytes.Road.K4.embAsks_at_val
