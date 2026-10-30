-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/EmbJoin.lean: the record EmbAsks (Johnson/Road/K4/EmbFirst.lean) at a hearing of the
layers' own rounds in the first group, at the chain's data read off the hearing's tape.

Main names:
  `sh_at`: at any reading, any letters of the chain and any data heard: a scalar that the last
    statement holds as sent in the weights' round is the reading of the word of that number in the
    list heard there.
  `embSh_atF`: at the data read off a tape, the first of these scalars is the reading of the first
    word that the round at the merge's cut sent. From sh_at.
  `embPa_atF`, `embPb_atF`: the two points that the weights' stretch reads off the last statement
    are the second and the third point of the statement in front. By definition.
  `embSlot_ofF`: the clause slot, from emb_slot (Johnson/Road/K4/EmbSlot.lean).
  `nat_rd`, `pt_toArray`: a list of words, read, in the two ways of writing a point.
  `embAsks_of_hear`: EmbAsks, in the world of every ledger later than G5.
Limits. WHAT STAYS A PREMISE of embAsks_of_hear: that the hearing returns in the first group, and
beside it its record LedG (own_ledG, Johnson/Road/K4/OwnLedgersG.lean, has one from a return out of
a ledger with arrays of the right sizes; here it is asked, since the later ledger is named after its
letter G5); that the public record X reads by gl and holds what was heard; five equations on public
numbers (five limbs; the blocks; the bits of a feature in its block; the coordinates of the point on
the blocks; the bits of a position); that the statement in front holds, as its second and third
point, the readings of what the tape's second and third round drew: nobody pays this here; that the
mask entry's name is worth the mask at the slot's number; that the ledger is later. The last
statement is made from the tape under three letters that stay free: the numbering W' of the end
values, nz (none of the seven further challenges reads 0) and a (seven states and seven targets).
One direction: from a return. Nothing on soundness or on hiding.


-/
import Johnson.Road.K4.EmbFirst
import Johnson.Road.K4.EmbHear
import Johnson.Road.K4.EmbSlot
import Johnson.Road.K4.SlotsOfLedFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Reading World Fork Level Tsc)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard)
open OnBytes.Desc.First.P1 (gl Ks NzT Adds7 TailM TailR tailT sentOf drawnOf array_getD_toList)
open OnBytes.Desc.First.K4 (k0 hear engFl)
open Inst.Model (Scl)

/-- A list of words, read as a vector and then as a function on the numbers. -/
theorem nat_rd {n : ℕ} (l : List E) {j : ℕ} (hj : j < n) :
    Blocks.nat (Johnson.L5.Layers.rd gl n l) j = gl.val (l.getD j zeroE) := by
  unfold Blocks.nat
  rw [dif_pos hj]
  rfl

/-- The same list as an array, read as a point of the verifier. -/
theorem pt_toArray (l : List E) (j : ℕ) : pt gl l.toArray j = gl.val (l.getD j zeroE) := by
  unfold pt
  exact congrArg gl.val (array_getD_toList ..)

section Sent

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M X : Type} {T : LayTail K M X}

/-- What the last statement holds as sent in the weights' round, at the number j: the reading of the
word of that number in the list heard there. The number and the list come each with an equation, so
that a caller names them as it writes them. -/
theorem sh_at (D : OnBytes.Tie.Pv.Lay.Eng.TailH ρ T) (x : X) (j : Fin T.nW) {i : ℕ}
    (hj : j.val = i) {l : List E} (hl : D.sW = l) :
    (T.y7 (D.z7 x)).1.2 j = ρ.val (l.getD i zeroE) := by
  subst hj hl
  rfl

end Sent

section Join

variable [scl : Scl] {M X : Type} (Pf : FullFPar Cb.Gl.E M X) {R : TailR} (W' : TailM (tailW Pf) R)

/-- What the last statement holds as sent in the weights' round. -/
theorem embSh_atF (k : Ks) (t : Tape) (nz : NzT (tailW Pf) k t) (a : Adds7 (tailW Pf))
    (x : Pf.ofp.fs.X3) :
    ((tailW Pf).y7 ((tailT W' k t nz a).z7 x)).1.2 (0 : Fin 1) =
      gl.val ((sentOf (k.tcW t)).getD 0 zeroE) :=
  sh_at (tailT W' k t nz a) x (0 : Fin 1) (i := 0) rfl (l := sentOf (k.tcW t)) rfl

/-- The embedding's point inside a block and at the positions, off the last statement. -/
theorem embPa_atF (k : Ks) (t : Tape) (nz : NzT (tailW Pf) k t) (a : Adds7 (tailW Pf))
    (x : Pf.ofp.fs.X3) : (stF Pf ((tailT W' k t nz a).z7 x)).pa = Blocks.nat x.1.2 := rfl

/-- Its point on the blocks. -/
theorem embPb_atF (k : Ks) (t : Tape) (nz : NzT (tailW Pf) k t) (a : Adds7 (tailW Pf))
    (x : Pf.ofp.fs.X3) : (stF Pf ((tailT W' k t nz a).z7 x)).pb = Blocks.nat x.2 := rfl

variable {P : Pub} {hp : HPlan2} {g : ℕ} {fo : OnBytes.Model.Forest.Heard} {o : Own} {F G : Fork}
  {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc} {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork}
  {u5 : Tape}

/-- The clause slot of EmbAsks, where the hearing has returned in the first group. -/
theorem embSlot_ofF (Ld : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (hg : (g == 0) = true) (nz : NzT (tailW Pf) (ksOf P hp) (t0.drop (k0 g)))
    (a : Adds7 (tailW Pf)) (x : Pf.ofp.fs.X3) {Hl : Fork} (lH : Fo.Later G5 Hl)
    (mask : ℕ → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E) (m : M)
    (hy : Pf.msg m Pf.mkE = mask o.sVE) :
    (Hl.worldOf gl mask entry).slot o.sVE =
      ((tailW Pf).y7 ((k4TailG W' P hp g t0 nz a).z7 x)).1.2 (0 : Fin 1) - Pf.msg m Pf.mkE :=
  embSlot_of_led gl mask entry Ld hg lH
    (embSh_atF Pf W' (ksOf P hp) (t0.drop (k0 g)) nz a x) hy

/-- **EmbAsks at a hearing in the first group.** -/
theorem embAsks_of_hear (Xp : Rows.Pub34 Cb.Gl.E)
    (Ld : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (hg : (g == 0) = true) (h : hear engFl P hp g fo F t0 = some (o, G, u))
    (nz : NzT (tailW Pf) (ksOf P hp) (t0.drop (k0 g))) (a : Adds7 (tailW Pf))
    (x : Pf.ofp.fs.X3) {Hl : Fork} (lH : Fo.Later G5 Hl) (mask : ℕ → Cb.Gl.E)
    (entry : ℕ → ℕ → ℕ → Cb.Gl.E) (m : M) (hρ : Xp.ρ = gl) (hH : Xp.H = o.H)
    (nl5 : P.y.xb.nl = 5) (hnb : P.y.h.d / P.y.S2 = Pf.nb) (hls : P.y.ls = Pf.ls)
    (hgB : P.y.lPd - P.y.ls = Pf.gB) (hlt : P.y.h.lt = Pf.D.lT)
    (hxa : x.1.2 = Johnson.L5.Layers.rd gl (Pf.ls + Pf.D.lT) (drawnOf (t0.drop 1)))
    (hxb : x.2 = Johnson.L5.Layers.rd gl Pf.gB (drawnOf ((t0.drop 1).drop 1)))
    (hy : Pf.msg m Pf.mkE = mask o.sVE) :
    EmbAsks Pf Xp (Hl.worldOf gl mask entry) o ((k4TailG W' P hp g t0 nz a).z7 x) m := by
  obtain ⟨e0, ey, aZ, -, aT, -⟩ := emb_hear hg h
  exact
    { g0 := e0
      nl5 := by rw [ey]; exact nl5
      nb := by rw [ey]; exact hnb
      ls := by rw [ey]; exact hls
      tk := (emb_hear_sizes hg h).2.trans hgB
      ze := by rw [hH, (emb_hear_sizes hg h).1, hls, hlt]
      pa1 := fun j hj => by
        have q : j < Pf.ls + Pf.D.lT := by omega
        rw [hρ, hH, aZ, pt_toArray, embPa_atF, hxa, nat_rd _ q]
      pa2 := fun j hj => by
        have q : Pf.ls + j < Pf.ls + Pf.D.lT := by omega
        rw [hρ, hH, aZ, pt_toArray, embPa_atF, hxa, nat_rd _ q]
      pb := fun j hj => by
        rw [hρ, aT, pt_toArray, embPb_atF, hxb, nat_rd _ hj]
      slot := embSlot_ofF Pf W' Ld hg nz a x lH mask entry m hy }

end Join

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.sh_at
#print axioms OnBytes.Road.K4.embSh_atF
#print axioms OnBytes.Road.K4.embPa_atF
#print axioms OnBytes.Road.K4.embPb_atF
#print axioms OnBytes.Road.K4.embSlot_ofF
#print axioms OnBytes.Road.K4.embAsks_of_hear
