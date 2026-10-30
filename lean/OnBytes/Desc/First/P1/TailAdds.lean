-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/TailAdds.lean: THE SEVEN STATES OF THE DATA THAT ARE READ OFF A TAPE, CHOSEN
ONE AFTER THE OTHER, so that of `TailH.Claims` (OnBytes/Tie/Pv/Lay/OwnTieL.lean) only the
seven equations on the claimed sums are left. Definitions and short statements. Bookkeeping.

`tailT W k t nz a` (OnBytes/Desc/First/P1/TailTape.lean) reads all words of the chain's data off a
tape t; the seven states and the seven targets a are free. A stage's claim asks
`S.cl x rd = (the reading of the target, the state)`, at the statement x that the stage finds, and
x holds the outputs of the stages in front, which hold their states. So the states are fixed from
the front on: each is the second component of its stage's `cl`.

NO NEW IDEA. OnBytes/Tie/Pv/Lay/HearCanon.lean splits `TailH.Claims` of any data into the
states' half and the targets' half (`StIs`, `TgIs`, `claims_of`) and makes this very choice of the
states for the data of verify-on-bytes's routine (`c1` … `c7`, `tailC_st`). This file is that
construction at `tailT`.

  `Tg7`: seven targets.
  `aY1` `aS1` `aD1` `aZ1` · `aY2` `aS2` `aD2` `aZ2` · `aS3` `aD3` `aZ3` · `aY4` `aS4` `aD4` `aZ4` ·
  `aS5` `aD5` `aZ5` · `aY6` `aS6` `aD6` `aZ6` · `aY7` `aS7`: the statement that a stage finds (the
    third finds `aZ2`, the fifth `aZ4`), its state, its data and the statement behind it, written
    out in the words of the tape.
  `addsOf`: the seven states so chosen, with the seven targets given.
  `tz1` … `tz6`: the statements behind the first six stages, as `TailH` names them at these data,
    are those written out. `ty7`, `td7`: what the seventh finds, and its data. `stg_claim`: a
    stage's claim from its two components. `clm1` … `clm7`: the claims one by one.
  `claims_of_firsts`: if each stage's claimed sum, at the statement written out, is the reading of
    its target, then `(tailT W k t nz (addsOf …)).Claims x`.
  `aZ4_vals`: the end values in the statement behind the fourth sumcheck are the readings of the
    words that its values' round sent, by the numbering: `sum_vals`, OnBytes/Tie/Pv/Lay/SumTie.lean.

Limits. No chain's value and no text is named: T, the tape and the targets are letters. The seven
equations on the claimed sums are premises. `NzT T k t` (the readings of seven challenges on the
tape are not 0) stands in the type of `tailT` and so in every statement from `aD1` on. Nothing on
soundness.
-/
import OnBytes.Desc.First.P1.TailTape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open Iop Cb TWhole Cb.Pv.Lay Cb.Pv.Att Johnson.L5.Layers
open OnBytes.K.Kc OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Tie.Pv.Lay.Eng (StgH TailH)

local notation "z0" => OnBytes.zeroE

/-- Seven targets. -/
structure Tg7 where
  t1 : OnBytes.E
  t2 : OnBytes.E
  t3 : OnBytes.E
  t4 : OnBytes.E
  t5 : OnBytes.E
  t6 : OnBytes.E
  t7 : OnBytes.E

noncomputable section

variable {M X : Type} {T : LayTail GE M X} {R : TailR} (W : TailM T R) (k : Ks) (t : Tape)
  (nz : NzT T k t) (x : X) (g : Tg7)

/-! ### The stages, from the front on -/

/-- The statement that the first sumcheck finds. -/
def aY1 (T : LayTail GE M X) (t : Tape) (x : X) :
    ((X × (Fin T.nL → GE)) × GE) × (Fin T.gN → GE) :=
  (((x, rd gl T.nL (sentOf t)), gl.val (tapeEps t)), rd gl T.gN (drawnOf (t.drop 1)))

def aS1 (T : LayTail GE M X) (k : Ks) (t : Tape) (x : X) : T.s1.L.St :=
  (T.s1.cl (aY1 T t x) (rd gl T.s1.n (sentOf (k.tc1 t)))).2

def aD1 : StgH gl T.s1 := stgT W.w1.num k.k1 (k.tc1 t) nz.b1 (aS1 T k t x) g.t1

def aZ1 : T.s1.Nx := (aD1 W k t nz x g).nx (aY1 T t x)

def aY2 : ((T.s1.Nx × GE) × (Fin T.nP → GE)) × GE :=
  (((aZ1 W k t nz x g, gl.val (tapeEps ((k.tc1 t).drop (k.k1 + 3)))),
    rd gl T.nP (sentOf (k.tcP t))), gl.val (tapeEps (k.tcP t)))

def aS2 : T.s2.L.St :=
  (T.s2.cl (aY2 W k t nz x g) (rd gl T.s2.n (sentOf ((k.tcP t).drop 1)))).2

def aD2 : StgH gl T.s2 :=
  stgT W.w2.num k.k2 ((k.tcP t).drop 1) nz.b2 (aS2 W k t nz x g) g.t2

def aZ2 : T.s2.Nx := (aD2 W k t nz x g).nx (aY2 W k t nz x g)

def aS3 : T.s3.L.St :=
  (T.s3.cl (aZ2 W k t nz x g)
    (rd gl T.s3.n (sentOf (((k.tcP t).drop 1).drop (k.k2 + 3))))).2

def aD3 : StgH gl T.s3 :=
  stgT W.w3.num k.k3 (((k.tcP t).drop 1).drop (k.k2 + 3)) nz.b3 (aS3 W k t nz x g) g.t3

def aZ3 : T.s3.Nx := (aD3 W k t nz x g).nx (aZ2 W k t nz x g)

def aY4 : T.s3.Nx × GE := (aZ3 W k t nz x g, gl.val (tapeEps (k.tc4 t)))

def aS4 : T.s4.L.St :=
  (T.s4.cl (aY4 W k t nz x g) (rd gl T.s4.n (sentOf ((k.tc4 t).drop 1)))).2

def aD4 : StgH gl T.s4 :=
  stgT W.w4.num k.k4 ((k.tc4 t).drop 1) nz.b4 (aS4 W k t nz x g) g.t4

def aZ4 : T.s4.Nx := (aD4 W k t nz x g).nx (aY4 W k t nz x g)

def aS5 : T.s5.L.St := (T.s5.cl (aZ4 W k t nz x g) (rd gl T.s5.n (sentOf (k.tc5 t)))).2

def aD5 : StgH gl T.s5 := stgT W.w5.num k.k5 (k.tc5 t) nz.b5 (aS5 W k t nz x g) g.t5

def aZ5 : T.s5.Nx := (aD5 W k t nz x g).nx (aZ4 W k t nz x g)

def aY6 : (T.s5.Nx × GE) × (Fin T.gR → GE) :=
  ((aZ5 W k t nz x g, gl.val (tapeEps ((k.tc5 t).drop (k.k5 + 3)))),
    rd gl T.gR (drawnOf (((k.tc5 t).drop (k.k5 + 3)).drop 1)))

def aS6 : T.s6.L.St := (T.s6.cl (aY6 W k t nz x g) (rd gl T.s6.n (sentOf (k.tc6 t)))).2

def aD6 : StgH gl T.s6 := stgT W.w6.num k.k6 (k.tc6 t) nz.b6 (aS6 W k t nz x g) g.t6

def aZ6 : T.s6.Nx := (aD6 W k t nz x g).nx (aY6 W k t nz x g)

def aY7 : ((T.s6.Nx × GE) × (Fin T.nW → GE)) × GE :=
  (((aZ6 W k t nz x g, gl.val (tapeEps ((k.tc6 t).drop (k.k6 + 3)))),
    rd gl T.nW (sentOf (k.tcW t))), gl.val (tapeEps (k.tcW t)))

def aS7 : T.s7.L.St :=
  (T.s7.cl (aY7 W k t nz x g) (rd gl T.s7.n (sentOf ((k.tcW t).drop 1)))).2

/-- **The seven states, chosen from the front on, with the seven targets given.** -/
def addsOf : Adds7 T :=
  ⟨aS1 T k t x, aS2 W k t nz x g, aS3 W k t nz x g, aS4 W k t nz x g, aS5 W k t nz x g,
    aS6 W k t nz x g, aS7 W k t nz x g, g.t1, g.t2, g.t3, g.t4, g.t5, g.t6, g.t7⟩

/-! ### The statements behind the stages are those written out -/

theorem tz1 : (tailT W k t nz (addsOf W k t nz x g)).z1 x = aZ1 W k t nz x g := rfl

theorem tz2 : (tailT W k t nz (addsOf W k t nz x g)).z2 x = aZ2 W k t nz x g := by
  unfold TailH.z2 TailH.y2
  rw [tz1]
  rfl

theorem tz3 : (tailT W k t nz (addsOf W k t nz x g)).z3 x = aZ3 W k t nz x g := by
  unfold TailH.z3
  rw [tz2]
  rfl

theorem tz4 : (tailT W k t nz (addsOf W k t nz x g)).z4 x = aZ4 W k t nz x g := by
  unfold TailH.z4 TailH.y4
  rw [tz3]
  rfl

theorem tz5 : (tailT W k t nz (addsOf W k t nz x g)).z5 x = aZ5 W k t nz x g := by
  unfold TailH.z5
  rw [tz4]
  rfl

theorem tz6 : (tailT W k t nz (addsOf W k t nz x g)).z6 x = aZ6 W k t nz x g := by
  unfold TailH.z6 TailH.y6
  rw [tz5]
  rfl

/-! ### The claims, one by one -/

theorem clm1 (h1 : (T.s1.cl (aY1 T t x) (rd gl T.s1.n (sentOf (k.tc1 t)))).1 = gl.val g.t1) :
    (tailT W k t nz (addsOf W k t nz x g)).d1.Claim
      ((tailT W k t nz (addsOf W k t nz x g)).y1 x) := by
  show T.s1.cl (aY1 T t x) (rd gl T.s1.n (sentOf (k.tc1 t))) = (gl.val g.t1, aS1 T k t x)
  exact Prod.ext h1 rfl

theorem clm2
    (h2 : (T.s2.cl (aY2 W k t nz x g) (rd gl T.s2.n (sentOf ((k.tcP t).drop 1)))).1 =
      gl.val g.t2) :
    (tailT W k t nz (addsOf W k t nz x g)).d2.Claim
      ((tailT W k t nz (addsOf W k t nz x g)).y2 x) := by
  unfold TailH.y2
  rw [tz1]
  show T.s2.cl (aY2 W k t nz x g) (rd gl T.s2.n (sentOf ((k.tcP t).drop 1))) =
    (gl.val g.t2, aS2 W k t nz x g)
  exact Prod.ext h2 rfl

theorem clm3
    (h3 : (T.s3.cl (aZ2 W k t nz x g)
      (rd gl T.s3.n (sentOf (((k.tcP t).drop 1).drop (k.k2 + 3))))).1 = gl.val g.t3) :
    (tailT W k t nz (addsOf W k t nz x g)).d3.Claim
      ((tailT W k t nz (addsOf W k t nz x g)).z2 x) := by
  rw [tz2]
  show T.s3.cl (aZ2 W k t nz x g)
    (rd gl T.s3.n (sentOf (((k.tcP t).drop 1).drop (k.k2 + 3)))) =
    (gl.val g.t3, aS3 W k t nz x g)
  exact Prod.ext h3 rfl

theorem clm4
    (h4 : (T.s4.cl (aY4 W k t nz x g) (rd gl T.s4.n (sentOf ((k.tc4 t).drop 1)))).1 =
      gl.val g.t4) :
    (tailT W k t nz (addsOf W k t nz x g)).d4.Claim
      ((tailT W k t nz (addsOf W k t nz x g)).y4 x) := by
  unfold TailH.y4
  rw [tz3]
  show T.s4.cl (aY4 W k t nz x g) (rd gl T.s4.n (sentOf ((k.tc4 t).drop 1))) =
    (gl.val g.t4, aS4 W k t nz x g)
  exact Prod.ext h4 rfl

theorem clm5
    (h5 : (T.s5.cl (aZ4 W k t nz x g) (rd gl T.s5.n (sentOf (k.tc5 t)))).1 = gl.val g.t5) :
    (tailT W k t nz (addsOf W k t nz x g)).d5.Claim
      ((tailT W k t nz (addsOf W k t nz x g)).z4 x) := by
  rw [tz4]
  show T.s5.cl (aZ4 W k t nz x g) (rd gl T.s5.n (sentOf (k.tc5 t))) =
    (gl.val g.t5, aS5 W k t nz x g)
  exact Prod.ext h5 rfl

theorem clm6
    (h6 : (T.s6.cl (aY6 W k t nz x g) (rd gl T.s6.n (sentOf (k.tc6 t)))).1 = gl.val g.t6) :
    (tailT W k t nz (addsOf W k t nz x g)).d6.Claim
      ((tailT W k t nz (addsOf W k t nz x g)).y6 x) := by
  unfold TailH.y6
  rw [tz5]
  show T.s6.cl (aY6 W k t nz x g) (rd gl T.s6.n (sentOf (k.tc6 t))) =
    (gl.val g.t6, aS6 W k t nz x g)
  exact Prod.ext h6 rfl

/-- A stage's claim from its two components. -/
theorem stg_claim {X' : Type} {S : Stg GE M X'} (D : StgH gl S) (y : X')
    (h1 : (S.cl y D.rd).1 = gl.val D.t) (h2 : (S.cl y D.rd).2 = D.st) : D.Claim y :=
  Prod.ext h1 h2

theorem ty7 : (tailT W k t nz (addsOf W k t nz x g)).y7 x = aY7 W k t nz x g := by
  unfold TailH.y7 aY7
  rw [tz6]
  rfl

theorem td7 : (tailT W k t nz (addsOf W k t nz x g)).d7 =
    stgT W.w7.num k.k7 ((k.tcW t).drop 1) nz.b7 (aS7 W k t nz x g) g.t7 := rfl

/- `aZ2` holds `aZ1` twice (in `aY2`, and in `aS2` inside `aD2`), and so on: unfolded, the terms
double at each stage. Whether so many heartbeats are needed has not been tried. -/
set_option maxHeartbeats 1600000 in
theorem clm7
    (h7 : (T.s7.cl (aY7 W k t nz x g) (rd gl T.s7.n (sentOf ((k.tcW t).drop 1)))).1 =
      gl.val g.t7) :
    (tailT W k t nz (addsOf W k t nz x g)).d7.Claim
      ((tailT W k t nz (addsOf W k t nz x g)).y7 x) := by
  rw [ty7, td7]
  exact stg_claim _ _ h7 rfl

/-- **Of the seven claims only the equations on the claimed sums are left.** -/
theorem claims_of_firsts
    (h1 : (T.s1.cl (aY1 T t x) (rd gl T.s1.n (sentOf (k.tc1 t)))).1 = gl.val g.t1)
    (h2 : (T.s2.cl (aY2 W k t nz x g) (rd gl T.s2.n (sentOf ((k.tcP t).drop 1)))).1 =
      gl.val g.t2)
    (h3 : (T.s3.cl (aZ2 W k t nz x g)
      (rd gl T.s3.n (sentOf (((k.tcP t).drop 1).drop (k.k2 + 3))))).1 = gl.val g.t3)
    (h4 : (T.s4.cl (aY4 W k t nz x g) (rd gl T.s4.n (sentOf ((k.tc4 t).drop 1)))).1 =
      gl.val g.t4)
    (h5 : (T.s5.cl (aZ4 W k t nz x g) (rd gl T.s5.n (sentOf (k.tc5 t)))).1 = gl.val g.t5)
    (h6 : (T.s6.cl (aY6 W k t nz x g) (rd gl T.s6.n (sentOf (k.tc6 t)))).1 = gl.val g.t6)
    (h7 : (T.s7.cl (aY7 W k t nz x g) (rd gl T.s7.n (sentOf ((k.tcW t).drop 1)))).1 =
      gl.val g.t7) :
    (tailT W k t nz (addsOf W k t nz x g)).Claims x :=
  ⟨clm1 W k t nz x g h1, clm2 W k t nz x g h2, clm3 W k t nz x g h3, clm4 W k t nz x g h4,
    clm5 W k t nz x g h5, clm6 W k t nz x g h6, clm7 W k t nz x g h7⟩

/-- The end values in the statement behind the fourth sumcheck. -/
theorem aZ4_vals (a : T.s4.L.S.A) :
    (aZ4 W k t nz x g).2.vals a =
      gl.val ((sentOf (((k.tc4 t).drop 1).drop (k.k4 + 2))).getD (W.w4.num a) z0) :=
  congrFun (OnBytes.Tie.Pv.Lay.Eng.sum_vals gl T.s4.L T.s4.F _ _ _ _ _ _ _ _ _) a

end

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.claims_of_firsts
#print axioms OnBytes.Desc.First.P1.aZ4_vals
