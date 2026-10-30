-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/ClaimsFree.lean: THAT THERE ARE SEVEN STATES AND SEVEN TARGETS WITH WHICH THE
DATA READ OFF A TAPE MEET `TailH.Claims` IS FREE: it holds at every chain, every tape and
every statement in front, with no premise. Definitions, small statements, one theorem.

WHY IT IS FREE. A stage's claim (`StgH.Claim`, OnBytes/Tie/Pv/Lay/OwnTieL.lean) asks
`S.cl x rd = (the reading of the target, the state)`. In `tailT W k t nz a`
(OnBytes/Desc/First/P1/TailTape.lean) the seven states and the seven targets a are letters. The
states can be chosen as the claims name them (OnBytes/Desc/First/P1/TailAdds.lean). The reading in
the library's extension field is onto (`readE_writeE`, OnBytes/Slice/KeyOfRec.lean): so
each target can be chosen as an element that reads as the claimed sum, from the front on, since what
a stage finds hangs on the targets in front of it alone.

WHAT FOLLOWS. "There are additions with `Claims`" says NOTHING of a program's records. What says
something is `Claims` at targets that ARE the records' (`claims_of_led` with `TgRec`,
Johnson/Road/K4/ClaimsHeard.lean). The free statement does no harm where only the chain's value is
wanted: `Claims` fixes each state and the reading of each target, so, by reading (no lemma here
says it), what is concluded from it of the chain's value does not hang on the choice.

  `gl_write`: what is written reads back, in the words of `gl`.
  `aZ1_c` … `aY7_c`: what a stage finds, and its state, are the same at two lists of targets that
    agree in front of the stage.
  `fT1`, `fG1`, … `fT7`, `fG7`: the targets so chosen.
  `claims_exist`: `∃ a, (tailT W k t nz a).Claims x`.

Limits. `NzT T k t` (the readings of seven challenges on the tape are not 0) stands in the type of
`tailT`. Nothing on soundness.
-/
import OnBytes.Desc.First.P1.TailAdds
import OnBytes.Slice.KeyOfRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open Iop Cb TWhole Cb.Pv.Lay Cb.Pv.Att Johnson.L5.Layers
open OnBytes.K.Kc OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Tie.Pv.Lay.Eng (StgH TailH)

local notation "z0" => OnBytes.zeroE

/-- What is written reads back. -/
theorem gl_write (y : GE) : gl.val (writeE y) = y := readE_writeE y

noncomputable section

variable {M X : Type} {T : LayTail GE M X} {R : TailR} (W : TailM T R) (k : Ks) (t : Tape)
  (nz : NzT T k t) (x : X)

/-! ### What a stage finds hangs on the targets in front alone -/

section Congr
variable {g g' : Tg7}

theorem aZ1_c (h1 : g.t1 = g'.t1) : aZ1 W k t nz x g = aZ1 W k t nz x g' := by
  unfold aZ1 aD1
  rw [h1]

theorem aY2_c (h1 : g.t1 = g'.t1) : aY2 W k t nz x g = aY2 W k t nz x g' := by
  unfold aY2
  rw [aZ1_c W k t nz x h1]

theorem aS2_c (h1 : g.t1 = g'.t1) : aS2 W k t nz x g = aS2 W k t nz x g' := by
  unfold aS2
  rw [aY2_c W k t nz x h1]

theorem aZ2_c (h1 : g.t1 = g'.t1) (h2 : g.t2 = g'.t2) : aZ2 W k t nz x g = aZ2 W k t nz x g' := by
  unfold aZ2 aD2
  rw [aY2_c W k t nz x h1, aS2_c W k t nz x h1, h2]

theorem aS3_c (h1 : g.t1 = g'.t1) (h2 : g.t2 = g'.t2) : aS3 W k t nz x g = aS3 W k t nz x g' := by
  unfold aS3
  rw [aZ2_c W k t nz x h1 h2]

theorem aZ3_c (h1 : g.t1 = g'.t1) (h2 : g.t2 = g'.t2) (h3 : g.t3 = g'.t3) :
    aZ3 W k t nz x g = aZ3 W k t nz x g' := by
  unfold aZ3 aD3
  rw [aZ2_c W k t nz x h1 h2, aS3_c W k t nz x h1 h2, h3]

theorem aY4_c (h1 : g.t1 = g'.t1) (h2 : g.t2 = g'.t2) (h3 : g.t3 = g'.t3) :
    aY4 W k t nz x g = aY4 W k t nz x g' := by
  unfold aY4
  rw [aZ3_c W k t nz x h1 h2 h3]

theorem aS4_c (h1 : g.t1 = g'.t1) (h2 : g.t2 = g'.t2) (h3 : g.t3 = g'.t3) :
    aS4 W k t nz x g = aS4 W k t nz x g' := by
  unfold aS4
  rw [aY4_c W k t nz x h1 h2 h3]

theorem aZ4_c (h1 : g.t1 = g'.t1) (h2 : g.t2 = g'.t2) (h3 : g.t3 = g'.t3)
    (h4 : g.t4 = g'.t4) : aZ4 W k t nz x g = aZ4 W k t nz x g' := by
  unfold aZ4 aD4
  rw [aY4_c W k t nz x h1 h2 h3, aS4_c W k t nz x h1 h2 h3, h4]

theorem aS5_c (h1 : g.t1 = g'.t1) (h2 : g.t2 = g'.t2) (h3 : g.t3 = g'.t3)
    (h4 : g.t4 = g'.t4) : aS5 W k t nz x g = aS5 W k t nz x g' := by
  unfold aS5
  rw [aZ4_c W k t nz x h1 h2 h3 h4]

theorem aZ5_c (h1 : g.t1 = g'.t1) (h2 : g.t2 = g'.t2) (h3 : g.t3 = g'.t3)
    (h4 : g.t4 = g'.t4) (h5 : g.t5 = g'.t5) : aZ5 W k t nz x g = aZ5 W k t nz x g' := by
  unfold aZ5 aD5
  rw [aZ4_c W k t nz x h1 h2 h3 h4, aS5_c W k t nz x h1 h2 h3 h4, h5]

theorem aY6_c (h1 : g.t1 = g'.t1) (h2 : g.t2 = g'.t2) (h3 : g.t3 = g'.t3)
    (h4 : g.t4 = g'.t4) (h5 : g.t5 = g'.t5) : aY6 W k t nz x g = aY6 W k t nz x g' := by
  unfold aY6
  rw [aZ5_c W k t nz x h1 h2 h3 h4 h5]

theorem aS6_c (h1 : g.t1 = g'.t1) (h2 : g.t2 = g'.t2) (h3 : g.t3 = g'.t3)
    (h4 : g.t4 = g'.t4) (h5 : g.t5 = g'.t5) : aS6 W k t nz x g = aS6 W k t nz x g' := by
  unfold aS6
  rw [aY6_c W k t nz x h1 h2 h3 h4 h5]

theorem aZ6_c (h1 : g.t1 = g'.t1) (h2 : g.t2 = g'.t2) (h3 : g.t3 = g'.t3)
    (h4 : g.t4 = g'.t4) (h5 : g.t5 = g'.t5) (h6 : g.t6 = g'.t6) :
    aZ6 W k t nz x g = aZ6 W k t nz x g' := by
  unfold aZ6 aD6
  rw [aY6_c W k t nz x h1 h2 h3 h4 h5, aS6_c W k t nz x h1 h2 h3 h4 h5, h6]

theorem aY7_c (h1 : g.t1 = g'.t1) (h2 : g.t2 = g'.t2) (h3 : g.t3 = g'.t3)
    (h4 : g.t4 = g'.t4) (h5 : g.t5 = g'.t5) (h6 : g.t6 = g'.t6) :
    aY7 W k t nz x g = aY7 W k t nz x g' := by
  unfold aY7
  rw [aZ6_c W k t nz x h1 h2 h3 h4 h5 h6]

end Congr

/-! ### The targets, from the front on -/

/-- The first target: an element that reads as the first claimed sum. -/
def fT1 (T : LayTail GE M X) (k : Ks) (t : Tape) (x : X) : OnBytes.E :=
  writeE (T.s1.cl (aY1 T t x) (rd gl T.s1.n (sentOf (k.tc1 t)))).1

def fG1 (T : LayTail GE M X) (k : Ks) (t : Tape) (x : X) : Tg7 :=
  ⟨fT1 T k t x, z0, z0, z0, z0, z0, z0⟩

def fT2 : OnBytes.E :=
  writeE (T.s2.cl (aY2 W k t nz x (fG1 T k t x))
    (rd gl T.s2.n (sentOf ((k.tcP t).drop 1)))).1

def fG2 : Tg7 :=
  ⟨fT1 T k t x, fT2 W k t nz x, z0, z0,
    z0, z0, z0⟩

def fT3 : OnBytes.E :=
  writeE (T.s3.cl (aZ2 W k t nz x (fG2 W k t nz x))
    (rd gl T.s3.n (sentOf (((k.tcP t).drop 1).drop (k.k2 + 3))))).1

def fG3 : Tg7 :=
  ⟨fT1 T k t x, fT2 W k t nz x, fT3 W k t nz x, z0,
    z0, z0, z0⟩

def fT4 : OnBytes.E :=
  writeE (T.s4.cl (aY4 W k t nz x (fG3 W k t nz x))
    (rd gl T.s4.n (sentOf ((k.tc4 t).drop 1)))).1

def fG4 : Tg7 :=
  ⟨fT1 T k t x, fT2 W k t nz x, fT3 W k t nz x, fT4 W k t nz x,
    z0, z0, z0⟩

def fT5 : OnBytes.E :=
  writeE (T.s5.cl (aZ4 W k t nz x (fG4 W k t nz x))
    (rd gl T.s5.n (sentOf (k.tc5 t)))).1

def fG5 : Tg7 :=
  ⟨fT1 T k t x, fT2 W k t nz x, fT3 W k t nz x, fT4 W k t nz x,
    fT5 W k t nz x, z0, z0⟩

def fT6 : OnBytes.E :=
  writeE (T.s6.cl (aY6 W k t nz x (fG5 W k t nz x))
    (rd gl T.s6.n (sentOf (k.tc6 t)))).1

def fG6 : Tg7 :=
  ⟨fT1 T k t x, fT2 W k t nz x, fT3 W k t nz x, fT4 W k t nz x,
    fT5 W k t nz x, fT6 W k t nz x, z0⟩

def fT7 : OnBytes.E :=
  writeE (T.s7.cl (aY7 W k t nz x (fG6 W k t nz x))
    (rd gl T.s7.n (sentOf ((k.tcW t).drop 1)))).1

def fG7 : Tg7 :=
  ⟨fT1 T k t x, fT2 W k t nz x, fT3 W k t nz x, fT4 W k t nz x,
    fT5 W k t nz x, fT6 W k t nz x, fT7 W k t nz x⟩

/-! ### The free statement -/

/-- **There are additions with which the data meet the claims: at every chain, tape and statement;
no premise.** It says nothing of a program's records: see the head. -/
theorem claims_exist : ∃ a : Adds7 T, (tailT W k t nz a).Claims x := by
  refine ⟨addsOf W k t nz x (fG7 W k t nz x),
    claims_of_firsts W k t nz x (fG7 W k t nz x) ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · exact (gl_write _).symm
  · rw [aY2_c W k t nz x (g := fG7 W k t nz x) (g' := fG1 T k t x) rfl]
    exact (gl_write _).symm
  · rw [aZ2_c W k t nz x (g := fG7 W k t nz x) (g' := fG2 W k t nz x) rfl rfl]
    exact (gl_write _).symm
  · rw [aY4_c W k t nz x (g := fG7 W k t nz x) (g' := fG3 W k t nz x) rfl rfl rfl]
    exact (gl_write _).symm
  · rw [aZ4_c W k t nz x (g := fG7 W k t nz x) (g' := fG4 W k t nz x) rfl rfl rfl rfl]
    exact (gl_write _).symm
  · rw [aY6_c W k t nz x (g := fG7 W k t nz x) (g' := fG5 W k t nz x) rfl rfl rfl rfl rfl]
    exact (gl_write _).symm
  · rw [aY7_c W k t nz x (g := fG7 W k t nz x) (g' := fG6 W k t nz x) rfl rfl rfl rfl rfl rfl]
    exact (gl_write _).symm

end

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.claims_exist
