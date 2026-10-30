-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/Key2.lean: a whole proximity test on a group of oracle messages as one typed list of
bare blocks (Johnson/E/KObj/Blocks.lean): the round before the test, each stage, the last step; and
that every block of the list has the property that a typed list asks, under conditions on public
data. The third chain of a key file is a chain of this form, with four stages.

The blocks are those of Cb/Pv/Bat.lean and Cb/Pv/Tower/ (First, Stage, Base, Test). Each stands
beside the joint of the kept messages, which is carried. The joints of neighbours are the same joint
by type: a list of blocks cannot be written otherwise. The first block is the round before the test
together with two steps without rounds: the rider is set next to the group's word, and the rows are
arranged for the fold. Definitions and proofs; nothing new on a block is proved.
Main names:
  `bkBeside`, `good_beside`: a reduction beside a carried part, as a block; its property from the
    four facts on the reduction.
  `towLK Sj T`, `towLK_each`, `towLK_len`: the stages and the last step of `T : TowR a Fx`
    (Cb/Pv/Tower/Test.lean), a block each, beside Sj; every block has its property under `T.HypK`
    and `T.Reads`; there are `T.nBl` blocks.
  `bkBat`, `bkSet`, `bkArr` with `good_bkBat`, `good_bkSet`, `good_bkArr`; `bkHead`, `good_bkHead`:
    the round before the test while the rider passes; the two steps without rounds; the three as
    one.
  `TestCaller`: who calls a test: the record of the round before the test, the group's shape, the
    data of the stages and the last step, the joint that is carried, a fixed witness for the
    extractor.
  `testLK c`: the list. `TestOK c`: the conditions, a field a clause.
  `testLK_each`: under `TestOK c` every block of the list has its property. `testLK_good`: so the
    list's one block has it. `testLK_len`: 1 + `c.T.nBl` blocks.
  `Key2Form c`: the test has four stages and a last step. `key2_len`: then the list has six blocks.
Limits: at a caller's letters: no value of `TestCaller` is built here, so the conditions are proved
of no value, and nothing says that the sizes of a key file's third chain are a caller's. The joints
at the list's two ends are the test's own; how they meet the joints of a description of a key file's
protocol is not treated. Nothing says that the errors are small. Nothing on an honest prover.

-/
import Johnson.E.KObj.Arrows
import Cb.Pv.Tower.Test
import Cb.Thin.Kinds.Rules

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop Cb IOR Cb.Pv Cb.Pv.Tower

/-! ### a reduction beside a carried part -/

section Beside
variable {Kc Xi Xo Z Wi Wo Wz : Type} {Ei Eo F : ExtSpec} (R : IOR Xi Ei Xo Eo)
  (A : Rels Unit Xi Ei Wi) (B : Rels Unit Xo Eo Wo) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi)
  (ε : Err R.shape) (Sj : Rels Kc Z F Wz)

/-- R beside the carried part, as a block. -/
@[reducible] def bkBeside : BK (jOf (A.beside Sj)) (jOf (B.beside Sj)) where
  R := R.keep Z F
  ext := fun a τ w => (ext (a.1.1, a.2.1) τ w.1, w.2)
  err := ε

theorem good_beside (point : Nonempty R.shape.IsPoint) (isLocal : R.IsLocal)
    (onOut : ∀ a τ b, A.on a → R.red.out a τ = some b → B.on b)
    (know : R.red.Know A.on A.relR B.relR ext ε) : (bkBeside R A B ext ε Sj).Good :=
  BK.good_of _ point (IsLocal.keepE F (isLocal_keepX isLocal Z))
    (fun a τ b hb ha => onOut_beside Kc _ _ _ _ _ _ R _ _ _ A B Sj onOut a τ b ha hb)
    (know_beside Kc _ _ _ _ _ _ R _ _ _ A B ext ε Sj know)

end Beside

theorem LK.len_app : {A B C : JK} → (l : LK A B) → (m : LK B C) → (l.app m).len = l.len + m.len
  | _, _, _, l, .one b => by rw [LK.app_one, LK.len, LK.len]
  | _, _, _, l, .snoc m b => by
      rw [LK.app_snoc, LK.len, LK.len, LK.len_app l m]
      omega

variable {E : Type} [Field E] [Fintype E]

/-! ### the stages and the last step -/

section Tower
variable {Kc Z Wz : Type} {F : ExtSpec} (Sj : Rels Kc Z F Wz)

/-- The stages and the last step, a block each, beside the carried part. -/
noncomputable def towLK : {a : LdJoint E} → {Fx : ExtSpec} → TowR a Fx →
    LK (jOf ((a.rels.keepE Fx).beside Sj)) (jOf (trivRels.beside Sj))
  | _, _, .base a t cov d bad L2 =>
      .one (bkBeside (baseRide a t cov) (baseIn a) trivRels (baseExt a t d) (baseErr a t bad L2) Sj)
  | _, _, @TowR.step _ _ _ _ _ _ _ _ _ _ _
      Y sl e fx Sw Cw Pt _ _ lf lfW d Lst mC mS mW e' L rest =>
      (LK.one (bkBeside (stageRide Y sl e fx Sw Cw Pt lf lfW) (stageInRide Y sl e)
        (stageOut Y sl e Sw Cw e') (stageExtRide Y sl e fx Sw Cw Pt lf lfW d e')
        (stageErrRide Y sl e fx Sw Cw Pt lf lfW Lst mC mS mW L) Sj)).app (towLK rest)

theorem towLK_each : {a : LdJoint E} → {Fx : ExtSpec} → (T : TowR a Fx) → T.HypK → T.Reads →
    (towLK Sj T).Each PG
  | _, _, .base a t cov d bad L2, h, _ =>
      (LK.each_one PG _).2 (good_beside _ _ _ _ _ Sj (base_point a t cov)
        (base_isLocal a t cov h.laws) (base_onOut a t cov) (base_know a t cov d bad L2 h))
  | _, _, @TowR.step _ _ _ _ _ _ _ _ _ _ _
      Y sl e fx Sw Cw Pt _ _ lf lfW d Lst mC mS mW e' L rest, h, hR =>
      (LK.each_app PG _ _).2
        ⟨(LK.each_one PG _).2 (good_beside _ _ _ _ _ Sj
            (stageRide_point Y sl e fx Sw Cw Pt lf lfW)
            (stageRide_local Y sl e fx Sw Cw Pt lf lfW h.1.codes.1.1 h.1.codes.1.2.1
              h.1.codes.1.2.2 hR.1)
            (stageRide_onOut Y sl e fx Sw Cw Pt lf lfW e')
            (stageRide_know Y sl e fx Sw Cw Pt lf lfW d Lst mC mS mW e' L h.1 h.2.1)),
          towLK_each rest h.2.2 hR.2⟩

omit [Field E] [Fintype E] in
/-- a list of one block -/
theorem len_one {A B : JK} (b : BK A B) : (LK.one b).len = 1 := by rw [LK.len]

theorem towLK_len : {a : LdJoint E} → {Fx : ExtSpec} → (T : TowR a Fx) → (towLK Sj T).len = T.nBl
  | _, _, .base .. => by rw [towLK, LK.len, TowR.nBl]
  | _, _, @TowR.step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rest => by
      rw [towLK, TowR.nBl]
      exact (LK.len_app _ _).trans
        ((congrArg₂ (· + ·) (len_one _) (towLK_len rest)).trans (Nat.add_comm 1 _))

end Tower

/-! ### the round before the test, and the two steps without rounds -/

section Head
variable (s : Cb.Pv.Bat.Size E) [Nonempty s.G.P] (Sh : GShape s.G) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((s.S.sub s.kp).Msg × Wp))

/-- The round before the test, while the first fold's mask passes. -/
@[reducible] noncomputable def bkBat :
    BK (jOf ((Cb.Pv.Bat.inJ s A₀).keepE Sh.par.Cw.nat))
      (jOf ((Cb.Pv.Bat.outJ s A₀).keepE Sh.par.Cw.nat)) where
  R := (Cb.Pv.Bat.R s St₀ E₀).keepE Sh.par.Cw.nat
  ext := fun _ _ w => ldBrBack s.G s.kp Wp s.hc w
  err := Cb.Pv.Bat.eps s

omit [Nonempty s.G.P] in
theorem good_bkBat (hZ : s.Z.OK) (hL : s.G.C.ListAt s.G.e s.L) (hF : s.G.Fits) :
    (bkBat s Sh A₀).Good :=
  BK.good_of _ (Cb.Pv.Bat.point s St₀ E₀) ((Cb.Pv.Bat.isLocal s St₀ E₀).keepE Sh.par.Cw.nat)
    (fun a τ x hx ha =>
      onOut_keepE Sh.par.Cw.nat (Cb.Pv.Bat.R s St₀ E₀) (Cb.Pv.Bat.inJ s A₀) (Cb.Pv.Bat.outJ s A₀)
        (Cb.Pv.Bat.onOut s hZ hL hF A₀) a τ x ha hx)
    (know_keepE Sh.par.Cw.nat (Cb.Pv.Bat.R s St₀ E₀) (Cb.Pv.Bat.inJ s A₀) (Cb.Pv.Bat.outJ s A₀)
      (fun _ _ w => ldBrBack s.G s.kp Wp s.hc w) (Cb.Pv.Bat.eps s)
      (Cb.Pv.Bat.hAt s hZ hL hF Kc St₀ Wp E₀ A₀))

/-- The mask is set next to the group's word. -/
@[reducible] noncomputable def bkSet :
    BK (jOf ((Cb.Pv.Bat.outJ s A₀).keepE Sh.par.Cw.nat))
      (jOf ((firstInRide Sh s.Sb s.sl s.Z).beside ((s.S.sub s.kp).over A₀))) where
  R := IOR.pure some (setR s.G.C.ext (CarE s E₀) Sh.par.Cw.nat)
  ext := fun _ _ w => w
  err := ()

theorem good_bkSet : (bkSet s Sh A₀).Good :=
  have g := goodK₀_pure ((Cb.Pv.Bat.outJ s A₀).keepE Sh.par.Cw.nat)
    ((firstInRide Sh s.Sb s.sl s.Z).beside ((s.S.sub s.kp).over A₀)) some
    (setR s.G.C.ext (CarE s E₀) Sh.par.Cw.nat) (fun _ w => w)
    ⟨setR_isLocal _ _ _,
      fun _ _ _ ha e => by
        obtain rfl := Option.some.inj e
        exact ha,
      fun _ _ _ _ _ e hw => by
        obtain rfl := Option.some.inj e
        exact hw⟩
  BK.good_of _ g.point g.isLocal (fun a τ x hx ha => g.onOut a τ x ha hx) g.know

/-- The rows are arranged for the fold, beside the carried part. -/
@[reducible] noncomputable def bkArr :
    BK (jOf ((firstInRide Sh s.Sb s.sl s.Z).beside ((s.S.sub s.kp).over A₀)))
      (jOf ((stageInRide Sh.par (Sh.form s.Sb s.sl s.Z) s.G.e).beside ((s.S.sub s.kp).over A₀))) :=
  bkBeside (arrRide Sh s.Sb s.sl s.Z) (firstInRide Sh s.Sb s.sl s.Z)
    (stageInRide Sh.par (Sh.form s.Sb s.sl s.Z) s.G.e) (fun _ _ w => Sh.rho.dn w) ()
    ((s.S.sub s.kp).over A₀)

theorem good_bkArr (h : Sh.OK) : (bkArr s Sh A₀).Good :=
  good_beside _ _ _ _ _ _ (arrRide_point Sh s.Sb s.sl s.Z) (arrRide_local Sh s.Sb s.sl s.Z h)
    (fun _ _ _ _ _ => trivial) (arrRide_know Sh s.Sb s.sl s.Z h)

/-- The three as one block. w₀: the extractor's value where a verifier has rejected. -/
noncomputable def bkHead (w₀ : s.S.Wit × Wp) :
    BK (jOf ((Cb.Pv.Bat.inJ s A₀).keepE Sh.par.Cw.nat))
      (jOf ((stageInRide Sh.par (Sh.form s.Sb s.sl s.Z) s.G.e).beside ((s.S.sub s.kp).over A₀))) :=
  ((bkBat s Sh A₀).seq (bkSet s Sh A₀) w₀).seq (bkArr s Sh A₀) w₀

theorem good_bkHead (w₀ : s.S.Wit × Wp) (hZ : s.Z.OK) (hL : s.G.C.ListAt s.G.e s.L)
    (hF : s.G.Fits) (h : Sh.OK) : (bkHead s Sh A₀ w₀).Good :=
  BK.good_seq _ _ w₀ (BK.good_seq _ _ w₀ (good_bkBat s Sh A₀ hZ hL hF) (good_bkSet s Sh A₀))
    (good_bkArr s Sh A₀ h)

end Head

/-! ### the list -/

/-- Who calls a test whose first fold's mask was sent earlier. -/
structure TestCaller (E : Type) [Field E] [Fintype E] : Type 1 where
  s : Cb.Pv.Bat.Size E
  [neP : Nonempty s.G.P]
  Sh : GShape s.G
  /-- the stages and the last step -/
  T : TowR (wholeJ Sh.par (Sh.form s.Sb s.sl s.Z) s.G.e) Sh.par.Cw.nat
  Kc : Type
  St₀ : Type
  Wp : Type
  E₀ : ExtSpec
  /-- the joint on the kept messages -/
  A₀ : Rels Kc St₀ E₀ ((s.S.sub s.kp).Msg × Wp)
  /-- the extractor's value where a verifier has rejected -/
  w₀ : s.S.Wit × Wp

attribute [instance] TestCaller.neP

variable (c : TestCaller E)

/-- the joints at the list's two ends -/
@[reducible] noncomputable def TestCaller.jIn : JK :=
  jOf ((Cb.Pv.Bat.inJ c.s c.A₀).keepE c.Sh.par.Cw.nat)
@[reducible] noncomputable def TestCaller.jOut : JK :=
  jOf (trivRels.beside ((c.s.S.sub c.s.kp).over c.A₀))

/-- The list: the round before the test; each stage; the last step. -/
noncomputable def testLK : LK c.jIn c.jOut :=
  (LK.one (bkHead c.s c.Sh c.A₀ c.w₀)).app (towLK ((c.s.S.sub c.s.kp).over c.A₀) c.T)

/-- The conditions, a field a clause, on public data alone. -/
structure TestOK : Prop where
  /-- the coefficients of the round before the test evade zero -/
  z : c.s.Z.OK
  /-- the lists of the group's code at the joint radius are bounded -/
  list : c.s.G.C.ListAt c.s.G.e c.s.L
  /-- the joint radius implies each member's own -/
  fits : c.s.G.Fits
  /-- the laws of the group's shape -/
  shape : c.Sh.OK
  /-- the conditions of all stages and of the last step -/
  tower : c.T.HypK
  /-- each switch's new code's transformation reads what it declares -/
  reads : c.T.Reads

/-- Under the conditions every block of the list has its property. -/
theorem testLK_each (h : TestOK c) : (testLK c).Each PG :=
  (LK.each_app PG _ _).2
    ⟨(LK.each_one PG _).2 (good_bkHead c.s c.Sh c.A₀ c.w₀ h.z h.list h.fits h.shape),
      towLK_each _ c.T h.tower h.reads⟩

/-- So the list's one block has it. -/
theorem testLK_good (h : TestOK c) : ((testLK c).blk c.w₀).Good :=
  LK.good _ c.w₀ (testLK_each c h)

theorem testLK_len : (testLK c).len = 1 + c.T.nBl := by
  rw [testLK]
  refine (LK.len_app _ _).trans ?_
  rw [LK.len]
  exact congrArg (fun n => 1 + n) (towLK_len _ c.T)

/-- The form of the third chain of a key file: four stages and a last step. -/
def Key2Form : Prop := c.T.nBl = 5

theorem key2_len (h : Key2Form c) : (testLK c).len = 6 := by
  rw [testLK_len, h]

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.towLK_each
#print axioms VerifiableInference.OnPublicFiles.good_bkHead
#print axioms VerifiableInference.OnPublicFiles.testLK_each
#print axioms VerifiableInference.OnPublicFiles.testLK_good
