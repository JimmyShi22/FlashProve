-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tower/Test.lean: a whole proximity test as one reduction, general in the number of its stages:
stages in a row, then the last step; on a group of oracle messages with the arrangement before them;
and with the round before the test, beside what is carried. For each the statement that it is
round-by-round knowledge sound, proved under conditions on codes and numbers that no file here shows
of any setting.

The library has its tower of stages as an inductive family over the joint at which a tower begins
(`LdTowC`, Cb/Obj/LdObjectTower.lean): a step's remainder begins at the joint at which the step's
switch ends, by type. This file has the same family for the blocks of Cb/Pv/Tower/Stage.lean and
Cb/Pv/Tower/Base.lean, in which the mask of a fold, and the masking word of the last step, went out
inside an earlier prover's message. So the family has a second index: the further oracle that stands
in the input. A step's remainder begins at the joint at which the step's switch ends, with the
switch's rider in its input. Definitions and proofs.
Main names:
  `EndR a Fx`, `EndR.Know`: a reduction from the joint a, with a further oracle Fx in its input of
    which nothing is asked, to the trivial statement, with extractor and errors; the statement that
    it is knowledge sound. `EndO a`, `EndO.Know`: the same without a further oracle.
  `TowR a Fx`: the data of a test: `base`: the last step, its masking word in the input; `step`: a
    stage whose fold's mask is in the input (finitely many leaves), then a remainder.
  `TowR.toEnd`: the reduction. `TowR.HypK`: the conditions of all its blocks. `TowR.know`: under
    them it is knowledge sound.
  `TowR.Reads`: the further condition for locality. `TowR.nBl`: the number of blocks.
  `TowR.toEnd_point`, `TowR.toEnd_local` (under `HypK` and `Reads`); `testRide_point`,
    `testRide_local`.
  `TowR.len`, `TowR.errs`, `TowR.vals` with `toEnd_len`, `toEnd_errs`, `toEnd_vals`: the number of
    rounds (k + 3 for each stage, then 2), the errors and the numbers of values of the verifier's
    messages, as lists, stage by stage.
  `ownStep`, `ownStep_know`: a test whose first fold sends its own mask.
  `testRide`, `testOwn` with `_know`: a test on a group: the arrangement (Cb/Pv/Tower/First.lean),
    then a test that begins at the fold's input code.
  `runRide`, `runOwn` with `RunRideKnow`, `RunOwnKnow`, `_know`, `_rounds`: the round before the
    test (Cb/Pv/Bat.lean), then the test beside the carried part, to the joint of the kept messages.
Limits: those of the files named. A stage whose switch bears no rider is not laid. That the joints
of neighbouring stages meet is asked by type: a value of `TowR` with two stages exists only where
the switch's new code is the next fold's input code (`swInto`, `cs_stage_seam`,
Cb/Pv/Tower/Stage.lean). No value is built here. Point oracles and locality of `runRide` and
`runOwn` are not shown; those of `ownStep` and `testOwn` are in Cb/Pv/Tower/RunsOwn.lean. Nothing on
an honest prover.

-/
import Cb.Pv.Tower.First
import Cb.Pv.Tower.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tower
open Iop Prob Hiop IOR

variable {E : Type} [Field E] [Fintype E]

/-! ## Reductions to the trivial statement -/

/-- A reduction from the joint a to the trivial statement whose input holds a further oracle. -/
structure EndR (a : LdJoint E) (Fx : ExtSpec) where
  R : IOR a.X (a.C.ext.prod Fx) Unit extNone
  ext : a.X × (a.C.ext.prod Fx).Str → Tr R.shape → Unit → a.W
  e : Err R.shape

/-- The statement that it is knowledge sound: nothing is asked of the further oracle. -/
def EndR.Know {a : LdJoint E} {Fx : ExtSpec} (Z : EndR a Fx) : Prop :=
  Z.R.red.Know (a.rels.keepE Fx).on (a.rels.keepE Fx).relR trivRels.relR Z.ext Z.e

/-- A reduction from the joint a to the trivial statement. -/
structure EndO (a : LdJoint E) where
  R : IOR a.X a.C.ext Unit extNone
  ext : a.X × a.C.ext.Str → Tr R.shape → Unit → a.W
  e : Err R.shape

/-- The statement that it is knowledge sound. -/
def EndO.Know {a : LdJoint E} (Z : EndO a) : Prop :=
  Z.R.red.Know a.rels.on a.rels.relR trivRels.relR Z.ext Z.e

/-! ## The stages in a row -/

/-- A test whose first block's rider is in the input: the data. -/
inductive TowR : LdJoint E → ExtSpec → Type 1
  | base (a : LdJoint E) (t : ℕ) (cov : a.C.NP → a.P) (d bad L2 : ℕ) : TowR a a.C.nat
  | step {P P' Pw St : Type} [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P'] (Y : SumPar E P)
      (sl : Slf E St Y.Cin.J) (e : ℕ) (fx : Fin ((Y.reform sl).n + 1) × E)
      (S : LdSwD (Y.reform sl) P') (Cw : LdCode E Pw) (Pt : Type) [Fintype Pt] [DecidableEq Pt]
      (lf : (S.D e).Cout.NP → Pt) (lfW : Cw.NP → Pt) (d : ℕ) (Lst mC mS mW : ℕ → ℕ) (e' L : ℕ)
      (rest : TowR ((S.D e).jOut e') Cw.nat) : TowR (wholeJ Y sl e) Y.Cw.nat

namespace TowR

/-- The reduction, its extractor and its errors. -/
noncomputable def toEnd : {a : LdJoint E} → {Fx : ExtSpec} → TowR a Fx → EndR a Fx
  | _, _, .base a t cov d bad L2 => ⟨baseRide a t cov, baseExt a t d, baseErr a t bad L2⟩
  | _, _, @TowR.step _ _ _ _ _ _ _ _ _ _ _ Y sl e fx S Cw Pt _ _ lf lfW d Lst mC mS mW e' L rest =>
      ⟨(stageRide Y sl e fx S Cw Pt lf lfW).seq rest.toEnd.R,
        IOR.extSeq (stageRide Y sl e fx S Cw Pt lf lfW) rest.toEnd.R
          (stageExtRide Y sl e fx S Cw Pt lf lfW d e') rest.toEnd.ext 0,
        Err.app (stageErrRide Y sl e fx S Cw Pt lf lfW Lst mC mS mW L) rest.toEnd.e⟩

/-- The conditions of all blocks, on public data alone. -/
def HypK : {a : LdJoint E} → {Fx : ExtSpec} → TowR a Fx → Prop
  | _, _, .base a _ _ d bad L2 => a.BaseHypK d bad L2
  | _, _, @TowR.step _ _ _ _ _ _ _ _ _ _ _ Y sl e _ S _ _ _ _ _ _ d Lst mC mS mW e' L rest =>
      (Y.reform sl).HypK d e Lst mC mS mW ∧ (S.D e).HypK e' L ∧ rest.HypK

/-- Under the conditions of its blocks the test is knowledge sound. -/
theorem know : {a : LdJoint E} → {Fx : ExtSpec} → (T : TowR a Fx) → T.HypK → T.toEnd.Know
  | _, _, .base a t cov d bad L2, h => base_know a t cov d bad L2 h
  | _, _, @TowR.step _ _ _ _ _ _ _ _ _ _ _
      Y sl e fx S Cw Pt _ _ lf lfW d Lst mC mS mW e' L rest, h =>
      know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0
        (stageRide_know Y sl e fx S Cw Pt lf lfW d Lst mC mS mW e' L h.1 h.2.1)
        (rest.know h.2.2) fun _ _ _ _ _ => trivial

/-- The further condition for locality: each switch's new code's transformation reads what it
declares. -/
def Reads : {a : LdJoint E} → {Fx : ExtSpec} → TowR a Fx → Prop
  | _, _, .base .. => True
  | _, _, @TowR.step _ _ _ _ _ _ _ _ _ _ _ _ _ e _ S _ _ _ _ _ _ _ _ _ _ _ _ _ rest =>
      (S.D e).Cout.Reads ∧ rest.Reads

/-- The number of blocks: the stages and the last step. -/
def nBl : {a : LdJoint E} → {Fx : ExtSpec} → TowR a Fx → ℕ
  | _, _, .base .. => 1
  | _, _, @TowR.step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rest => rest.nBl + 1

/-- The oracles are strings of symbols. -/
theorem toEnd_point : {a : LdJoint E} → {Fx : ExtSpec} → (T : TowR a Fx) →
    Nonempty T.toEnd.R.shape.IsPoint
  | _, _, .base a t cov _ _ _ => base_point a t cov
  | _, _, @TowR.step _ _ _ _ _ _ _ _ _ _ _
      Y sl e fx S Cw Pt _ _ lf lfW _ _ _ _ _ _ _ rest =>
      (stageRide_point Y sl e fx S Cw Pt lf lfW).elim fun p =>
        rest.toEnd_point.elim fun q => ⟨Shape.IsPoint.append p q⟩

/-- The verifier is local. -/
theorem toEnd_local : {a : LdJoint E} → {Fx : ExtSpec} → (T : TowR a Fx) → T.HypK → T.Reads →
    T.toEnd.R.IsLocal
  | _, _, .base a t cov _ _ _, h, _ => base_isLocal a t cov h.laws
  | _, _, @TowR.step _ _ _ _ _ _ _ _ _ _ _
      Y sl e fx S Cw Pt _ _ lf lfW _ _ _ _ _ _ _ rest, h, hR =>
      (stageRide_local Y sl e fx S Cw Pt lf lfW h.1.codes.1.1 h.1.codes.1.2.1 h.1.codes.1.2.2
        hR.1).seq (rest.toEnd_local h.2.2 hR.2)

/-- The number of rounds. -/
def len : {a : LdJoint E} → {Fx : ExtSpec} → TowR a Fx → ℕ
  | _, _, .base .. => 2
  | _, _, @TowR.step _ _ _ _ _ _ _ _ _ _ _ Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rest =>
      Y.k + 3 + rest.len

theorem toEnd_len : {a : LdJoint E} → {Fx : ExtSpec} → (T : TowR a Fx) →
    T.toEnd.R.shape.length = T.len
  | _, _, .base a t cov _ _ _ => base_rounds a t cov
  | _, _, @TowR.step _ _ _ _ _ _ _ _ _ _ _ Y sl e fx S Cw Pt _ _ lf lfW _ _ _ _ _ _ _ rest => by
      show ((stageRide Y sl e fx S Cw Pt lf lfW).shape ++ rest.toEnd.R.shape).length = _
      rw [List.length_append, stageRide_rounds, rest.toEnd_len]
      rfl

/-- The errors, round by round. -/
noncomputable def errs : {a : LdJoint E} → {Fx : ExtSpec} → TowR a Fx → List ℕ
  | _, _, .base a t _ _ bad L2 => [bad + L2, (Fintype.card a.P - a.e - 1) ^ t]
  | _, _, @TowR.step _ _ _ _ _ _ _ _ _ _ _ Y sl e _ S _ _ _ _ _ _ _ Lst mC mS mW _ L rest =>
      (((Y.reform sl).err Lst mC mS mW).toList ++ [(S.D e).W.err1 L, (S.D e).W.err2 e L]) ++
        rest.errs

theorem toEnd_errs : {a : LdJoint E} → {Fx : ExtSpec} → (T : TowR a Fx) →
    T.toEnd.e.toList = T.errs
  | _, _, .base a t _ _ bad L2 => base_errList a t bad L2
  | _, _, @TowR.step _ _ _ _ _ _ _ _ _ _ _ Y sl e fx S Cw Pt _ _ lf lfW _ Lst mC mS mW _ L rest =>
      (Err.toList_app (stageErrRide Y sl e fx S Cw Pt lf lfW Lst mC mS mW L) rest.toEnd.e).trans
        (congrArg₂ (· ++ ·) (stageRide_errList Y sl e fx S Cw Pt lf lfW Lst mC mS mW L)
          rest.toEnd_errs)

/-- The numbers of values of the verifier's messages, round by round. -/
noncomputable def vals : {a : LdJoint E} → {Fx : ExtSpec} → TowR a Fx → List ℕ
  | _, _, .base a t _ _ _ _ => [Fintype.card E, Fintype.card (Fin t → a.P)]
  | _, _, @TowR.step _ _ _ P _ _ _ _ _ _ _ Y _ e _ S _ _ _ _ _ _ _ _ _ _ _ _ _ rest =>
      (List.replicate (Y.k + 1) (Fintype.card Y.Ch) ++
        [Fintype.card (S.D e).Zo.D, Fintype.card ((Fin (S.D e).t → P) × (S.D e).Zb.D)]) ++
        rest.vals

theorem toEnd_vals : {a : LdJoint E} → {Fx : ExtSpec} → (T : TowR a Fx) →
    T.toEnd.R.shape.chalList = T.vals
  | _, _, .base a t cov _ _ _ => base_vals a t cov
  | _, _, @TowR.step _ _ _ _ _ _ _ _ _ _ _ Y sl e fx S Cw Pt _ _ lf lfW _ _ _ _ _ _ _ rest =>
      (Shape.chalList_append (stageRide Y sl e fx S Cw Pt lf lfW).shape rest.toEnd.R.shape).trans
        (congrArg₂ (· ++ ·) (stageRide_vals Y sl e fx S Cw Pt lf lfW) rest.toEnd_vals)

end TowR

/-! ## A test whose first fold sends its own mask -/

section Own
variable {P P' Pw St : Type} [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P'] (Y : SumPar E P)
  (sl : Slf E St Y.Cin.J) (e : ℕ) (fx : Fin ((Y.reform sl).n + 1) × E)
  (S : LdSwD (Y.reform sl) P') (Cw : LdCode E Pw) (Pt : Type) (lf : (S.D e).Cout.NP → Pt)
  (lfW : Cw.NP → Pt) (d : ℕ) (Lst mC mS mW : ℕ → ℕ) (e' L : ℕ)
  (rest : TowR ((S.D e).jOut e') Cw.nat)

/-- A stage whose fold sends its mask, then a remainder. -/
noncomputable def ownStep : EndO (wholeJ Y sl e) :=
  ⟨(stageOwn Y sl e fx S Cw Pt lf lfW).seq rest.toEnd.R,
    IOR.extSeq (stageOwn Y sl e fx S Cw Pt lf lfW) rest.toEnd.R
      (stageExtOwn Y sl e fx S Cw Pt lf lfW d e') rest.toEnd.ext 0,
    Err.app (stageErrOwn Y sl e fx S Cw Pt lf lfW Lst mC mS mW L) rest.toEnd.e⟩

theorem ownStep_know (h₁ : (Y.reform sl).HypK d e Lst mC mS mW) (h₂ : (S.D e).HypK e' L)
    (h₃ : rest.HypK) : (ownStep Y sl e fx S Cw Pt lf lfW d Lst mC mS mW e' L rest).Know :=
  know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0
    (stageOwn_know Y sl e fx S Cw Pt lf lfW d Lst mC mS mW e' L h₁ h₂) (rest.know h₃)
    fun _ _ _ _ _ => trivial

end Own

/-! ## A test on a group -/

section Group
variable {B : Type} [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P] (Sh : GShape G)
  (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))

/-- The arrangement, then a test whose first fold's mask is in the input. -/
noncomputable def testRide (T : TowR (wholeJ Sh.par (Sh.form Sb sl Z) G.e) Sh.par.Cw.nat) :
    EndR (G.joint Sb sl Z) Sh.par.Cw.nat :=
  ⟨(arrRide Sh Sb sl Z).seq T.toEnd.R,
    IOR.extSeq (arrRide Sh Sb sl Z) T.toEnd.R (fun _ _ w => Sh.rho.dn w) T.toEnd.ext 0,
    Err.app (s := (arrRide Sh Sb sl Z).shape) () T.toEnd.e⟩

theorem testRide_know (T : TowR (wholeJ Sh.par (Sh.form Sb sl Z) G.e) Sh.par.Cw.nat) (h : Sh.OK)
    (hT : T.HypK) : (testRide Sh Sb sl Z T).Know :=
  know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 (arrRide_know Sh Sb sl Z h) (T.know hT)
    fun _ _ _ _ _ => trivial

theorem testRide_point (T : TowR (wholeJ Sh.par (Sh.form Sb sl Z) G.e) Sh.par.Cw.nat) :
    Nonempty (testRide Sh Sb sl Z T).R.shape.IsPoint :=
  T.toEnd_point.elim fun p => ⟨Shape.IsPoint.append (s := (arrRide Sh Sb sl Z).shape) () p⟩

theorem testRide_local (T : TowR (wholeJ Sh.par (Sh.form Sb sl Z) G.e) Sh.par.Cw.nat) (h : Sh.OK)
    (hT : T.HypK) (hR : T.Reads) : (testRide Sh Sb sl Z T).R.IsLocal :=
  (arrRide_local Sh Sb sl Z h).seq (T.toEnd_local hT hR)

theorem testRide_len (T : TowR (wholeJ Sh.par (Sh.form Sb sl Z) G.e) Sh.par.Cw.nat) :
    (testRide Sh Sb sl Z T).R.shape.length = T.len := T.toEnd_len

/-- The arrangement, then a test that begins at the fold's input code without a rider. -/
noncomputable def testOwn (T : EndO (wholeJ Sh.par (Sh.form Sb sl Z) G.e)) :
    EndO (G.joint Sb sl Z) :=
  ⟨(arrOwn Sh Sb sl Z).seq T.R,
    IOR.extSeq (arrOwn Sh Sb sl Z) T.R (fun _ _ w => Sh.rho.dn w) T.ext 0,
    Err.app (s := (arrOwn Sh Sb sl Z).shape) () T.e⟩

theorem testOwn_know (T : EndO (wholeJ Sh.par (Sh.form Sb sl Z) G.e)) (h : Sh.OK) (hT : T.Know) :
    (testOwn Sh Sb sl Z T).Know :=
  know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 (arrOwn_know Sh Sb sl Z h) hT
    fun _ _ _ _ _ => trivial

end Group

/-! ## The round before the test, then the test beside the carried part -/

section Run
variable (s : Cb.Pv.Bat.Size E) [Nonempty s.G.P] (St₀ : Type) (E₀ : ExtSpec)

/-- The round before the test, then a test without a rider in its input. -/
noncomputable def runOwn (T : EndO (s.G.joint s.Sb s.sl s.Z)) :
    IOR ((((s.B → E) × (∀ b, s.Sb b)) × St₀) × s.S.Smp) (E₀.prod s.S.ext) (Unit × CarX s St₀)
      (extNone.prod (CarE s E₀)) :=
  (Cb.Pv.Bat.R s St₀ E₀).seq (T.R.keep (CarX s St₀) (CarE s E₀))

/-- The round before the test, then a test whose rider stands behind the input's oracles. -/
noncomputable def runRide (Fx : ExtSpec) (T : EndR (s.G.joint s.Sb s.sl s.Z) Fx) :
    IOR ((((s.B → E) × (∀ b, s.Sb b)) × St₀) × s.S.Smp) ((E₀.prod s.S.ext).prod Fx)
      (Unit × CarX s St₀) (extNone.prod (CarE s E₀)) :=
  ((Cb.Pv.Bat.R s St₀ E₀).keepE Fx).seq
    ((IOR.pure some (setR s.G.C.ext (CarE s E₀) Fx)).seq (T.R.keep (CarX s St₀) (CarE s E₀)))

variable {St₀ E₀} {Kc Wp : Type} (A₀ : Rels Kc St₀ E₀ ((s.S.sub s.kp).Msg × Wp))
  (w₀ : s.S.Wit × Wp) (w₁ : LdBrW s.G s.kp Wp)

/-- the joint behind the test: the kept messages' -/
noncomputable abbrev runOut :
    Rels Kc (Unit × CarX s St₀) (extNone.prod (CarE s E₀)) (Unit × ((s.S.sub s.kp).Wit × Wp)) :=
  trivRels.beside ((s.S.sub s.kp).over A₀)

noncomputable def runExtOwn (T : EndO (s.G.joint s.Sb s.sl s.Z)) :
    ((((s.B → E) × (∀ b, s.Sb b)) × St₀) × s.S.Smp) × (E₀.prod s.S.ext).Str →
      Tr (runOwn s St₀ E₀ T).shape →
      Unit × ((s.S.sub s.kp).Wit × Wp) → s.S.Wit × Wp :=
  IOR.extSeq (Cb.Pv.Bat.R s St₀ E₀) (T.R.keep (CarX s St₀) (CarE s E₀))
    (fun _ _ w => ldBrBack s.G s.kp Wp s.hc w)
    (fun a τ w => (T.ext (a.1.1, a.2.1) τ w.1, w.2)) w₀

noncomputable def runErrOwn (T : EndO (s.G.joint s.Sb s.sl s.Z)) :
    Err (runOwn s St₀ E₀ T).shape :=
  Err.app (s := (Cb.Pv.Bat.R s St₀ E₀).shape) (Cb.Pv.Bat.eps s) T.e

/-- The statement that the round before the test and the test are knowledge sound. -/
def RunOwnKnow (T : EndO (s.G.joint s.Sb s.sl s.Z)) : Prop :=
  (runOwn s St₀ E₀ T).red.Know (Cb.Pv.Bat.inJ s A₀).on (Cb.Pv.Bat.inJ s A₀).relR
    (runOut s A₀).relR (runExtOwn s w₀ T) (runErrOwn s T)

theorem runOwn_know (T : EndO (s.G.joint s.Sb s.sl s.Z)) (hZ : s.Z.OK)
    (hL : s.G.C.ListAt s.G.e s.L) (hF : s.G.Fits) (hT : T.Know) : RunOwnKnow s A₀ w₀ T :=
  know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ w₀
    (Cb.Pv.Bat.hAt s hZ hL hF Kc St₀ Wp E₀ A₀)
    (know_beside Kc _ _ _ _ _ _ T.R _ _ _ (s.G.joint s.Sb s.sl s.Z).rels trivRels T.ext T.e
      ((s.S.sub s.kp).over A₀) hT)
    (Cb.Pv.Bat.onOut s hZ hL hF A₀)

variable (Fx : ExtSpec)

theorem setR_know' :
    (IOR.pure some (setR s.G.C.ext (CarE s E₀) Fx)).red.Know ((Cb.Pv.Bat.outJ s A₀).keepE Fx).on
      ((Cb.Pv.Bat.outJ s A₀).keepE Fx).relR
      (((s.G.joint s.Sb s.sl s.Z).rels.keepE Fx).beside ((s.S.sub s.kp).over A₀)).relR
      (fun _ _ w => w) () :=
  know_pure _ _ _ _ _ _ _ _ _ _ _ (fun _ w => w) () (fun _ _ _ _ e hw => by
    obtain rfl := Option.some.inj e
    exact hw)

theorem setR_onOut' : ∀ a τ b, ((Cb.Pv.Bat.outJ s A₀).keepE Fx).on a →
    (IOR.pure some (setR s.G.C.ext (CarE s E₀) Fx)).red.out a τ = some b →
      (((s.G.joint s.Sb s.sl s.Z).rels.keepE Fx).beside ((s.S.sub s.kp).over A₀)).on b :=
  onOut_pure _ _ _ _ _ _ _ _ (fun _ _ ha e => by
    obtain rfl := Option.some.inj e
    exact ha)

noncomputable def runExtRide (T : EndR (s.G.joint s.Sb s.sl s.Z) Fx) :
    ((((s.B → E) × (∀ b, s.Sb b)) × St₀) × s.S.Smp) × ((E₀.prod s.S.ext).prod Fx).Str →
      Tr (runRide s St₀ E₀ Fx T).shape →
      Unit × ((s.S.sub s.kp).Wit × Wp) → s.S.Wit × Wp :=
  IOR.extSeq ((Cb.Pv.Bat.R s St₀ E₀).keepE Fx)
    ((IOR.pure some (setR s.G.C.ext (CarE s E₀) Fx)).seq (T.R.keep (CarX s St₀) (CarE s E₀)))
    (fun _ _ w => ldBrBack s.G s.kp Wp s.hc w)
    (IOR.extSeq (IOR.pure some (setR s.G.C.ext (CarE s E₀) Fx))
      (T.R.keep (CarX s St₀) (CarE s E₀)) (fun _ _ w => w)
      (fun a τ w => (T.ext (a.1.1, a.2.1) τ w.1, w.2)) w₁)
    w₀

noncomputable def runErrRide (T : EndR (s.G.joint s.Sb s.sl s.Z) Fx) :
    Err (runRide s St₀ E₀ Fx T).shape :=
  Err.app (s := (Cb.Pv.Bat.R s St₀ E₀).shape) (Cb.Pv.Bat.eps s)
    (Err.app (s := (IOR.pure some (setR s.G.C.ext (CarE s E₀) Fx)).shape) () T.e)

/-- The statement of the same with a rider behind the input's oracles. -/
def RunRideKnow (T : EndR (s.G.joint s.Sb s.sl s.Z) Fx) : Prop :=
  (runRide s St₀ E₀ Fx T).red.Know ((Cb.Pv.Bat.inJ s A₀).keepE Fx).on
    ((Cb.Pv.Bat.inJ s A₀).keepE Fx).relR (runOut s A₀).relR (runExtRide s w₀ w₁ Fx T)
    (runErrRide s Fx T)

theorem runRide_know (T : EndR (s.G.joint s.Sb s.sl s.Z) Fx) (hZ : s.Z.OK)
    (hL : s.G.C.ListAt s.G.e s.L) (hF : s.G.Fits) (hT : T.Know) :
    RunRideKnow s A₀ w₀ w₁ Fx T :=
  know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ w₀
    (know_keepE Fx (Cb.Pv.Bat.R s St₀ E₀) (Cb.Pv.Bat.inJ s A₀) (Cb.Pv.Bat.outJ s A₀)
      (fun _ _ w => ldBrBack s.G s.kp Wp s.hc w) (Cb.Pv.Bat.eps s)
      (Cb.Pv.Bat.hAt s hZ hL hF Kc St₀ Wp E₀ A₀))
    (know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ w₁ (setR_know' s A₀ Fx)
      (know_beside Kc _ _ _ _ _ _ T.R _ _ _ ((s.G.joint s.Sb s.sl s.Z).rels.keepE Fx) trivRels
        T.ext T.e ((s.S.sub s.kp).over A₀) hT)
      (setR_onOut' s A₀ Fx))
    (onOut_keepE Fx (Cb.Pv.Bat.R s St₀ E₀) (Cb.Pv.Bat.inJ s A₀) (Cb.Pv.Bat.outJ s A₀)
      (Cb.Pv.Bat.onOut s hZ hL hF A₀))

theorem runRide_rounds (T : EndR (s.G.joint s.Sb s.sl s.Z) Fx) :
    (runRide s St₀ E₀ Fx T).shape.length = 1 + T.R.shape.length := by
  show ((Cb.Pv.Bat.R s St₀ E₀).shape ++ ([] ++ T.R.shape)).length = _
  rw [List.length_append, List.nil_append, Cb.Pv.Bat.rounds]

theorem runOwn_rounds (T : EndO (s.G.joint s.Sb s.sl s.Z)) :
    (runOwn s St₀ E₀ T).shape.length = 1 + T.R.shape.length := by
  show ((Cb.Pv.Bat.R s St₀ E₀).shape ++ T.R.shape).length = _
  rw [List.length_append, Cb.Pv.Bat.rounds]

end Run

#print axioms TowR.know
#print axioms TowR.toEnd_errs
#print axioms TowR.toEnd_vals
#print axioms ownStep_know
#print axioms testRide_know
#print axioms runRide_know
#print axioms runOwn_know

end Cb.Pv.Tower
