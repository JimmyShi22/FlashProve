-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tower/First.lean: the first stage of a proximity test on a group of oracle messages, and the
seam from the round before the test to it: the rows as they were sent are arranged for the fold;
then a stage as any other. Also the batching round, the arrangement, the cut and the fold in a row,
beside what is carried. For each the statement that it is round-by-round knowledge sound, proved
under conditions on codes and numbers that no file here shows of any setting.

The round before a test (Cb/Pv/Bat.lean) ends at the joint of the group's complex as it was sent,
with one batched form, beside the joint of the kept messages. A stage (Cb/Pv/Tower/Stage.lean)
begins at the joint of a fold's input code with one form. Between the two stands the library's
arrangement (`GShape.rho`, Cb/Ld/LdGroupFold.lean), a step without rounds (`ldShapeBlock`,
Cb/Ld/LdBatShapeBlock.lean). The library lays arrangement, cut and its own fold as one block
(`GShape.block`); here the arrangement is taken alone, and the cut, the fold and the switch are
those of Cb/Pv/Tower/Stage.lean: short rounds; riders. Definitions and proofs.
Main names (Sh : `GShape G`; Sb, sl, Z: the rows' states and forms and the coefficients of the round
before; the other letters as in Cb/Pv/Tower/Stage.lean, at the fold `Sh.par`, the form `Sh.form Sb
sl Z` and the radius `G.e`):
  `arrOwn`, `arrRide`: the arrangement; the same while the fold's mask is handed on.
  `arrOwn_know`, `arrRide_know`: under `Sh.OK`. `arr_stage_seam`: the arrangement ends where a stage
    begins: one joint, by definition.
  `firstOwn`, `firstRide`: arrangement, then a stage. `FirstOwnKnow`, `FirstRideKnow`: the
    statements. `firstOwn_know`, `firstRide_know`: under `Sh.OK` and the two conditions of a stage.
  `gfOwn`, `gfRide`: arrangement, cut, fold, without a switch. `gfOwn_know`, `gfRide_know`.
  `arrOwn_local`, `arrRide_local` (under `Sh.OK`), `arrOwn_point`, `arrRide_point`.
  `setR`: the map of oracles that sets a rider next to the group's word. `setR_isLocal`.
  `batFoldOwn`, `batFoldRide`: the round before the test, then `gfOwn` | `gfRide` beside the carried
    part. `BatFoldOwnKnow`, `BatFoldRideKnow`: the statements. `batFoldOwn_know`,
    `batFoldRide_know`.
  `_rounds` for each: k + 3; k + 1; k + 2.
Limits: those of the files named. Of point oracles and locality only the arrangement's and `setR`'s
are here. That a group of a chain of the programs has a shape with `Sh.OK` is not shown. Nothing on
an honest prover.

-/
import Cb.Pv.Tower.Stage
import Cb.Pv.Bat
import Cb.Ld.LdGroupFoldProofs
import Ior.KnowRulesProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tower
open Iop Prob Hiop IOR

/-! ## The arrangement -/

section Arr
variable {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  (Sh : GShape G) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))

/-- the state of the one batched form -/
abbrev BSt : Type := (∀ ν, G.RowSt Sb ν) × Z.D

/-- The arrangement: a step without rounds. -/
noncomputable def arrOwn : IOR (E × BSt Sb Z) G.C.ext (E × BSt Sb Z) Sh.par.Cin.ext :=
  (ldShapeBlock Sh.rho (Slf.bat Z.ze (G.rows sl)) G.e).R

/-- The same while the fold's mask is handed on. -/
noncomputable def arrRide :
    IOR (E × BSt Sb Z) (G.C.ext.prod Sh.par.Cw.nat) (E × BSt Sb Z) (EiRide Sh.par) :=
  (arrOwn Sh Sb sl Z).keepE Sh.par.Cw.nat

/-- the joints at which a test on the group begins -/
noncomputable abbrev firstInOwn : IOR.Rels Unit (E × BSt Sb Z) G.C.ext G.C.N.Wit :=
  (G.joint Sb sl Z).rels

noncomputable abbrev firstInRide :
    IOR.Rels Unit (E × BSt Sb Z) (G.C.ext.prod Sh.par.Cw.nat) G.C.N.Wit :=
  (G.joint Sb sl Z).rels.keepE Sh.par.Cw.nat

/-- The arrangement ends where a stage begins. -/
theorem arr_stage_seam :
    (⟨G.P, Sh.Cin, BSt Sb Z, Sh.rho.sl (Slf.bat Z.ze (G.rows sl)), G.e⟩ : LdJoint E).rels =
      stageInOwn Sh.par (Sh.form Sb sl Z) G.e := rfl

theorem arrOwn_know (h : Sh.OK) :
    (arrOwn Sh Sb sl Z).red.Know (firstInOwn Sb sl Z).on (firstInOwn Sb sl Z).relR
      (stageInOwn Sh.par (Sh.form Sb sl Z) G.e).relR (fun _ _ w => Sh.rho.dn w) () :=
  ldEnt_shape_know E G.P G.C Sh.Cin Sh.rho (BSt Sb Z) (Slf.bat Z.ze (G.rows sl)) G.e
    (ldGroup_shape_laws E S G Sh h).1

theorem arrRide_know (h : Sh.OK) :
    (arrRide Sh Sb sl Z).red.Know (firstInRide Sh Sb sl Z).on (firstInRide Sh Sb sl Z).relR
      (stageInRide Sh.par (Sh.form Sb sl Z) G.e).relR (fun _ _ w => Sh.rho.dn w) () :=
  know_keepE Sh.par.Cw.nat (arrOwn Sh Sb sl Z) (firstInOwn Sb sl Z)
    (stageInOwn Sh.par (Sh.form Sb sl Z) G.e) (fun _ _ w => Sh.rho.dn w) ()
    (arrOwn_know Sh Sb sl Z h)

theorem arrOwn_local (h : Sh.OK) : (arrOwn Sh Sb sl Z).IsLocal :=
  (ldShape_block E G.P G.C Sh.Cin Sh.rho (BSt Sb Z) (Slf.bat Z.ze (G.rows sl)) G.e 0
    (ldGroup_shape_laws E S G Sh h).1).good.isLocal

theorem arrRide_local (h : Sh.OK) : (arrRide Sh Sb sl Z).IsLocal :=
  (arrOwn_local Sh Sb sl Z h).keepE Sh.par.Cw.nat

theorem arrOwn_point : Nonempty (arrOwn Sh Sb sl Z).shape.IsPoint := ⟨()⟩

theorem arrRide_point : Nonempty (arrRide Sh Sb sl Z).shape.IsPoint := ⟨()⟩

end Arr

/-! ## The first stage -/

section First
variable {E B P' Pw : Type} [Field E] [Fintype E] [Fintype B] [Fintype P'] [Nonempty P']
  {S : Sig E} {G : Grp S} [Nonempty G.P] (Sh : GShape G) (Sb : B → Type)
  (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))
  (fx : Fin ((Sh.fold Sb sl Z).n + 1) × E) (Sw : LdSwD (Sh.fold Sb sl Z) P') (Cw : LdCode E Pw)
  (Pt : Type) (lf : (Sw.D G.e).Cout.NP → Pt) (lfW : Cw.NP → Pt)

/-- The first stage on a group; the fold sends its fresh mask. -/
noncomputable def firstOwn :
    IOR (E × BSt Sb Z) G.C.ext (E × (Sw.D G.e).St') ((Sw.D G.e).Cout.ext.prod Cw.nat) :=
  (arrOwn Sh Sb sl Z).seq (stageOwn Sh.par (Sh.form Sb sl Z) G.e fx Sw Cw Pt lf lfW)

/-- The first stage on a group; the fold's mask was sent earlier. -/
noncomputable def firstRide :
    IOR (E × BSt Sb Z) (G.C.ext.prod Sh.par.Cw.nat) (E × (Sw.D G.e).St')
      ((Sw.D G.e).Cout.ext.prod Cw.nat) :=
  (arrRide Sh Sb sl Z).seq (stageRide Sh.par (Sh.form Sb sl Z) G.e fx Sw Cw Pt lf lfW)

variable (d : ℕ) (Lst mC mS mW : ℕ → ℕ) (e' L : ℕ)

noncomputable def firstExtOwn :
    (E × BSt Sb Z) × G.C.ext.Str → Tr (firstOwn Sh Sb sl Z fx Sw Cw Pt lf lfW).shape →
      ((Sw.D G.e).jOut e').W → G.C.N.Wit :=
  IOR.extSeq (arrOwn Sh Sb sl Z) (stageOwn Sh.par (Sh.form Sb sl Z) G.e fx Sw Cw Pt lf lfW)
    (fun _ _ w => Sh.rho.dn w) (stageExtOwn Sh.par (Sh.form Sb sl Z) G.e fx Sw Cw Pt lf lfW d e') 0

noncomputable def firstExtRide :
    (E × BSt Sb Z) × (G.C.ext.prod Sh.par.Cw.nat).Str →
      Tr (firstRide Sh Sb sl Z fx Sw Cw Pt lf lfW).shape → ((Sw.D G.e).jOut e').W → G.C.N.Wit :=
  IOR.extSeq (arrRide Sh Sb sl Z) (stageRide Sh.par (Sh.form Sb sl Z) G.e fx Sw Cw Pt lf lfW)
    (fun _ _ w => Sh.rho.dn w) (stageExtRide Sh.par (Sh.form Sb sl Z) G.e fx Sw Cw Pt lf lfW d e') 0

noncomputable def firstErrOwn : Err (firstOwn Sh Sb sl Z fx Sw Cw Pt lf lfW).shape :=
  Err.app (s := (arrOwn Sh Sb sl Z).shape) ()
    (stageErrOwn Sh.par (Sh.form Sb sl Z) G.e fx Sw Cw Pt lf lfW Lst mC mS mW L)

noncomputable def firstErrRide : Err (firstRide Sh Sb sl Z fx Sw Cw Pt lf lfW).shape :=
  Err.app (s := (arrRide Sh Sb sl Z).shape) ()
    (stageErrRide Sh.par (Sh.form Sb sl Z) G.e fx Sw Cw Pt lf lfW Lst mC mS mW L)

/-- The statement that the first stage whose fold sends its mask is knowledge sound. -/
def FirstOwnKnow : Prop :=
  (firstOwn Sh Sb sl Z fx Sw Cw Pt lf lfW).red.Know (firstInOwn Sb sl Z).on
    (firstInOwn Sb sl Z).relR (stageOut Sh.par (Sh.form Sb sl Z) G.e Sw Cw e').relR
    (firstExtOwn Sh Sb sl Z fx Sw Cw Pt lf lfW d e')
    (firstErrOwn Sh Sb sl Z fx Sw Cw Pt lf lfW Lst mC mS mW L)

/-- The statement that the first stage whose fold's mask was sent earlier is knowledge sound. -/
def FirstRideKnow : Prop :=
  (firstRide Sh Sb sl Z fx Sw Cw Pt lf lfW).red.Know (firstInRide Sh Sb sl Z).on
    (firstInRide Sh Sb sl Z).relR (stageOut Sh.par (Sh.form Sb sl Z) G.e Sw Cw e').relR
    (firstExtRide Sh Sb sl Z fx Sw Cw Pt lf lfW d e')
    (firstErrRide Sh Sb sl Z fx Sw Cw Pt lf lfW Lst mC mS mW L)

theorem firstOwn_know (h : Sh.OK) (h₁ : (Sh.fold Sb sl Z).HypK d G.e Lst mC mS mW)
    (h₂ : (Sw.D G.e).HypK e' L) :
    FirstOwnKnow Sh Sb sl Z fx Sw Cw Pt lf lfW d Lst mC mS mW e' L :=
  know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 (arrOwn_know Sh Sb sl Z h)
    (stageOwn_know Sh.par (Sh.form Sb sl Z) G.e fx Sw Cw Pt lf lfW d Lst mC mS mW e' L h₁ h₂)
    fun _ _ _ _ _ => trivial

theorem firstRide_know (h : Sh.OK) (h₁ : (Sh.fold Sb sl Z).HypK d G.e Lst mC mS mW)
    (h₂ : (Sw.D G.e).HypK e' L) :
    FirstRideKnow Sh Sb sl Z fx Sw Cw Pt lf lfW d Lst mC mS mW e' L :=
  know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 (arrRide_know Sh Sb sl Z h)
    (stageRide_know Sh.par (Sh.form Sb sl Z) G.e fx Sw Cw Pt lf lfW d Lst mC mS mW e' L h₁ h₂)
    fun _ _ _ _ _ => trivial

omit [Fintype P'] [Nonempty P'] in
theorem firstOwn_rounds :
    (firstOwn Sh Sb sl Z fx Sw Cw Pt lf lfW).shape.length = Sh.par.k + 3 :=
  stageOwn_rounds Sh.par (Sh.form Sb sl Z) G.e fx Sw Cw Pt lf lfW

omit [Fintype P'] [Nonempty P'] in
theorem firstRide_rounds :
    (firstRide Sh Sb sl Z fx Sw Cw Pt lf lfW).shape.length = Sh.par.k + 3 :=
  stageRide_rounds Sh.par (Sh.form Sb sl Z) G.e fx Sw Cw Pt lf lfW

end First

/-! ## Arrangement, cut, fold -/

section GroupFold
variable {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  (Sh : GShape G) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))
  (fx : Fin ((Sh.fold Sb sl Z).n + 1) × E)

/-- Arrangement, cut, fold; the fold sends its fresh mask. -/
noncomputable def gfOwn :
    IOR (E × BSt Sb Z) G.C.ext (Sh.fold Sb sl Z).Xo (Sh.fold Sb sl Z).Cout.ext :=
  (arrOwn Sh Sb sl Z).seq
    ((cutOwn Sh.par (Sh.form Sb sl Z) G.e).seq (foldOwn (Sh.fold Sb sl Z) fx))

/-- Arrangement, cut, fold; the fold's mask was sent earlier. -/
noncomputable def gfRide :
    IOR (E × BSt Sb Z) (G.C.ext.prod Sh.par.Cw.nat) (Sh.fold Sb sl Z).Xo
      (Sh.fold Sb sl Z).Cout.ext :=
  (arrRide Sh Sb sl Z).seq
    ((cutRide Sh.par (Sh.form Sb sl Z) G.e).seq (foldRide (Sh.fold Sb sl Z) fx))

variable (d : ℕ) (Lst mC mS mW : ℕ → ℕ)

noncomputable def gfExtOwn :
    (E × BSt Sb Z) × G.C.ext.Str → Tr (gfOwn Sh Sb sl Z fx).shape →
      (Sh.fold Sb sl Z).Cout.N.Wit → G.C.N.Wit :=
  IOR.extSeq (arrOwn Sh Sb sl Z)
    ((cutOwn Sh.par (Sh.form Sb sl Z) G.e).seq (foldOwn (Sh.fold Sb sl Z) fx))
    (fun _ _ w => Sh.rho.dn w)
    (IOR.extSeq (cutOwn Sh.par (Sh.form Sb sl Z) G.e) (foldOwn (Sh.fold Sb sl Z) fx)
      (fun _ _ w => w) (extOwn (Sh.fold Sb sl Z) fx d 0) 0) 0

noncomputable def gfExtRide :
    (E × BSt Sb Z) × (G.C.ext.prod Sh.par.Cw.nat).Str → Tr (gfRide Sh Sb sl Z fx).shape →
      (Sh.fold Sb sl Z).Cout.N.Wit → G.C.N.Wit :=
  IOR.extSeq (arrRide Sh Sb sl Z)
    ((cutRide Sh.par (Sh.form Sb sl Z) G.e).seq (foldRide (Sh.fold Sb sl Z) fx))
    (fun _ _ w => Sh.rho.dn w)
    (IOR.extSeq (cutRide Sh.par (Sh.form Sb sl Z) G.e) (foldRide (Sh.fold Sb sl Z) fx)
      (fun _ _ w => w) (extRide (Sh.fold Sb sl Z) fx d 0) 0) 0

noncomputable def gfErrOwn : Err (gfOwn Sh Sb sl Z fx).shape :=
  Err.app (s := (arrOwn Sh Sb sl Z).shape) ()
    (Err.app (s := (cutOwn Sh.par (Sh.form Sb sl Z) G.e).shape) ()
      (errOwn (Sh.fold Sb sl Z) fx Lst mC mS mW))

noncomputable def gfErrRide : Err (gfRide Sh Sb sl Z fx).shape :=
  Err.app (s := (arrRide Sh Sb sl Z).shape) ()
    (Err.app (s := (cutRide Sh.par (Sh.form Sb sl Z) G.e).shape) ()
      (errRide (Sh.fold Sb sl Z) fx Lst mC mS mW))

theorem gfOwn_know (h : Sh.OK) (h₁ : (Sh.fold Sb sl Z).HypK d G.e Lst mC mS mW) :
    (gfOwn Sh Sb sl Z fx).red.Know (firstInOwn Sb sl Z).on (firstInOwn Sb sl Z).relR
      (outJ (Sh.fold Sb sl Z) G.e).relR (gfExtOwn Sh Sb sl Z fx d)
      (gfErrOwn Sh Sb sl Z fx Lst mC mS mW) :=
  know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 (arrOwn_know Sh Sb sl Z h)
    (know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0
      (cutOwn_know Sh.par (Sh.form Sb sl Z) G.e)
      (foldOwn_know (Sh.fold Sb sl Z) fx d G.e Lst mC mS mW 0 h₁) fun _ _ _ _ _ => trivial)
    fun _ _ _ _ _ => trivial

theorem gfRide_know (h : Sh.OK) (h₁ : (Sh.fold Sb sl Z).HypK d G.e Lst mC mS mW) :
    (gfRide Sh Sb sl Z fx).red.Know (firstInRide Sh Sb sl Z).on (firstInRide Sh Sb sl Z).relR
      (outJ (Sh.fold Sb sl Z) G.e).relR (gfExtRide Sh Sb sl Z fx d)
      (gfErrRide Sh Sb sl Z fx Lst mC mS mW) :=
  know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 (arrRide_know Sh Sb sl Z h)
    (know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0
      (cutRide_know Sh.par (Sh.form Sb sl Z) G.e)
      (foldRide_know (Sh.fold Sb sl Z) fx d G.e Lst mC mS mW 0 h₁) fun _ _ _ _ _ => trivial)
    fun _ _ _ _ _ => trivial

theorem gfOwn_rounds : (gfOwn Sh Sb sl Z fx).shape.length = Sh.par.k + 1 :=
  foldOwn_rounds (Sh.fold Sb sl Z) fx

theorem gfRide_rounds : (gfRide Sh Sb sl Z fx).shape.length = Sh.par.k + 1 :=
  foldRide_rounds (Sh.fold Sb sl Z) fx

end GroupFold

/-! ## The round before the test, then arrangement, cut and fold beside the carried part -/

/-- A rider behind a pair of oracles is set next to the first of the pair. -/
noncomputable def setR (A B F : ExtSpec) : ExtMap ((A.prod B).prod F) ((A.prod F).prod B) :=
  (((ExtMap.fst A B).comp (ExtMap.fst (A.prod B) F)).pair (ExtMap.snd (A.prod B) F)).pair
    ((ExtMap.snd A B).comp (ExtMap.fst (A.prod B) F))

theorem setR_isLocal (A B F : ExtSpec) : (setR A B F).IsLocal := by
  obtain ⟨_, hfs, _, hcomp, hpair⟩ := extMap_isLocal
  exact hpair _ _ _ _ _
    (hpair _ _ _ _ _ (hcomp _ _ _ _ _ (hfs A B).1 (hfs (A.prod B) F).1) (hfs (A.prod B) F).2)
    (hcomp _ _ _ _ _ (hfs A B).2 (hfs (A.prod B) F).1)

section BatFold
variable {E : Type} [Field E] [Fintype E] (s : Cb.Pv.Bat.Size E) [Nonempty s.G.P]
  (Sh : GShape s.G) (fx : Fin ((Sh.fold s.Sb s.sl s.Z).n + 1) × E) (St₀ : Type) (E₀ : ExtSpec)

/-- what is carried beside the test -/
abbrev CarX : Type := St₀ × (s.S.sub s.kp).Smp
abbrev CarE : ExtSpec := E₀.prod (s.S.sub s.kp).ext

/-- The round before the test, the arrangement, the cut, the fold; the fold sends its mask. -/
noncomputable def batFoldOwn :
    IOR ((((s.B → E) × (∀ b, s.Sb b)) × St₀) × s.S.Smp) (E₀.prod s.S.ext)
      ((Sh.fold s.Sb s.sl s.Z).Xo × CarX s St₀)
      ((Sh.fold s.Sb s.sl s.Z).Cout.ext.prod (CarE s E₀)) :=
  (Cb.Pv.Bat.R s St₀ E₀).seq ((gfOwn Sh s.Sb s.sl s.Z fx).keep (CarX s St₀) (CarE s E₀))

/-- The same; the fold's mask was sent earlier and stands behind the input's oracles. -/
noncomputable def batFoldRide :
    IOR ((((s.B → E) × (∀ b, s.Sb b)) × St₀) × s.S.Smp) ((E₀.prod s.S.ext).prod Sh.par.Cw.nat)
      ((Sh.fold s.Sb s.sl s.Z).Xo × CarX s St₀)
      ((Sh.fold s.Sb s.sl s.Z).Cout.ext.prod (CarE s E₀)) :=
  ((Cb.Pv.Bat.R s St₀ E₀).keepE Sh.par.Cw.nat).seq
    ((IOR.pure some (setR s.G.C.ext (CarE s E₀) Sh.par.Cw.nat)).seq
      ((gfRide Sh s.Sb s.sl s.Z fx).keep (CarX s St₀) (CarE s E₀)))

variable {St₀ E₀} {Kc Wp : Type} (A₀ : Rels Kc St₀ E₀ ((s.S.sub s.kp).Msg × Wp))
  (d : ℕ) (Lst mC mS mW : ℕ → ℕ) (w₀ : s.S.Wit × Wp)

/-- the joint behind the fold, beside the carried part -/
noncomputable abbrev batFoldOut :
    Rels Kc ((Sh.fold s.Sb s.sl s.Z).Xo × CarX s St₀)
      ((Sh.fold s.Sb s.sl s.Z).Cout.ext.prod (CarE s E₀))
      ((Sh.fold s.Sb s.sl s.Z).Cout.N.Wit × ((s.S.sub s.kp).Wit × Wp)) :=
  (outJ (Sh.fold s.Sb s.sl s.Z) s.G.e).beside ((s.S.sub s.kp).over A₀)

noncomputable def batFoldExtOwn :
    ((((s.B → E) × (∀ b, s.Sb b)) × St₀) × s.S.Smp) × (E₀.prod s.S.ext).Str →
      Tr (batFoldOwn s Sh fx St₀ E₀).shape →
      (Sh.fold s.Sb s.sl s.Z).Cout.N.Wit × ((s.S.sub s.kp).Wit × Wp) → s.S.Wit × Wp :=
  IOR.extSeq (Cb.Pv.Bat.R s St₀ E₀) ((gfOwn Sh s.Sb s.sl s.Z fx).keep (CarX s St₀) (CarE s E₀))
    (fun _ _ w => ldBrBack s.G s.kp Wp s.hc w)
    (fun a τ w => (gfExtOwn Sh s.Sb s.sl s.Z fx d (a.1.1, a.2.1) τ w.1, w.2)) w₀

noncomputable def batFoldErrOwn : Err (batFoldOwn s Sh fx St₀ E₀).shape :=
  Err.app (s := (Cb.Pv.Bat.R s St₀ E₀).shape) (Cb.Pv.Bat.eps s)
    (gfErrOwn Sh s.Sb s.sl s.Z fx Lst mC mS mW)

/-- The statement that the round before the test, arrangement, cut and fold are knowledge sound. -/
def BatFoldOwnKnow : Prop :=
  (batFoldOwn s Sh fx St₀ E₀).red.Know (Cb.Pv.Bat.inJ s A₀).on (Cb.Pv.Bat.inJ s A₀).relR
    (batFoldOut s Sh A₀).relR (batFoldExtOwn s Sh fx d w₀) (batFoldErrOwn s Sh fx Lst mC mS mW)

theorem batFoldOwn_know (hZ : s.Z.OK) (hL : s.G.C.ListAt s.G.e s.L) (hF : s.G.Fits) (h : Sh.OK)
    (h₁ : (Sh.fold s.Sb s.sl s.Z).HypK d s.G.e Lst mC mS mW) :
    BatFoldOwnKnow s Sh fx A₀ d Lst mC mS mW w₀ :=
  know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ w₀
    (Cb.Pv.Bat.hAt s hZ hL hF Kc St₀ Wp E₀ A₀)
    (know_beside Kc _ _ _ _ _ _ (gfOwn Sh s.Sb s.sl s.Z fx) _ _ _ (firstInOwn s.Sb s.sl s.Z)
      (outJ (Sh.fold s.Sb s.sl s.Z) s.G.e) (gfExtOwn Sh s.Sb s.sl s.Z fx d)
      (gfErrOwn Sh s.Sb s.sl s.Z fx Lst mC mS mW) ((s.S.sub s.kp).over A₀)
      (gfOwn_know Sh s.Sb s.sl s.Z fx d Lst mC mS mW h h₁))
    (Cb.Pv.Bat.onOut s hZ hL hF A₀)

variable (w₁ : LdBrW s.G s.kp Wp)

/-- the joint behind the round before the test, the rider passing -/
noncomputable abbrev batMid₁ :
    Rels Kc (LdBrXo s.G s.kp s.Sb s.Z St₀) ((LdBrE s.G s.kp E₀).prod Sh.par.Cw.nat)
      (LdBrW s.G s.kp Wp) :=
  (Cb.Pv.Bat.outJ s A₀).keepE Sh.par.Cw.nat

/-- the same joint, the rider next to the group's word -/
noncomputable abbrev batMid₂ :
    Rels Kc (LdBrXo s.G s.kp s.Sb s.Z St₀) ((s.G.C.ext.prod Sh.par.Cw.nat).prod (CarE s E₀))
      (LdBrW s.G s.kp Wp) :=
  (firstInRide Sh s.Sb s.sl s.Z).beside ((s.S.sub s.kp).over A₀)

theorem setR_know :
    (IOR.pure some (setR s.G.C.ext (CarE s E₀) Sh.par.Cw.nat)).red.Know (batMid₁ s Sh A₀).on
      (batMid₁ s Sh A₀).relR (batMid₂ s Sh A₀).relR (fun _ _ w => w) () :=
  know_pure _ _ _ _ _ _ _ _ _ _ _ (fun _ w => w) () (fun _ _ _ _ e hw => by
    obtain rfl := Option.some.inj e
    exact hw)

theorem setR_onOut : ∀ a τ b, (batMid₁ s Sh A₀).on a →
    (IOR.pure some (setR s.G.C.ext (CarE s E₀) Sh.par.Cw.nat)).red.out a τ = some b →
      (batMid₂ s Sh A₀).on b :=
  onOut_pure _ _ _ _ _ _ _ _ (fun _ _ ha e => by
    obtain rfl := Option.some.inj e
    exact ha)

noncomputable def batFoldExtRide :
    ((((s.B → E) × (∀ b, s.Sb b)) × St₀) × s.S.Smp) × ((E₀.prod s.S.ext).prod Sh.par.Cw.nat).Str →
      Tr (batFoldRide s Sh fx St₀ E₀).shape →
      (Sh.fold s.Sb s.sl s.Z).Cout.N.Wit × ((s.S.sub s.kp).Wit × Wp) → s.S.Wit × Wp :=
  IOR.extSeq ((Cb.Pv.Bat.R s St₀ E₀).keepE Sh.par.Cw.nat)
    ((IOR.pure some (setR s.G.C.ext (CarE s E₀) Sh.par.Cw.nat)).seq
      ((gfRide Sh s.Sb s.sl s.Z fx).keep (CarX s St₀) (CarE s E₀)))
    (fun _ _ w => ldBrBack s.G s.kp Wp s.hc w)
    (IOR.extSeq (IOR.pure some (setR s.G.C.ext (CarE s E₀) Sh.par.Cw.nat))
      ((gfRide Sh s.Sb s.sl s.Z fx).keep (CarX s St₀) (CarE s E₀)) (fun _ _ w => w)
      (fun a τ w => (gfExtRide Sh s.Sb s.sl s.Z fx d (a.1.1, a.2.1) τ w.1, w.2)) w₁)
    w₀

noncomputable def batFoldErrRide : Err (batFoldRide s Sh fx St₀ E₀).shape :=
  Err.app (s := (Cb.Pv.Bat.R s St₀ E₀).shape) (Cb.Pv.Bat.eps s)
    (Err.app (s := (IOR.pure some (setR s.G.C.ext (CarE s E₀) Sh.par.Cw.nat)).shape) ()
      (gfErrRide Sh s.Sb s.sl s.Z fx Lst mC mS mW))

/-- The statement of the same with the fold's mask sent earlier. -/
def BatFoldRideKnow : Prop :=
  (batFoldRide s Sh fx St₀ E₀).red.Know ((Cb.Pv.Bat.inJ s A₀).keepE Sh.par.Cw.nat).on
    ((Cb.Pv.Bat.inJ s A₀).keepE Sh.par.Cw.nat).relR (batFoldOut s Sh A₀).relR
    (batFoldExtRide s Sh fx d w₀ w₁) (batFoldErrRide s Sh fx Lst mC mS mW)

theorem batFoldRide_know (hZ : s.Z.OK) (hL : s.G.C.ListAt s.G.e s.L) (hF : s.G.Fits) (h : Sh.OK)
    (h₁ : (Sh.fold s.Sb s.sl s.Z).HypK d s.G.e Lst mC mS mW) :
    BatFoldRideKnow s Sh fx A₀ d Lst mC mS mW w₀ w₁ :=
  know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ w₀
    (know_keepE Sh.par.Cw.nat (Cb.Pv.Bat.R s St₀ E₀) (Cb.Pv.Bat.inJ s A₀) (Cb.Pv.Bat.outJ s A₀)
      (fun _ _ w => ldBrBack s.G s.kp Wp s.hc w) (Cb.Pv.Bat.eps s)
      (Cb.Pv.Bat.hAt s hZ hL hF Kc St₀ Wp E₀ A₀))
    (know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ w₁ (setR_know s Sh A₀)
      (know_beside Kc _ _ _ _ _ _ (gfRide Sh s.Sb s.sl s.Z fx) _ _ _
        (firstInRide Sh s.Sb s.sl s.Z) (outJ (Sh.fold s.Sb s.sl s.Z) s.G.e)
        (gfExtRide Sh s.Sb s.sl s.Z fx d) (gfErrRide Sh s.Sb s.sl s.Z fx Lst mC mS mW)
        ((s.S.sub s.kp).over A₀) (gfRide_know Sh s.Sb s.sl s.Z fx d Lst mC mS mW h h₁))
      (setR_onOut s Sh A₀))
    (onOut_keepE Sh.par.Cw.nat (Cb.Pv.Bat.R s St₀ E₀) (Cb.Pv.Bat.inJ s A₀) (Cb.Pv.Bat.outJ s A₀)
      (Cb.Pv.Bat.onOut s hZ hL hF A₀))

theorem batFoldOwn_rounds : (batFoldOwn s Sh fx St₀ E₀).shape.length = Sh.par.k + 2 := by
  show ((Cb.Pv.Bat.R s St₀ E₀).shape ++ (gfOwn Sh s.Sb s.sl s.Z fx).shape).length = _
  rw [List.length_append, Cb.Pv.Bat.rounds, gfOwn_rounds]
  omega

theorem batFoldRide_rounds : (batFoldRide s Sh fx St₀ E₀).shape.length = Sh.par.k + 2 := by
  show ((Cb.Pv.Bat.R s St₀ E₀).shape ++ ([] ++ (gfRide Sh s.Sb s.sl s.Z fx).shape)).length = _
  rw [List.length_append, List.nil_append, Cb.Pv.Bat.rounds, gfRide_rounds]
  omega

end BatFold

#print axioms firstOwn_know
#print axioms firstRide_know
#print axioms batFoldOwn_know
#print axioms batFoldRide_know

end Cb.Pv.Tower
