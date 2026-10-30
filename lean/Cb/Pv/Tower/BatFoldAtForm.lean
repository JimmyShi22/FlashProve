-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tower/BatFoldAtForm.lean: the round before a proximity test, the arrangement, the cut and the
test's first fold in a row, with the cut and the fold at any form on the fold's input code, not only
at the arranged form.

Cb/Pv/Tower/First.lean lays these reductions (`gfOwn`, `gfRide`, `batFoldOwn`, `batFoldRide`) with
the cut and the fold at the batched form carried along (`GShape.form`, Cb/Ld/LdGroupFold.lean),
which is 0 on every row that holds no member's row. The round before the test, the step that sets
the fold's mask next to the group's word and the arrangement read no form. So the same reductions
are laid here with the cut and the fold at a form F that is a letter. What is asked in the place of
the arrangement's own theorem is that of Cb/Pv/Tower/TestAt.lean (`ArrOwnInto`, `ArrRideInto`).
Definitions, statements and proofs.
Main names (Sh, Sb, sl, Z, s as in Cb/Pv/Tower/First.lean; F : a form on `Sh.Cin.J`):
  `arrOwnInto_of_ride`: `ArrRideInto` gives `ArrOwnInto`. `hypK_reform`: the fold's conditions at
    one form give them at any other.
  `gfOwnAt`, `gfRideAt`: arrangement, cut, fold. `gfExtOwnAt`, `gfExtRideAt`, `gfErrOwnAt`,
    `gfErrRideAt`: extractors and errors. `gfOwnAt_know`, `gfRideAt_know`: under `ArrOwnInto` |
    `ArrRideInto` at F and the fold's conditions at F. `_point`, `_local`, `_rounds`.
  `batFoldOwnAt`, `batFoldRideAt`: the round before the test, then these beside the carried part.
    `batFoldOutAt`: the joint behind. `BatFoldOwnKnowAt`, `BatFoldRideKnowAt`: the statements.
    `batFoldOwnAt_know`, `batFoldRideAt_know`, `_rounds`.
  `_form` for each: at the arranged form it is that of Cb/Pv/Tower/First.lean, by definition.
  `foldRide_anyForm`, `cutRide_anyForm`, `gfRideAt_anyForm`, `batFoldRideAt_anyForm`: with the
    fold's mask sent earlier, the reduction at F is the reduction at any other form.
Limits: no form other than the arranged one is written here, and nothing says that a form is any
program's. `ArrOwnInto` and `ArrRideInto` are asked. That the reduction is the same at any two forms
is not proved where the fold sends its mask, nor of an extractor or of the errors. The limits of the
files named hold here. Nothing on an honest prover.

-/
import Cb.Pv.Tower.TestAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tower
open Iop Prob Hiop IOR

/-! ## Two facts on what is asked -/

section Asked
variable {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  (Sh : GShape G) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))
  (F : Slf E (BSt Sb Z) Sh.Cin.J)

/-- What is asked of the arrangement while the fold's mask is handed on gives what is asked of it
alone: the mask may be the zero word. -/
theorem arrOwnInto_of_ride (h : ArrRideInto Sh Sb sl Z F) : ArrOwnInto Sh Sb sl Z F :=
  fun a ha b w hb hw =>
    h (a.1, (a.2, fun _ _ => 0)) ha (b.1, (b.2, fun _ _ => 0)) w
      (by
        obtain rfl := Option.some.inj hb
        rfl) hw

end Asked

section Reform
variable {E P : Type} [Field E] [Fintype E] [Fintype P] (Y : SumPar E P) {St St' : Type}
  (F : Slf E St Y.Cin.J) (F' : Slf E St' Y.Cin.J)

/-- The fold's conditions read no form. -/
theorem hypK_reform {d e : ℕ} {Lst mC mS mW : ℕ → ℕ} (h : (Y.reform F).HypK d e Lst mC mS mW) :
    (Y.reform F').HypK d e Lst mC mS mW :=
  ⟨h.codes, ⟨h.errs.list, h.errs.mcaC, h.errs.mcaS, h.errs.mcaW⟩, h.inj, h.deg, h.qw⟩

end Reform

/-! ## Arrangement, cut, fold -/

section GroupFold
variable {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  (Sh : GShape G) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))
  (F : Slf E (BSt Sb Z) Sh.Cin.J) (fx : Fin ((Sh.par.reform F).n + 1) × E)

/-- Arrangement, then cut and fold at the form F; the fold sends its fresh mask. -/
noncomputable def gfOwnAt :
    IOR (E × BSt Sb Z) G.C.ext (Sh.par.reform F).Xo (Sh.par.reform F).Cout.ext :=
  (arrOwn Sh Sb sl Z).seq ((cutOwn Sh.par F G.e).seq (foldOwn (Sh.par.reform F) fx))

/-- Arrangement, then cut and fold at the form F; the fold's mask was sent earlier. -/
noncomputable def gfRideAt :
    IOR (E × BSt Sb Z) (G.C.ext.prod Sh.par.Cw.nat) (Sh.par.reform F).Xo
      (Sh.par.reform F).Cout.ext :=
  (arrRide Sh Sb sl Z).seq ((cutRide Sh.par F G.e).seq (foldRide (Sh.par.reform F) fx))

variable (d : ℕ) (Lst mC mS mW : ℕ → ℕ)

/-- The extractor of `gfOwnAt`. -/
noncomputable def gfExtOwnAt :
    (E × BSt Sb Z) × G.C.ext.Str → Tr (gfOwnAt Sh Sb sl Z F fx).shape →
      (Sh.par.reform F).Cout.N.Wit → G.C.N.Wit :=
  IOR.extSeq (arrOwn Sh Sb sl Z) ((cutOwn Sh.par F G.e).seq (foldOwn (Sh.par.reform F) fx))
    (fun _ _ w => Sh.rho.dn w)
    (IOR.extSeq (cutOwn Sh.par F G.e) (foldOwn (Sh.par.reform F) fx) (fun _ _ w => w)
      (extOwn (Sh.par.reform F) fx d 0) 0) 0

/-- The extractor of `gfRideAt`. -/
noncomputable def gfExtRideAt :
    (E × BSt Sb Z) × (G.C.ext.prod Sh.par.Cw.nat).Str → Tr (gfRideAt Sh Sb sl Z F fx).shape →
      (Sh.par.reform F).Cout.N.Wit → G.C.N.Wit :=
  IOR.extSeq (arrRide Sh Sb sl Z) ((cutRide Sh.par F G.e).seq (foldRide (Sh.par.reform F) fx))
    (fun _ _ w => Sh.rho.dn w)
    (IOR.extSeq (cutRide Sh.par F G.e) (foldRide (Sh.par.reform F) fx) (fun _ _ w => w)
      (extRide (Sh.par.reform F) fx d 0) 0) 0

/-- The errors of `gfOwnAt`: the fold's. -/
noncomputable def gfErrOwnAt : Err (gfOwnAt Sh Sb sl Z F fx).shape :=
  Err.app (s := (arrOwn Sh Sb sl Z).shape) ()
    (Err.app (s := (cutOwn Sh.par F G.e).shape) () (errOwn (Sh.par.reform F) fx Lst mC mS mW))

/-- The errors of `gfRideAt`: the fold's. -/
noncomputable def gfErrRideAt : Err (gfRideAt Sh Sb sl Z F fx).shape :=
  Err.app (s := (arrRide Sh Sb sl Z).shape) ()
    (Err.app (s := (cutRide Sh.par F G.e).shape) () (errRide (Sh.par.reform F) fx Lst mC mS mW))

/-- Arrangement, cut and fold are knowledge sound from the group's joint into the joint behind the
fold at F. -/
theorem gfOwnAt_know (hA : ArrOwnInto Sh Sb sl Z F)
    (h₁ : (Sh.par.reform F).HypK d G.e Lst mC mS mW) :
    (gfOwnAt Sh Sb sl Z F fx).red.Know (firstInOwn Sb sl Z).on (firstInOwn Sb sl Z).relR
      (outJ (Sh.par.reform F) G.e).relR (gfExtOwnAt Sh Sb sl Z F fx d)
      (gfErrOwnAt Sh Sb sl Z F fx Lst mC mS mW) :=
  know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 hA
    (know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 (cutOwn_know Sh.par F G.e)
      (foldOwn_know (Sh.par.reform F) fx d G.e Lst mC mS mW 0 h₁) fun _ _ _ _ _ => trivial)
    fun _ _ _ _ _ => trivial

/-- The same with the fold's mask sent earlier. -/
theorem gfRideAt_know (hA : ArrRideInto Sh Sb sl Z F)
    (h₁ : (Sh.par.reform F).HypK d G.e Lst mC mS mW) :
    (gfRideAt Sh Sb sl Z F fx).red.Know (firstInRide Sh Sb sl Z).on (firstInRide Sh Sb sl Z).relR
      (outJ (Sh.par.reform F) G.e).relR (gfExtRideAt Sh Sb sl Z F fx d)
      (gfErrRideAt Sh Sb sl Z F fx Lst mC mS mW) :=
  know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 hA
    (know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 (cutRide_know Sh.par F G.e)
      (foldRide_know (Sh.par.reform F) fx d G.e Lst mC mS mW 0 h₁) fun _ _ _ _ _ => trivial)
    fun _ _ _ _ _ => trivial

/-- `gfOwnAt` has k + 1 rounds. -/
theorem gfOwnAt_rounds : (gfOwnAt Sh Sb sl Z F fx).shape.length = Sh.par.k + 1 :=
  foldOwn_rounds (Sh.par.reform F) fx

/-- `gfRideAt` has k + 1 rounds. -/
theorem gfRideAt_rounds : (gfRideAt Sh Sb sl Z F fx).shape.length = Sh.par.k + 1 :=
  foldRide_rounds (Sh.par.reform F) fx

/-- Every query of the verifier of `gfOwnAt` is a point query. -/
theorem gfOwnAt_point : Nonempty (gfOwnAt Sh Sb sl Z F fx).shape.IsPoint :=
  (foldOwn_point (Sh.par.reform F) fx).elim fun q =>
    ⟨Shape.IsPoint.append (s := (arrOwn Sh Sb sl Z).shape) ()
      (Shape.IsPoint.append (s := (cutOwn Sh.par F G.e).shape) () q)⟩

/-- Every query of the verifier of `gfRideAt` is a point query. -/
theorem gfRideAt_point : Nonempty (gfRideAt Sh Sb sl Z F fx).shape.IsPoint :=
  (foldRide_point (Sh.par.reform F) fx).elim fun q =>
    ⟨Shape.IsPoint.append (s := (arrRide Sh Sb sl Z).shape) ()
      (Shape.IsPoint.append (s := (cutRide Sh.par F G.e).shape) () q)⟩

/-- The verifier of `gfOwnAt` is local. -/
theorem gfOwnAt_local (h : Sh.OK) (hC : Sh.par.C.Laws) (hZ : Sh.par.Z.Laws)
    (hW : Sh.par.Zw.Laws) : (gfOwnAt Sh Sb sl Z F fx).IsLocal :=
  (arrOwn_local Sh Sb sl Z h).seq
    ((cutOwn_local Sh.par F G.e).seq (foldOwn_local (Sh.par.reform F) fx hC hZ hW))

/-- The verifier of `gfRideAt` is local. -/
theorem gfRideAt_local (h : Sh.OK) (hC : Sh.par.C.Laws) (hZ : Sh.par.Z.Laws)
    (hW : Sh.par.Zw.Laws) : (gfRideAt Sh Sb sl Z F fx).IsLocal :=
  (arrRide_local Sh Sb sl Z h).seq
    (((cutOwn_local Sh.par F G.e).keepE Sh.par.Cw.nat).seq
      (foldRide_local (Sh.par.reform F) fx hC hZ hW))

end GroupFold

section GroupFoldForm
variable {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  (Sh : GShape G) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))
  (fx : Fin ((Sh.fold Sb sl Z).n + 1) × E) (d : ℕ) (Lst mC mS mW : ℕ → ℕ)

/-- At the arranged form they are those of Cb/Pv/Tower/First.lean. -/
theorem gfOwnAt_form : gfOwnAt Sh Sb sl Z (Sh.form Sb sl Z) fx = gfOwn Sh Sb sl Z fx := rfl

/-- The same for `gfRideAt`. -/
theorem gfRideAt_form : gfRideAt Sh Sb sl Z (Sh.form Sb sl Z) fx = gfRide Sh Sb sl Z fx := rfl

/-- The same for the extractor of `gfOwnAt`. -/
theorem gfExtOwnAt_form :
    gfExtOwnAt Sh Sb sl Z (Sh.form Sb sl Z) fx d = gfExtOwn Sh Sb sl Z fx d := rfl

/-- The same for the extractor of `gfRideAt`. -/
theorem gfExtRideAt_form :
    gfExtRideAt Sh Sb sl Z (Sh.form Sb sl Z) fx d = gfExtRide Sh Sb sl Z fx d := rfl

/-- The same for the errors of `gfOwnAt`. -/
theorem gfErrOwnAt_form :
    gfErrOwnAt Sh Sb sl Z (Sh.form Sb sl Z) fx Lst mC mS mW =
      gfErrOwn Sh Sb sl Z fx Lst mC mS mW := rfl

/-- The same for the errors of `gfRideAt`. -/
theorem gfErrRideAt_form :
    gfErrRideAt Sh Sb sl Z (Sh.form Sb sl Z) fx Lst mC mS mW =
      gfErrRide Sh Sb sl Z fx Lst mC mS mW := rfl

end GroupFoldForm

/-! ## The round before the test, then arrangement, cut and fold beside the carried part -/

section BatFold
variable {E : Type} [Field E] [Fintype E] (s : Cb.Pv.Bat.Size E) [Nonempty s.G.P]
  (Sh : GShape s.G) (F : Slf E (BSt s.Sb s.Z) Sh.Cin.J)
  (fx : Fin ((Sh.par.reform F).n + 1) × E) (St₀ : Type) (E₀ : ExtSpec)

/-- The round before the test, the arrangement, then cut and fold at F; the fold sends its mask. -/
noncomputable def batFoldOwnAt :
    IOR ((((s.B → E) × (∀ b, s.Sb b)) × St₀) × s.S.Smp) (E₀.prod s.S.ext)
      ((Sh.par.reform F).Xo × CarX s St₀) ((Sh.par.reform F).Cout.ext.prod (CarE s E₀)) :=
  (Cb.Pv.Bat.R s St₀ E₀).seq ((gfOwnAt Sh s.Sb s.sl s.Z F fx).keep (CarX s St₀) (CarE s E₀))

/-- The same; the fold's mask was sent earlier and stands behind the input's oracles. -/
noncomputable def batFoldRideAt :
    IOR ((((s.B → E) × (∀ b, s.Sb b)) × St₀) × s.S.Smp) ((E₀.prod s.S.ext).prod Sh.par.Cw.nat)
      ((Sh.par.reform F).Xo × CarX s St₀) ((Sh.par.reform F).Cout.ext.prod (CarE s E₀)) :=
  ((Cb.Pv.Bat.R s St₀ E₀).keepE Sh.par.Cw.nat).seq
    ((IOR.pure some (setR s.G.C.ext (CarE s E₀) Sh.par.Cw.nat)).seq
      ((gfRideAt Sh s.Sb s.sl s.Z F fx).keep (CarX s St₀) (CarE s E₀)))

variable {St₀ E₀} {Kc Wp : Type} (A₀ : Rels Kc St₀ E₀ ((s.S.sub s.kp).Msg × Wp))
  (d : ℕ) (Lst mC mS mW : ℕ → ℕ) (w₀ : s.S.Wit × Wp)

/-- the joint behind the fold at F, beside the carried part -/
noncomputable abbrev batFoldOutAt :
    Rels Kc ((Sh.par.reform F).Xo × CarX s St₀) ((Sh.par.reform F).Cout.ext.prod (CarE s E₀))
      ((Sh.par.reform F).Cout.N.Wit × ((s.S.sub s.kp).Wit × Wp)) :=
  (outJ (Sh.par.reform F) s.G.e).beside ((s.S.sub s.kp).over A₀)

/-- The extractor of `batFoldOwnAt`. -/
noncomputable def batFoldExtOwnAt :
    ((((s.B → E) × (∀ b, s.Sb b)) × St₀) × s.S.Smp) × (E₀.prod s.S.ext).Str →
      Tr (batFoldOwnAt s Sh F fx St₀ E₀).shape →
      (Sh.par.reform F).Cout.N.Wit × ((s.S.sub s.kp).Wit × Wp) → s.S.Wit × Wp :=
  IOR.extSeq (Cb.Pv.Bat.R s St₀ E₀)
    ((gfOwnAt Sh s.Sb s.sl s.Z F fx).keep (CarX s St₀) (CarE s E₀))
    (fun _ _ w => ldBrBack s.G s.kp Wp s.hc w)
    (fun a τ w => (gfExtOwnAt Sh s.Sb s.sl s.Z F fx d (a.1.1, a.2.1) τ w.1, w.2)) w₀

/-- The errors of `batFoldOwnAt`: the round's before the test, then the fold's. -/
noncomputable def batFoldErrOwnAt : Err (batFoldOwnAt s Sh F fx St₀ E₀).shape :=
  Err.app (s := (Cb.Pv.Bat.R s St₀ E₀).shape) (Cb.Pv.Bat.eps s)
    (gfErrOwnAt Sh s.Sb s.sl s.Z F fx Lst mC mS mW)

/-- The statement that the round before the test, arrangement, cut and fold are knowledge sound. -/
def BatFoldOwnKnowAt : Prop :=
  (batFoldOwnAt s Sh F fx St₀ E₀).red.Know (Cb.Pv.Bat.inJ s A₀).on (Cb.Pv.Bat.inJ s A₀).relR
    (batFoldOutAt s Sh F A₀).relR (batFoldExtOwnAt s Sh F fx d w₀)
    (batFoldErrOwnAt s Sh F fx Lst mC mS mW)

/-- The statement holds, under `ArrOwnInto` at F and the conditions of the round and the fold. -/
theorem batFoldOwnAt_know (hZ : s.Z.OK) (hL : s.G.C.ListAt s.G.e s.L) (hF : s.G.Fits)
    (hA : ArrOwnInto Sh s.Sb s.sl s.Z F) (h₁ : (Sh.par.reform F).HypK d s.G.e Lst mC mS mW) :
    BatFoldOwnKnowAt s Sh F fx A₀ d Lst mC mS mW w₀ :=
  know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ w₀
    (Cb.Pv.Bat.hAt s hZ hL hF Kc St₀ Wp E₀ A₀)
    (know_beside Kc _ _ _ _ _ _ (gfOwnAt Sh s.Sb s.sl s.Z F fx) _ _ _ (firstInOwn s.Sb s.sl s.Z)
      (outJ (Sh.par.reform F) s.G.e) (gfExtOwnAt Sh s.Sb s.sl s.Z F fx d)
      (gfErrOwnAt Sh s.Sb s.sl s.Z F fx Lst mC mS mW) ((s.S.sub s.kp).over A₀)
      (gfOwnAt_know Sh s.Sb s.sl s.Z F fx d Lst mC mS mW hA h₁))
    (Cb.Pv.Bat.onOut s hZ hL hF A₀)

variable (w₁ : LdBrW s.G s.kp Wp)

/-- The extractor of `batFoldRideAt`. -/
noncomputable def batFoldExtRideAt :
    ((((s.B → E) × (∀ b, s.Sb b)) × St₀) × s.S.Smp) × ((E₀.prod s.S.ext).prod Sh.par.Cw.nat).Str →
      Tr (batFoldRideAt s Sh F fx St₀ E₀).shape →
      (Sh.par.reform F).Cout.N.Wit × ((s.S.sub s.kp).Wit × Wp) → s.S.Wit × Wp :=
  IOR.extSeq ((Cb.Pv.Bat.R s St₀ E₀).keepE Sh.par.Cw.nat)
    ((IOR.pure some (setR s.G.C.ext (CarE s E₀) Sh.par.Cw.nat)).seq
      ((gfRideAt Sh s.Sb s.sl s.Z F fx).keep (CarX s St₀) (CarE s E₀)))
    (fun _ _ w => ldBrBack s.G s.kp Wp s.hc w)
    (IOR.extSeq (IOR.pure some (setR s.G.C.ext (CarE s E₀) Sh.par.Cw.nat))
      ((gfRideAt Sh s.Sb s.sl s.Z F fx).keep (CarX s St₀) (CarE s E₀)) (fun _ _ w => w)
      (fun a τ w => (gfExtRideAt Sh s.Sb s.sl s.Z F fx d (a.1.1, a.2.1) τ w.1, w.2)) w₁)
    w₀

/-- The errors of `batFoldRideAt`: the round's before the test, then the fold's. -/
noncomputable def batFoldErrRideAt : Err (batFoldRideAt s Sh F fx St₀ E₀).shape :=
  Err.app (s := (Cb.Pv.Bat.R s St₀ E₀).shape) (Cb.Pv.Bat.eps s)
    (Err.app (s := (IOR.pure some (setR s.G.C.ext (CarE s E₀) Sh.par.Cw.nat)).shape) ()
      (gfErrRideAt Sh s.Sb s.sl s.Z F fx Lst mC mS mW))

/-- The statement of the same with the fold's mask sent earlier. -/
def BatFoldRideKnowAt : Prop :=
  (batFoldRideAt s Sh F fx St₀ E₀).red.Know ((Cb.Pv.Bat.inJ s A₀).keepE Sh.par.Cw.nat).on
    ((Cb.Pv.Bat.inJ s A₀).keepE Sh.par.Cw.nat).relR (batFoldOutAt s Sh F A₀).relR
    (batFoldExtRideAt s Sh F fx d w₀ w₁) (batFoldErrRideAt s Sh F fx Lst mC mS mW)

/-- The statement holds, under `ArrRideInto` at F and the conditions of the round and the fold. -/
theorem batFoldRideAt_know (hZ : s.Z.OK) (hL : s.G.C.ListAt s.G.e s.L) (hF : s.G.Fits)
    (hA : ArrRideInto Sh s.Sb s.sl s.Z F) (h₁ : (Sh.par.reform F).HypK d s.G.e Lst mC mS mW) :
    BatFoldRideKnowAt s Sh F fx A₀ d Lst mC mS mW w₀ w₁ :=
  know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ w₀
    (know_keepE Sh.par.Cw.nat (Cb.Pv.Bat.R s St₀ E₀) (Cb.Pv.Bat.inJ s A₀) (Cb.Pv.Bat.outJ s A₀)
      (fun _ _ w => ldBrBack s.G s.kp Wp s.hc w) (Cb.Pv.Bat.eps s)
      (Cb.Pv.Bat.hAt s hZ hL hF Kc St₀ Wp E₀ A₀))
    (know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ w₁ (setR_know s Sh A₀)
      (know_beside Kc _ _ _ _ _ _ (gfRideAt Sh s.Sb s.sl s.Z F fx) _ _ _
        (firstInRide Sh s.Sb s.sl s.Z) (outJ (Sh.par.reform F) s.G.e)
        (gfExtRideAt Sh s.Sb s.sl s.Z F fx d) (gfErrRideAt Sh s.Sb s.sl s.Z F fx Lst mC mS mW)
        ((s.S.sub s.kp).over A₀) (gfRideAt_know Sh s.Sb s.sl s.Z F fx d Lst mC mS mW hA h₁))
      (setR_onOut s Sh A₀))
    (onOut_keepE Sh.par.Cw.nat (Cb.Pv.Bat.R s St₀ E₀) (Cb.Pv.Bat.inJ s A₀) (Cb.Pv.Bat.outJ s A₀)
      (Cb.Pv.Bat.onOut s hZ hL hF A₀))

/-- `batFoldOwnAt` has k + 2 rounds. -/
theorem batFoldOwnAt_rounds : (batFoldOwnAt s Sh F fx St₀ E₀).shape.length = Sh.par.k + 2 := by
  show ((Cb.Pv.Bat.R s St₀ E₀).shape ++ (gfOwnAt Sh s.Sb s.sl s.Z F fx).shape).length = _
  rw [List.length_append, Cb.Pv.Bat.rounds, gfOwnAt_rounds]
  omega

/-- `batFoldRideAt` has k + 2 rounds. -/
theorem batFoldRideAt_rounds : (batFoldRideAt s Sh F fx St₀ E₀).shape.length = Sh.par.k + 2 := by
  show ((Cb.Pv.Bat.R s St₀ E₀).shape ++ ([] ++ (gfRideAt Sh s.Sb s.sl s.Z F fx).shape)).length = _
  rw [List.length_append, List.nil_append, Cb.Pv.Bat.rounds, gfRideAt_rounds]
  omega

end BatFold

section BatFoldForm
variable {E : Type} [Field E] [Fintype E] (s : Cb.Pv.Bat.Size E) [Nonempty s.G.P]
  (Sh : GShape s.G) (fx : Fin ((Sh.fold s.Sb s.sl s.Z).n + 1) × E) (St₀ : Type) (E₀ : ExtSpec)
  {Kc Wp : Type} (A₀ : Rels Kc St₀ E₀ ((s.S.sub s.kp).Msg × Wp))
  (d : ℕ) (Lst mC mS mW : ℕ → ℕ) (w₀ : s.S.Wit × Wp) (w₁ : LdBrW s.G s.kp Wp)

/-- At the arranged form they are those of Cb/Pv/Tower/First.lean. -/
theorem batFoldOwnAt_form :
    batFoldOwnAt s Sh (Sh.form s.Sb s.sl s.Z) fx St₀ E₀ = batFoldOwn s Sh fx St₀ E₀ := rfl

/-- The same for `batFoldRideAt`. -/
theorem batFoldRideAt_form :
    batFoldRideAt s Sh (Sh.form s.Sb s.sl s.Z) fx St₀ E₀ = batFoldRide s Sh fx St₀ E₀ := rfl

/-- The same for the joint behind. -/
theorem batFoldOutAt_form :
    batFoldOutAt s Sh (Sh.form s.Sb s.sl s.Z) A₀ = batFoldOut s Sh A₀ := rfl

/-- The same for the statement on `batFoldRideAt`. -/
theorem batFoldRideKnowAt_form :
    BatFoldRideKnowAt s Sh (Sh.form s.Sb s.sl s.Z) fx A₀ d Lst mC mS mW w₀ w₁ =
      BatFoldRideKnow s Sh fx A₀ d Lst mC mS mW w₀ w₁ := rfl

/-- The same for the statement on `batFoldOwnAt`. -/
theorem batFoldOwnKnowAt_form :
    BatFoldOwnKnowAt s Sh (Sh.form s.Sb s.sl s.Z) fx A₀ d Lst mC mS mW w₀ =
      BatFoldOwnKnow s Sh fx A₀ d Lst mC mS mW w₀ := rfl

end BatFoldForm

/-! ## With the fold's mask sent earlier, the reductions are the same at any two forms -/

section AnyFormStage
variable {E P : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P] (Y : SumPar E P) {St : Type}
  (F F' : Slf E St Y.Cin.J) (fx : Fin (Y.n + 1) × E) (e : ℕ)

omit [Fintype E] [Fintype P] [Nonempty P] in
/-- The fold whose mask was sent earlier is one reduction at any two forms, by definition. -/
theorem foldRide_anyForm : foldRide (Y.reform F) fx = foldRide (Y.reform F') fx := rfl

/-- So is the cut while the fold's mask is handed on. -/
theorem cutRide_anyForm : cutRide Y F e = cutRide Y F' e := rfl

end AnyFormStage

section AnyFormGroup
variable {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  (Sh : GShape G) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))
  (F F' : Slf E (BSt Sb Z) Sh.Cin.J) (fx : Fin (Sh.n + 1) × E)

/-- So is `gfRideAt`. The two equations above are laid into the row, which spares Lean the
unfolding of the whole row. -/
theorem gfRideAt_anyForm : gfRideAt Sh Sb sl Z F fx = gfRideAt Sh Sb sl Z F' fx :=
  congrArg₂
    (fun (a : IOR (E × BSt Sb Z) (EiRide Sh.par) (Sh.par.reform F).Xi (EiRide (Sh.par.reform F)))
      (b : IOR (Sh.par.reform F).Xi (EiRide (Sh.par.reform F)) (Sh.par.reform F).Xo
        (Sh.par.reform F).Cout.ext) => (arrRide Sh Sb sl Z).seq (a.seq b))
    (cutRide_anyForm Sh.par F F' G.e) (foldRide_anyForm Sh.par F F' fx)

end AnyFormGroup

section AnyFormBat
variable {E : Type} [Field E] [Fintype E] (s : Cb.Pv.Bat.Size E) [Nonempty s.G.P]
  (Sh : GShape s.G) (F F' : Slf E (BSt s.Sb s.Z) Sh.Cin.J) (fx : Fin (Sh.n + 1) × E)
  (St₀ : Type) (E₀ : ExtSpec)

/-- So is `batFoldRideAt`: the form stands in the joint behind the block, not in the reduction. -/
theorem batFoldRideAt_anyForm :
    batFoldRideAt s Sh F fx St₀ E₀ = batFoldRideAt s Sh F' fx St₀ E₀ :=
  congrArg
    (fun g : IOR (E × BSt s.Sb s.Z) (s.G.C.ext.prod Sh.par.Cw.nat) (Sh.par.reform F).Xo
        (Sh.par.reform F).Cout.ext =>
      ((Cb.Pv.Bat.R s St₀ E₀).keepE Sh.par.Cw.nat).seq
        ((IOR.pure some (setR s.G.C.ext (CarE s E₀) Sh.par.Cw.nat)).seq
          (g.keep (CarX s St₀) (CarE s E₀))))
    (gfRideAt_anyForm Sh s.Sb s.sl s.Z F F' fx)

end AnyFormBat

end Cb.Pv.Tower
