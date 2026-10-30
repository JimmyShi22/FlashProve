-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/AtForm.lean: THE LAW OF K10 ON VECTORS AT THE CALLER WHOSE RELATION
HOLDS THE FORM. Statements and proofs.

BatTie.lean, beside this file, says what the proved block `kBatFoldRide` puts out, and reads the
form "arranged plus the batched further weights" at the state put out. But in the relation behind
that block stands the arranged form alone. The kind `kBatFoldRideAt`
(Johnson/Top/H/BatFoldAtForm.lean) has the form as a field of its caller, and `BatFoldCaller.plus c
w` (Johnson/Top/H/BatFoldAtFormAdd.lean) is the caller c at the arranged form plus w.
  `red_any`: the reduction of `kBatFoldRideAt`'s block at any form is `batFoldRide`: the
    verifier does not read the form.
  `know_any`: the reduction `batFoldRide`, with its own errors, is knowledge sound into
    the joint at any form for which the kind at a form is.
  `plus_good`: under the conditions of `kBatFoldRide` at c, if a codeword within the joint radius of
    an arranged word is arranged, and each row's further weights are 0 off the free rows: the block
    at `c.plus (Slf.bat Z.ze fr)` has the property that a typed list of blocks asks (knowledge sound
    from the joint in front into the joint behind AT THAT FORM; point queries; local).
  `know_form`: the proved block's own reduction and errors, into the joint at any form into which
    the arrangement is knowledge sound.
  `know_plus`: so, under the premises of `plus_good`, into the joint at "arranged plus the batched
    further weights". It is the reduction of which `law_tied` (BatTie.lean) speaks, and the form
    which `law_tied`, under its own premises, reads at the state put out as `outVec` of the claim
    that the closing hands on. No theorem here joins the two.

Limits. `Reshape.Fix` at the group's arrangement and the conditions `BatFoldOKAt` are premises of
`plus_good`. Nothing on the words or the samples. No rule of composition is spent here: nothing yet
says "the prover has lost" of the description's own block. Nothing on an honest prover or on hiding.

-/
import Johnson.Desc.First.Close.Law.BatTie
import Johnson.Top.H.BatFoldAtFormAdd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold Iop IOR KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open Johnson.Top.H.ArrAdd (FreeAt)
open OnBytes.PscRun (drawnOf)

/-- The reduction at any form F is the reduction at the arranged form: `batFoldRide`. F
is a letter here: at a written form Lean's kernel would first try to show the two forms equal. -/
theorem red_any {K : Type} [Field K] [Fintype K] (s : Cb.Pv.Bat.Size K) [Nonempty s.G.P]
    (Sh : GShape s.G) (F : Slf K (Tower.BSt s.Sb s.Z) Sh.Cin.J) (fx : Fin (Sh.n + 1) × K)
    (St₀ : Type) (E₀ : ExtSpec) :
    Tower.batFoldRideAt s Sh F fx St₀ E₀ = Tower.batFoldRide s Sh fx St₀ E₀ :=
  (Tower.batFoldRideAt_anyForm s Sh F (Sh.form s.Sb s.sl s.Z) fx St₀ E₀).trans
    (Tower.batFoldRideAt_form s Sh fx St₀ E₀)

/-- **`batFoldRide` is knowledge sound into the joint at any form F** for which the kind at a
form is: with its own errors. -/
theorem know_any {K : Type} [Field K] [Fintype K] (s : Cb.Pv.Bat.Size K) [Nonempty s.G.P]
    (Sh : GShape s.G) (F : Slf K (Tower.BSt s.Sb s.Z) Sh.Cin.J) (fx : Fin (Sh.n + 1) × K)
    {St₀ : Type} {E₀ : ExtSpec} {Kc Wp : Type} (A₀ : Rels Kc St₀ E₀ ((s.S.sub s.kp).Msg × Wp))
    (d : ℕ) (Lst mC mS mW : ℕ → ℕ) (w₀ : s.S.Wit × Wp) (w₁ : LdBrW s.G s.kp Wp)
    (h : Tower.BatFoldRideKnowAt s Sh F fx A₀ d Lst mC mS mW w₀ w₁) :
    (Tower.batFoldRide s Sh fx St₀ E₀).red.Know ((Cb.Pv.Bat.inJ s A₀).keepE Sh.par.Cw.nat).on
      ((Cb.Pv.Bat.inJ s A₀).keepE Sh.par.Cw.nat).relR (Tower.batFoldOutAt s Sh F A₀).relR
      (Tower.batFoldExtRideAt s Sh F fx d w₀ w₁) (Tower.batFoldErrRide s Sh fx Lst mC mS mW) := h

/-- The block at the arranged form plus batched weights on the free rows is good. -/
theorem plus_good (c : BatFoldCaller GE) (h : BatFoldOKAt c) (hF : c.Sh.rho.Fix c.s.G.e)
    (fr : ∀ ν, Slf GE (c.s.G.RowSt c.s.Sb ν) c.Sh.Cin.J)
    (hfr : ∀ ν s j, ¬ FreeAt c.Sh j → fr ν s j = 0) :
    ((kBatFoldRideAt [c.plus (Slf.bat c.s.Z.ze fr)]).block (c.plus (Slf.bat c.s.Z.ze fr))).Good :=
  kBatFoldRideAt_good _
    (fun c' hc' => by
      rw [List.mem_singleton.1 hc']
      exact BatFoldOKAt.plus h hF (free_bat c.Sh c.s.Sb c.s.Z fr hfr))
    _ (List.mem_singleton.2 rfl)

/-- The proved block's own reduction, with its own errors, is knowledge sound into the joint at any
form F into which the arrangement is. -/
theorem know_form (c : BatFoldCaller GE) (h : BatFoldOKAt c)
    (F : Slf GE (Tower.BSt c.s.Sb c.s.Z) c.Sh.Cin.J)
    (hA : Tower.ArrRideInto c.Sh c.s.Sb c.s.sl c.s.Z F) :
    (Tower.batFoldRide c.s c.Sh c.fx c.St₀ c.E₀).red.Know
      ((Cb.Pv.Bat.inJ c.s c.A₀).keepE c.Sh.par.Cw.nat).on
      ((Cb.Pv.Bat.inJ c.s c.A₀).keepE c.Sh.par.Cw.nat).relR
      (Tower.batFoldOutAt c.s c.Sh F c.A₀).relR
      (Tower.batFoldExtRideAt c.s c.Sh F c.fx c.d c.w₀ c.w₁)
      (Tower.batFoldErrRide c.s c.Sh c.fx c.Lst c.mC c.mS c.mW) :=
  know_any c.s c.Sh F c.fx c.A₀ c.d c.Lst c.mC c.mS c.mW c.w₀ c.w₁
    (Tower.batFoldRideAt_know c.s c.Sh F c.fx c.A₀ c.d c.Lst c.mC c.mS c.mW c.w₀ c.w₁ h.z h.list
      h.fits hA (Tower.hypK_reform c.Sh.par _ F h.fold))

/-- **THE PROVED BLOCK's OWN REDUCTION IS KNOWLEDGE SOUND INTO THE JOINT AT "ARRANGED PLUS BATCHED
WEIGHTS ON THE FREE ROWS"**, with the proved block's own errors. The form is named by a letter and
an equation: at the written form Lean would first try to show it equal to the arranged one. -/
theorem know_plus (c : BatFoldCaller GE) (h : BatFoldOKAt c) (hF : c.Sh.rho.Fix c.s.G.e)
    (fr : ∀ ν, Slf GE (c.s.G.RowSt c.s.Sb ν) c.Sh.Cin.J)
    (hfr : ∀ ν s j, ¬ FreeAt c.Sh j → fr ν s j = 0)
    (F : Slf GE (Tower.BSt c.s.Sb c.s.Z) c.Sh.Cin.J)
    (hFe : F = c.Sh.form c.s.Sb c.s.sl c.s.Z + Slf.bat c.s.Z.ze fr) :
    (Tower.batFoldRide c.s c.Sh c.fx c.St₀ c.E₀).red.Know
      ((Cb.Pv.Bat.inJ c.s c.A₀).keepE c.Sh.par.Cw.nat).on
      ((Cb.Pv.Bat.inJ c.s c.A₀).keepE c.Sh.par.Cw.nat).relR
      (Tower.batFoldOutAt c.s c.Sh F c.A₀).relR
      (Tower.batFoldExtRideAt c.s c.Sh F c.fx c.d c.w₀ c.w₁)
      (Tower.batFoldErrRide c.s c.Sh c.fx c.Lst c.mC c.mS c.mW) :=
  know_form c h F (by
    rw [hFe]
    exact Johnson.Top.H.ArrAdd.arrRide_know_add c.Sh c.s.Sb c.s.sl c.s.Z _ h.shape hF
      (free_bat c.Sh c.s.Sb c.s.Z fr hfr))

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.know_form
#print axioms VerifiableInference.Desc.First.Close.know_plus
#print axioms VerifiableInference.Desc.First.Close.red_any
#print axioms VerifiableInference.Desc.First.Close.know_any
#print axioms VerifiableInference.Desc.First.Close.plus_good
