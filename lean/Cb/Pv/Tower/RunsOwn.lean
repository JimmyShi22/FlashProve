-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tower/RunsOwn.lean: what the verifier of a proximity test whose first fold sends its own mask
puts out, in closed form: the first stage never rejects; so the whole test rejects at its last step
alone; and the two facts on the verifier alone for such a test.

Cb/Pv/Tower/Runs.lean has the same for a test whose first fold's mask was sent earlier. Here the
first stage is `stageOwn` (Cb/Pv/Tower/Stage.lean); the further stages and the last step are as
there. All is said of typed transcripts. Definitions and proofs.
Main names:
  `foldNewOwn Y fx x τ`: the statement that a fold that sends its own mask puts out.
  `stageNewOwn`, `stageOwn_out`: the statement that the first stage puts out; it puts that out, if
    the coefficient that is left out of a round's message is one at which no check is left.
  `ownStep_out`: the first stage and a remainder: the verifier puts out the remainder's verdict
    (`TowR.course`) at the statement and the oracles at which the first stage arrives.
  `testOwn_out`: the same behind the arrangement of a group's rows.
  `ownStep_point`, `ownStep_local`, `testOwn_point`, `testOwn_local`: the oracles are strings of
    symbols; the verifier is local.
Limits: the round before a test and what is carried beside a test are not treated. Nothing on
soundness. Nothing on an honest prover.

-/
import Cb.Pv.Tower.Runs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tower
open Iop Prob Hiop IOR

section Fold
variable {E P : Type} [Field E] (Y : SumPar E P) (fx : Fin (Y.n + 1) × E)

/-- The statement that a fold that sends its own mask puts out. -/
noncomputable def foldNewOwn (x : Y.Xi) (τ : Tr Y.shapeS) : Y.Xo :=
  Y.newX x (Y.upRho τ.rho) (sClaim Y.val Y.n fx Y.k (τ.1.2 + x.1 * Y.val τ.2.1) τ.2.2)

end Fold

variable {E : Type} [Field E] [Fintype E]

section Own
variable {P P' Pw St : Type} [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P'] (Y : SumPar E P)
  (sl : Slf E St Y.Cin.J) (e : ℕ) (fx : Fin ((Y.reform sl).n + 1) × E)
  (S : LdSwD (Y.reform sl) P') (Cw : LdCode E Pw) (Pt : Type) (lf : (S.D e).Cout.NP → Pt)
  (lfW : Cw.NP → Pt)

/-- the cut and the fold -/
noncomputable abbrev cutFoldOwn :
    IOR (E × St) Y.Cin.ext (Y.reform sl).Xo (Y.reform sl).Cout.ext :=
  (cutOwn Y sl e).seq (foldOwn (Y.reform sl) fx)

theorem cutFoldOwn_out (h : fx.2 * (HVar.plain E (Y.reform sl).n).mon fx.1 = 1) (x : E × St)
    (y : Y.Cin.ext.Str) (τ : Tr (cutFoldOwn Y sl e fx).shape) :
    (cutFoldOwn Y sl e fx).out x y τ = some (foldNewOwn (Y.reform sl) fx (x.1, (x.2, x.2)) τ) :=
  ldEnt_foldS_out E P (Y.reform sl) fx h (x.1, (x.2, x.2)) y τ

/-- The statement that the first stage puts out. -/
noncomputable def stageNewOwn (x : E × St) (y : Y.Cin.ext.Str)
    (τ : Tr (stageOwn Y sl e fx S Cw Pt lf lfW).shape) : E × (S.D e).St' :=
  csNew (S.D e) Cw Pt lf lfW
    (foldNewOwn (Y.reform sl) fx (x.1, (x.2, x.2))
      (Tr.fst (s := (cutFoldOwn Y sl e fx).shape) τ))
    ((cutFoldOwn Y sl e fx).imp y (Tr.fst (s := (cutFoldOwn Y sl e fx).shape) τ))
    (Tr.snd (s := (cutFoldOwn Y sl e fx).shape) τ)

omit [Fintype P'] [Nonempty P'] in
/-- The first stage puts that out: it never rejects. -/
theorem stageOwn_out (h : fx.2 * (HVar.plain E (Y.reform sl).n).mon fx.1 = 1) (x : E × St)
    (y : Y.Cin.ext.Str) (τ : Tr (stageOwn Y sl e fx S Cw Pt lf lfW).shape) :
    (stageOwn Y sl e fx S Cw Pt lf lfW).out x y τ =
      some (stageNewOwn Y sl e fx S Cw Pt lf lfW x y τ) := by
  show ((cutFoldOwn Y sl e fx).out x y (Tr.fst (s := (cutFoldOwn Y sl e fx).shape) τ)).bind
    (fun x₂ => (csRide (S.D e) Cw Pt lf lfW).out x₂
      ((cutFoldOwn Y sl e fx).imp y (Tr.fst (s := (cutFoldOwn Y sl e fx).shape) τ))
      (Tr.snd (s := (cutFoldOwn Y sl e fx).shape) τ)) = _
  rw [cutFoldOwn_out Y sl e fx h]
  rfl

variable (d : ℕ) (Lst mC mS mW : ℕ → ℕ) (e' L : ℕ) (rest : TowR ((S.D e).jOut e') Cw.nat)

/-- The first stage and a remainder: the remainder's verdict at where the first stage arrives. -/
theorem ownStep_out (h : fx.2 * (HVar.plain E (Y.reform sl).n).mon fx.1 = 1) (hR : rest.Pick)
    (x : E × St) (y : Y.Cin.ext.Str)
    (τ : Tr (ownStep Y sl e fx S Cw Pt lf lfW d Lst mC mS mW e' L rest).R.shape) :
    (ownStep Y sl e fx S Cw Pt lf lfW d Lst mC mS mW e' L rest).R.out x y τ =
      rest.course
        (stageNewOwn Y sl e fx S Cw Pt lf lfW x y
          (Tr.fst (s := (stageOwn Y sl e fx S Cw Pt lf lfW).shape) (t := rest.toEnd.R.shape) τ))
        ((stageOwn Y sl e fx S Cw Pt lf lfW).imp y
          (Tr.fst (s := (stageOwn Y sl e fx S Cw Pt lf lfW).shape) (t := rest.toEnd.R.shape) τ))
        (Tr.snd (s := (stageOwn Y sl e fx S Cw Pt lf lfW).shape) (t := rest.toEnd.R.shape) τ) := by
  show ((stageOwn Y sl e fx S Cw Pt lf lfW).out x y
    (Tr.fst (s := (stageOwn Y sl e fx S Cw Pt lf lfW).shape) (t := rest.toEnd.R.shape) τ)).bind
      (fun x₂ => rest.toEnd.R.out x₂
        ((stageOwn Y sl e fx S Cw Pt lf lfW).imp y
          (Tr.fst (s := (stageOwn Y sl e fx S Cw Pt lf lfW).shape) (t := rest.toEnd.R.shape) τ))
        (Tr.snd (s := (stageOwn Y sl e fx S Cw Pt lf lfW).shape) (t := rest.toEnd.R.shape) τ)) = _
  rw [stageOwn_out Y sl e fx S Cw Pt lf lfW h]
  exact rest.out_course hR _ _ _

theorem ownStep_point [Fintype Pt] [DecidableEq Pt] :
    Nonempty (ownStep Y sl e fx S Cw Pt lf lfW d Lst mC mS mW e' L rest).R.shape.IsPoint :=
  (stageOwn_point Y sl e fx S Cw Pt lf lfW).elim fun p =>
    rest.toEnd_point.elim fun q => ⟨Shape.IsPoint.append p q⟩

theorem ownStep_local (h₁ : (Y.reform sl).HypK d e Lst mC mS mW) (hR₁ : (S.D e).Cout.Reads)
    (h₃ : rest.HypK) (hR : rest.Reads) :
    (ownStep Y sl e fx S Cw Pt lf lfW d Lst mC mS mW e' L rest).R.IsLocal :=
  (stageOwn_local Y sl e fx S Cw Pt lf lfW h₁.codes.1.1 h₁.codes.1.2.1 h₁.codes.1.2.2 hR₁).seq
    (rest.toEnd_local h₃ hR)

end Own

section Group
variable {B : Type} [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P] (Sh : GShape G)
  (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))
  (T : EndO (wholeJ Sh.par (Sh.form Sb sl Z) G.e))

/-- The arrangement changes no statement; the test goes on at the arranged word. -/
theorem testOwn_out (x : E × BSt Sb Z) (y : G.C.ext.Str) (τ : Tr (testOwn Sh Sb sl Z T).R.shape) :
    (testOwn Sh Sb sl Z T).R.out x y τ = T.R.out x ((arrOwn Sh Sb sl Z).imp y ()) τ := rfl

theorem testOwn_point (h : Nonempty T.R.shape.IsPoint) :
    Nonempty (testOwn Sh Sb sl Z T).R.shape.IsPoint :=
  h.elim fun p => ⟨Shape.IsPoint.append (s := (arrOwn Sh Sb sl Z).shape) () p⟩

theorem testOwn_local (h : Sh.OK) (hT : T.R.IsLocal) : (testOwn Sh Sb sl Z T).R.IsLocal :=
  (arrOwn_local Sh Sb sl Z h).seq hT

end Group

#print axioms stageOwn_out
#print axioms ownStep_out
#print axioms ownStep_local
#print axioms testOwn_local

end Cb.Pv.Tower
