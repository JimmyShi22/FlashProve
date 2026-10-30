-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tower/Runs.lean: what the verifier of a proximity test puts out, in closed form: a stage puts
out a new statement and never rejects; so a whole test rejects at its last step alone, at the
statement and the oracles at which the stages arrive.

Cb/Pv/Tower/Fold.lean, Cs.lean and Base.lean have the verifiers of a fold, of a code switch and of
the last step in closed form. This file joins them: along a stage (Cb/Pv/Tower/Stage.lean), along
the stages of a test (`TowR`, Cb/Pv/Tower/Test.lean), and behind the arrangement of a group's rows
(Cb/Pv/Tower/First.lean). All is said of typed transcripts. A transcript in another form is read
through a map to the typed one; nothing on such a map is here. Definitions and proofs.
Main names:
  `csNew D x y τ`: the statement that a code switch puts out. `csRide_out`: it puts that out.
  `foldNew Y fx x τ`: the statement that a fold whose mask was sent earlier puts out.
  `stageNew`, `stageRide_out`: the statement that a stage puts out, from the statement before it,
    the oracles before it and the stage's transcript; the stage puts that out, if the coefficient
    that is left out of a round's message is one at which no check is left (`fx.2` is an inverse of
    the "sum" of that power).
  `TowR.Pick`: that premise at every stage. `TowR.course`: the last step's verdict at the statement
    and oracles at which the stages arrive. `TowR.out_course`: under `Pick` the test's verifier puts
    out just that.
  `testRide_out`: the same behind the arrangement.
Limits: the stage whose fold sends its own mask, the round before a test and what is carried beside
a test are not treated. Nothing on soundness. Nothing on an honest prover.

-/
import Cb.Pv.Tower.Test

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tower
open Iop Prob Hiop IOR

/-! ## The blocks -/

section Cs
variable {E P P' Pw St : Type} [Field E] [Fintype P] [Nonempty P] (D : LdSw E P P' St)
  (Cw : LdCode E Pw) (Pt : Type) (lf : D.Cout.NP → Pt) (lfW : Cw.NP → Pt)

/-- The statement that a code switch puts out: the library's new target and new state. -/
noncomputable def csNew (x : E × St) (y : D.Cin.Word) (τ : Tr (D.shC Cw Pt lf lfW)) : E × D.St' :=
  (D.W.tgt' x.1 τ.2.2.1.2 (D.Cin.T y) τ.2.2.2.1, (D.stOf x.2 τ.2.1 τ.2.2.2.1.1, τ.2.2.2.1.2))

theorem csRide_out (x : E × St) (y : D.Cin.Word) (τ : Tr (D.shC Cw Pt lf lfW)) :
    (csRide D Cw Pt lf lfW).out x y τ = some (csNew D Cw Pt lf lfW x y τ) := rfl

end Cs

section Fold
variable {E P : Type} [Field E] (Y : SumPar E P) (fx : Fin (Y.n + 1) × E)

/-- The statement that a fold whose mask was sent earlier puts out. -/
noncomputable def foldNew (x : Y.Xi) (τ : Tr Y.shapeR) : Y.Xo :=
  Y.newX x (Y.upRhoR τ.rho) (sClaim Y.val Y.n fx Y.k (τ.1.2 + x.1 * Y.val τ.2.1) τ.2.2)

end Fold

/-! ## A stage -/

section Stage
variable {E P P' Pw St : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P] [Fintype P']
  [Nonempty P'] (Y : SumPar E P) (sl : Slf E St Y.Cin.J) (e : ℕ)
  (fx : Fin ((Y.reform sl).n + 1) × E) (S : LdSwD (Y.reform sl) P') (Cw : LdCode E Pw) (Pt : Type)
  (lf : (S.D e).Cout.NP → Pt) (lfW : Cw.NP → Pt)

/-- the cut and the fold -/
noncomputable abbrev cutFold : IOR (E × St) (EiRide Y) (Y.reform sl).Xo (Y.reform sl).Cout.ext :=
  (cutRide Y sl e).seq (foldRide (Y.reform sl) fx)

theorem cutFold_out (h : fx.2 * (HVar.plain E (Y.reform sl).n).mon fx.1 = 1) (x : E × St)
    (y : (EiRide Y).Str) (τ : Tr (cutFold Y sl e fx).shape) :
    (cutFold Y sl e fx).out x y τ = some (foldNew (Y.reform sl) fx (x.1, (x.2, x.2)) τ) :=
  foldRide_out (Y.reform sl) fx h (x.1, (x.2, x.2)) y τ

/-- The statement that a stage puts out. -/
noncomputable def stageNew (x : E × St) (y : (EiRide Y).Str)
    (τ : Tr (stageRide Y sl e fx S Cw Pt lf lfW).shape) : E × (S.D e).St' :=
  csNew (S.D e) Cw Pt lf lfW
    (foldNew (Y.reform sl) fx (x.1, (x.2, x.2)) (Tr.fst (s := (cutFold Y sl e fx).shape) τ))
    ((cutFold Y sl e fx).imp y (Tr.fst (s := (cutFold Y sl e fx).shape) τ))
    (Tr.snd (s := (cutFold Y sl e fx).shape) τ)

omit [Fintype P'] [Nonempty P'] in
/-- A stage puts that out: it never rejects. -/
theorem stageRide_out (h : fx.2 * (HVar.plain E (Y.reform sl).n).mon fx.1 = 1) (x : E × St)
    (y : (EiRide Y).Str) (τ : Tr (stageRide Y sl e fx S Cw Pt lf lfW).shape) :
    (stageRide Y sl e fx S Cw Pt lf lfW).out x y τ =
      some (stageNew Y sl e fx S Cw Pt lf lfW x y τ) := by
  show ((cutFold Y sl e fx).out x y (Tr.fst (s := (cutFold Y sl e fx).shape) τ)).bind
    (fun x₂ => (csRide (S.D e) Cw Pt lf lfW).out x₂
      ((cutFold Y sl e fx).imp y (Tr.fst (s := (cutFold Y sl e fx).shape) τ))
      (Tr.snd (s := (cutFold Y sl e fx).shape) τ)) = _
  rw [cutFold_out Y sl e fx h]
  rfl

end Stage

/-! ## The stages in a row -/

namespace TowR
variable {E : Type} [Field E] [Fintype E]

/-- At every stage the coefficient that is left out is one at which no check is left. -/
def Pick : {a : LdJoint E} → {Fx : ExtSpec} → TowR a Fx → Prop
  | _, _, .base .. => True
  | _, _, @TowR.step _ _ _ _ _ _ _ _ _ _ _ Y sl _ fx _ _ _ _ _ _ _ _ _ _ _ _ _ _ rest =>
      fx.2 * (HVar.plain E (Y.reform sl).n).mon fx.1 = 1 ∧ rest.Pick

/-- The last step's verdict, at the statement and the oracles at which the stages arrive. -/
noncomputable def course : {a : LdJoint E} → {Fx : ExtSpec} → (T : TowR a Fx) → a.X →
    (a.C.ext.prod Fx).Str → Tr T.toEnd.R.shape → Option Unit
  | _, _, .base a t cov _ _ _, x, y, τ => (baseRide a t cov).out x y τ
  | _, _, @TowR.step _ _ _ _ _ _ _ _ _ _ _
      Y sl e fx S Cw Pt _ _ lf lfW _ _ _ _ _ _ _ rest, x, y, τ =>
      rest.course
        (stageNew Y sl e fx S Cw Pt lf lfW x y
          (Tr.fst (s := (stageRide Y sl e fx S Cw Pt lf lfW).shape) (t := rest.toEnd.R.shape) τ))
        ((stageRide Y sl e fx S Cw Pt lf lfW).imp y
          (Tr.fst (s := (stageRide Y sl e fx S Cw Pt lf lfW).shape) (t := rest.toEnd.R.shape) τ))
        (Tr.snd (s := (stageRide Y sl e fx S Cw Pt lf lfW).shape) (t := rest.toEnd.R.shape) τ)

/-- Under `Pick` the test's verifier puts out the last step's verdict at where the stages arrive. -/
theorem out_course : {a : LdJoint E} → {Fx : ExtSpec} → (T : TowR a Fx) → T.Pick → ∀ x y τ,
    T.toEnd.R.out x y τ = T.course x y τ
  | _, _, .base _ _ _ _ _ _, _, _, _, _ => rfl
  | _, _, @TowR.step _ _ _ _ _ _ _ _ _ _ _
      Y sl e fx S Cw Pt _ _ lf lfW _ _ _ _ _ _ _ rest, h, x, y, τ => by
      show ((stageRide Y sl e fx S Cw Pt lf lfW).out x y
        (Tr.fst (s := (stageRide Y sl e fx S Cw Pt lf lfW).shape) (t := rest.toEnd.R.shape)
          τ)).bind (fun x₂ => rest.toEnd.R.out x₂
            ((stageRide Y sl e fx S Cw Pt lf lfW).imp y
              (Tr.fst (s := (stageRide Y sl e fx S Cw Pt lf lfW).shape)
                (t := rest.toEnd.R.shape) τ))
            (Tr.snd (s := (stageRide Y sl e fx S Cw Pt lf lfW).shape)
              (t := rest.toEnd.R.shape) τ)) = _
      rw [stageRide_out Y sl e fx S Cw Pt lf lfW h.1]
      exact rest.out_course h.2 _ _ _

end TowR

/-! ## Behind the arrangement -/

section Group
variable {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  (Sh : GShape G) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))

/-- The arrangement changes no statement; the test goes on at the arranged word. -/
theorem testRide_out (T : TowR (wholeJ Sh.par (Sh.form Sb sl Z) G.e) Sh.par.Cw.nat) (h : T.Pick)
    (x : E × BSt Sb Z) (y : (G.C.ext.prod Sh.par.Cw.nat).Str)
    (τ : Tr (testRide Sh Sb sl Z T).R.shape) :
    (testRide Sh Sb sl Z T).R.out x y τ = T.course x ((arrRide Sh Sb sl Z).imp y ()) τ :=
  T.out_course h x ((arrRide Sh Sb sl Z).imp y ()) τ

end Group

#print axioms stageRide_out
#print axioms TowR.out_course
#print axioms testRide_out

end Cb.Pv.Tower
