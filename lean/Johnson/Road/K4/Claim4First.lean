-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Claim4First.lean: THE FIRST GROUP's twin of two statements of
Johnson/Road/K4/Claim4.lean: the claimed sum of the fourth stage (the batched sumcheck) of the first
group's typed chain is the typed target at the stage's state, and so, at a state that is tied to
what was heard, the reading of the verifier's target.

The statements and proofs are that file's, turned to the first group's letters by a program
(FullFPar for FullPar; the chain P.ownF.toOwn.tail) and compiled; each name bears an F. target4, on
which both stand, is general and is that file's own.

Main names: `cl4F` · `claim4F`.

Limits. As that file's. Nothing on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.Claim4
import Cb.Pv.Lay.At.OwnFirstW

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Finset Cb Cb.Pv.Lay Cb.Pv.Lay.At
open OnBytes.Model (Reading World Aff Fork)
open OnBytes.Road.Rows (Pub34)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW)

variable [scl : Scl] {M Xs : Type}

/-- The stage's claimed sum is the typed target at the stage's own state. -/
theorem cl4F {E : Type} [Field E] [Fintype E] (P : FullFPar E M Xs)
    (y : P.ownF.toOwn.tail.s3.Nx × E) (r : Fin 0 → E) :
    (P.ownF.toOwn.tail.s4.cl y r).1 = P.ip.inn.tg (P.ownF.toOwn.tail.s4.cl y r).2 := rfl

/-- **The fourth claim.** -/
theorem claim4F (X : Pub34 Cb.Gl.E) (hρ : X.ρ = Reading.gl)
    (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam) (P : FullFPar Cb.Gl.E M Xs)
    (hD : X.D = P.D) (htb : X.tb = P.tb) (F0 F : Fork) (w : ℕ → LW Cb.Gl.E)
    (y : P.ownF.toOwn.tail.s3.Nx × Cb.Gl.E) (r : Fin 0 → Cb.Gl.E) (st : P.ip.St)
    (hst : (P.ownF.toOwn.tail.s4.cl y r).2 = st) (t : E)
    (ht : Reading.gl.val t = (startOf X.H X.om X.parts).value Reading.gl
      (F.worldOf Reading.gl (fun _ => 0) fun _ _ _ => 0))
    (hα : X.alpha = X.H.fo.alpha) (hθ : X.theta = X.H.fo.theta)
    (hzs : st.z = zAt X.H.fo) (hkT : st.kTg = kTgAt X.H.fo F0)
    (hs : st.s = Reading.gl.val (F.vp.getD X.tT.sCl zeroE))
    (hβ : st.β = Reading.gl.val (X.om.getD 1 zeroE))
    (hf : st.o3.fin = Reading.gl.val X.tT.p.claim) (he : st.o3.eps = Reading.gl.val X.tT.p.eps)
    (hkeep : X.H.fo.cEnd.value Reading.gl (F.worldOf Reading.gl (fun _ => 0) fun _ _ _ => 0) =
      X.H.fo.cEnd.value Reading.gl (F0.worldOf Reading.gl (fun _ => 0) fun _ _ _ => 0))
    (h0 : ∀ j, X.tT.p.first ≤ j → j < X.tT.p.first + X.tT.p.walk.1.length →
      Reading.gl.val (F.vp.getD j zeroE) = 0)
    (htt : Reading.gl.val X.tT.p.target = X.tT.p.start.value Reading.gl
      (F.worldOf Reading.gl (fun _ => 0) fun _ _ _ => 0)) :
    (P.ownF.toOwn.tail.s4.cl y r).1 = Reading.gl.val t := by
  rw [cl4F, hst, ht]
  exact target4 X hρ hscl P.toMidPar hD htb F0 F w st hα hθ hzs hkT hs hβ hf he hkeep h0 htt

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.claim4F
