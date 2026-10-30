-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/TenOfOut.lean: the pairs of the library's typed merge of the weight claims, at what
the merge reads of an output of the typed batched sumcheck, and the verifier's weight claims, number
by number, say the same of every matrix W.

The typed merge's letters (InnPar0.wPar, Cb/Pv/Lay/At/SeamW.lean) give claim number a the pair tenAt
of the piece num a, at the points that st7 reads of the batched sumcheck's output: the lookup's
point (one of two letters, by the panel's call), the end point of the sumcheck of the terms and the
batched sumcheck's own end point. Under StackTies (Johnson/Road/K4/StackTyped.lean) the first three
are the letters z and zh of SigFits; the fourth reads the verifier's challenges turned round, which
is all that SigFits asks of its letter (sig_zeta). So ten_of_placed (Johnson/Road/K4/TenOfPan.lean)
applies.

`ten_of_out`: claim number a of the verifier's list is there, and on every W it is worth what the
typed merge's pair number a is worth.

Limits. Premises: StackTies at the output's state; SigFits at its letters z, zh; the end point's
reading; the verifier's lists of panels and claims have returned; room for all units; the pieces'
layers are layers of the model; the typed numbering num is numK's (hnum). An identity on public data
and any matrix W: nothing on which matrix is committed, on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.TenOfPan
import Johnson.Road.K4.StackTyped
import Cb.Pv.Lay.At.SeamW

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model.Layout (units off)
open Inst.Model.Layout.Tensor (matOf)
open OnBytes.Model (Reading World WsShape WsClaim)
open OnBytes.Model.Layer (Lay Panels PanelEnv ClaimEnv panelsA panelsT)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Cell Rd)

variable {K : Type} [Field K] [Fintype K] [scl : Scl] {ρ : Reading K}

/-- **The typed merge's pairs against the verifier's claims, number by number.** -/
theorem ten_of_out (P : InnPar0 K) (k hW n : ℕ) (Wn : (P.J → K) → ℕ → ℕ → K)
    (num : Fin n ≃ Piece P.D) (wAt : PIdx (ldPartFmt K k (fun _ => 2) ++ [pDummy K 1]) → P.J)
    (cAt : P.J) (o4 : P.inn.toSum.T.par.Out) {y : Lay} {sh om : Array E} {z zh : ℕ → K}
    (T : StackTies P o4.st ρ y sh om z zh) {Wo : World K} {p : PanelEnv} {c : ClaimEnv}
    {h : OnBytes.Model.Layer.Shape} {pc : List (List String)} {s : WsShape} {cc : Cells K}
    {t : Cell → K} {low ζ0 : ℕ → K}
    (S : SigFits ρ Wo p c h pc s P.D k P.L0 cc t low z zh ζ0 P.tb)
    (hpt : ∀ j, j < kS P.D → Blocks.nat (P.inn.Kp.outPt P.inn.Mk o4) j =
      ρ.val (c.rs.getD (kS P.D - 1 - j) zeroE))
    (r : Rd K) (hH : off k (units P.D.P) (units P.D.P).length ≤ hW) {TS : List ℕ}
    (hTS : TS = [0, 1, 2, 5]) {pans' : Panels} {cl : List WsClaim}
    (hp : panelsT p TS (panelsA p {}) = some pans') (hc : c.weightClaims TS = some cl)
    (hL : ∀ x : Piece P.D, P.L0 + layerOfRow x.1.1 x.2 < P.D.P.layers)
    (hnum : ∀ a : Fin n, ((numK P.D).symm (num a)).val = a.val) (a : Fin n) :
    ∃ c0, cl[a.val]? = some c0 ∧ ∀ W : Wm K,
      tval ((P.wPar k hW n Wn num wAt cAt).ten a (P.st7 num o4)) (matOf W) =
        claimVal ρ c.wsLay W c0 := by
  have S' : SigFits ρ Wo p c h pc s P.D k P.L0 cc t low z zh
      (Blocks.nat (P.inn.Kp.outPt P.inn.Mk o4)) P.tb :=
    sig_zeta S fun j hj => by
      have e := hpt j (by rw [kS_eq]; exact hj)
      rw [kS_eq] at e
      exact e
  obtain ⟨c0, e0, q⟩ := ten_of_placed S' r hH hTS hp hc hL (num a)
  rw [hnum a] at e0
  refine ⟨c0, e0, fun W => ?_⟩
  have z3 : o4.st.o3.st = z := T.z3
  show tval (tenAt P.D P.tb P.L0 k hW (if (num a).1.1.late then o4.st.o3.st else o4.st.z)
    (P.rt o4.st) (Blocks.nat (P.inn.Kp.outPt P.inn.Mk o4)) (num a).1.1 (num a).2) (matOf W) = _
  rw [z3, T.z0, T.rt, ite_self]
  exact q W

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.ten_of_out
