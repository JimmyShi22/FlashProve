-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/PointTiesAt.lean: the record PointTies (Johnson/Road/K4/FrontDictOf.lean) at the
last statement made from the chain's data off a tape (tailT): the points in the library's
records eAt, termsEAt and gatedEAt agree with the readings of the verifier's own points.

  `level_size`: a product layer's point has as many coordinates as the layer has variables.
  `pointTies_at`: PointTies, by pointTies_of (PointsOf.lean) from the ties of PointsAt.lean.
Limits. Premises: OutIs at five stages; the five flat functions' returns, each on its stage's tape;
that each typed stage has as many variables' rounds as its flat function; that the three typed
permutations are those of the flat functions' orders; the numbers of variables as sums of the
library's sizes; the token point's words; the tie of the lookup's token point (hzt), as it stands.
Identities on public numbers: nothing on a world, on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.PointsAt
import Johnson.Road.K4.PointsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc
open Inst.Model (Scl)
open Inst.Model.FFSeg (lF lFe)
open OnBytes.Model (Fork Psc Level Aff Tsc lastOf)
open OnBytes.Tie.Pv.Lay (OutIs ordE)
open OnBytes.Desc.First.P1 (gl Ks NzT Adds7 tailT TailM TailR levelIn_heard)

/-- A product layer's point has as many coordinates as the layer has variables. -/
theorem level_size {mu : ℕ} {rho : Array E} {C : Aff} {order : List ℕ} {F G : Fork} {t u : Tape}
    {L : Level} (h : Fl.levelIn mu rho C order F t = some (L, G, u)) : L.r.size = mu := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hr, -⟩ := levelIn_heard h
  rw [hr, levelR_size, Array.size_replicate]

variable [scl : Scl] {M X : Type} (P : FullPar Cb.Gl.E M X) {R : TailR} (W' : TailM (tailF P) R)
  (k : Ks) (t : Tape) (nz : NzT (tailF P) k t) (a : Adds7 (tailF P)) (x : P.XT)

/-- **PointTies at the chain's data off a tape.** -/
theorem pointTies_at {p1 p2 p3 p5 p6 : Psc} (O1 : OutIs gl (tailT W' k t nz a).d1 p1)
    (O2 : OutIs gl (tailT W' k t nz a).d2 p2) (O3 : OutIs gl (tailT W' k t nz a).d3 p3)
    (O5 : OutIs gl (tailT W' k t nz a).d5 p5) (O6 : OutIs gl (tailT W' k t nz a).d6 p6)
    (k1 : (tailF P).s1.L.S.k = k.k1) (k2 : (tailF P).s2.L.S.k = k.k2)
    (k3 : (tailF P).s3.L.S.k = k.k3) (k5 : (tailF P).s5.L.S.k = k.k5)
    (k6 : (tailF P).s6.L.S.k = k.k6)
    {rho1 rho5 rho6 : Array E} {C1 C5 C6 : Aff} {or1 or5 or6 : List ℕ}
    {F1 G1 F2 G2 F3 G3 F5 G5 F6 G6 : Fork} {u1 u2 u3 u5 u6 : Tape} {L1 L5 L6 : Level}
    {Pv2 Pv3 : Array E} {n2 n3 dY2 dY3 : ℕ} {o2 o3 : Tsc}
    (c1 : Fl.levelIn k.k1 rho1 C1 or1 F1 (k.tc1 t) = some (L1, G1, u1))
    (c2 : Fl.tscIn Pv2 k.k2 n2 dY2 F2 ((k.tcP t).drop 1) = some (o2, G2, u2))
    (c3 : Fl.tscIn Pv3 k.k3 n3 dY3 F3 (((k.tcP t).drop 1).drop (k.k2 + 3)) = some (o3, G3, u3))
    (c5 : Fl.levelIn k.k5 rho5 C5 or5 F5 (k.tc5 t) = some (L5, G5, u5))
    (c6 : Fl.levelIn k.k6 rho6 C6 or6 F6 (k.tc6 t) = some (L6, G6, u6))
    (q1 : or1.Perm (List.range (tailF P).s1.L.S.k))
    (q5 : or5.Perm (List.range (tailF P).s5.L.S.k))
    (q6 : or6.Perm (List.range (tailF P).s6.L.S.k))
    (e1 : P.nr.sq.R.L.e = ordE (tailF P).s1.L.S.k or1 q1)
    (e5 : P.fp.gp.e = ordE (tailF P).s5.L.S.k or5 q5)
    (e6 : P.fp.rt.L.e = ordE (tailF P).s6.L.S.k or6 q6)
    {b sG la : ℕ} (hla : la = sG + P.D.lT) (s1 : k.k1 = P.D.lL + 1 + b + la)
    (s5 : k.k5 = P.D.lL + lF P.D - sG + la) (s6 : k.k6 = P.D.lL - 1 + lFe P.D - sG + la)
    (s2 : k.k2 = P.D.lT) (s3 : k.k3 = P.D.lT) {ZV ZA ZB PV : Array E} {d0 : List E}
    (hZV : lastOf L1.r la = .ok ZV) (hZA : lastOf L5.r la = .ok ZA)
    (hZB : lastOf L6.r la = .ok ZB) (hP : PV.toList = d0)
    (hx : ∀ i : Fin P.D.lT, x.2 i = gl.val (d0.getD i.val zeroE)) (zt u : ℕ → Cb.Gl.E)
    (hzt : ∀ j, j < P.D.lT → u j = zt j) :
    PointTies P.D (eAt P.toOwnPar P.wPart ((tailT W' k t nz a).z7 x) zt)
      (termsEAt P.tp ((tailF P).b3 ((tailT W' k t nz a).z7 x)).2)
      (gatedEAt P.fp ((tailF P).b5 ((tailT W' k t nz a).z7 x)).2
        ((tailF P).b6 ((tailT W' k t nz a).z7 x)).2) b sG u (pt gl o3.r) (pt gl o3.r) (pt gl ZV)
      (fun j => pt gl ZV (sG + j)) (pt gl PV) (pt gl o2.r) (pt gl ZA)
      (fun j => pt gl ZA (sG + j)) (pt gl ZB) (fun j => pt gl ZB (sG + j)) :=
  pointTies_of hla hZV hZA hZB (by rw [level_size c1, s1]) (by rw [level_size c5, s5])
    (by rw [level_size c6, s6])
    (fun j hj => r1_at P W' k t nz a x O1 k1 c1 q1 e1 zt (by rw [k1, ← level_size c1]; exact hj))
    (fun j hj => r5_at P W' k t nz a x O5 k5 c5 q5 e5 (by rw [k5, ← level_size c5]; exact hj))
    (fun j hj => r6_at P W' k t nz a x O6 k6 c6 q6 e6 (by rw [k6, ← level_size c6]; exact hj))
    hzt (fun j hj => rt_at P W' k t nz a x O3 k3 c3 (by rw [k3, s3]; exact hj))
    (fun j hj => pV_at P W' k t nz a x hP hx zt hj)
    (fun j hj => r2_at P W' k t nz a x O2 k2 c2 zt (by rw [k2, s2]; exact hj))

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.pointTies_at
