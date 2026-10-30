-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/WeightsOfLed.lean: the three clauses of SlotTies (Johnson/Road/K4/FrontDictOf.lean)
on the verifier's tables of weights, sqW, g5W and g6W, at a hearing of K4's text in a group that is
not the first: from the record Led7 (Johnson/Road/K4/OwnLedgers.lean), OutIs and sizes.

  `r1_of_led`, `r5_of_led`, `r6_of_led`: the three product layers' points, read, are the library's
    records' points, coordinate by coordinate (r1_at, r5_at, r6_at of Johnson/Road/K4/PointsAt.lean
    at Led7's calls).
  `sqW_of_led`, `g5W_of_led`, `g6W_of_led`: the three clauses, by sqW_of and gW_of
    (Johnson/Road/K4/PointsOf.lean).
Limits. Premises: Led7; OutIs at the three stages; that each typed stage has as many variables'
rounds as the plan says; that the typed permutations are eDefault and eRange; sizes.
A group that is not the first. Identities on public numbers: nothing on a world, on a draw, on
soundness or on hiding.


-/
import Johnson.Road.K4.PointsOfLed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc
open Inst.Model (Scl)
open Inst.Model.FFSeg (lF lFe)
open OnBytes.Model (Fork Psc Level Tsc orderDefault orderRange hiTab)
open OnBytes.Model.Layer (Pub Own Heard HPlan2)
open OnBytes.Tie.Pv.Lay (OutIs ordE eDefault eRange default_perm range_perm)
open OnBytes.Desc.First.P1 (gl NzT Adds7 TailM TailR)
open Blocks (eqN)

variable [scl : Scl] {M X : Type} (Pf : FullPar Cb.Gl.E M X) {R : TailR}
  (W' : TailM (tailF Pf) R) {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Model.Forest.Heard} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}
  (Ld : Led7 P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
  (nz : NzT (tailF Pf) (ksOf P hp) (t0.drop 1)) (a : Adds7 (tailF Pf)) (x : Pf.XT)

include Ld

/-- The squares' point. -/
theorem r1_of_led {p1 : Psc} (O1 : OutIs gl (k4Tail W' P hp t0 nz a).d1 p1)
    (k1 : (tailF Pf).s1.L.S.k = P.rd.muV) (e1 : Pf.nr.sq.R.L.e = eDefault (tailF Pf).s1.L.S.k)
    (zt : ℕ → Cb.Gl.E) : ∀ j, j < P.rd.muV → pt gl o.H.wpl.r j =
      (eAt Pf.toOwnPar Pf.wPart ((k4Tail W' P hp t0 nz a).z7 x) zt).r1 j := by
  intro j hj
  obtain ⟨v1, c1⟩ := Ld.c1
  have q1 : (orderDefault P.rd.muV).Perm (List.range (tailF Pf).s1.L.S.k) := by
    rw [k1]
    exact default_perm _
  rw [Ld.kWpl]
  exact r1_at Pf W' (ksOf P hp) (t0.drop 1) nz a x O1 k1 c1 q1
    (e1.trans (ordE_congr (by rw [k1]) _ q1)) zt (by rw [k1]; exact hj)

/-- The first product layer of the gated products. -/
theorem r5_of_led {p5 : Psc} (O5 : OutIs gl (k4Tail W' P hp t0 nz a).d5 p5)
    (k5 : (tailF Pf).s5.L.S.k = P.rd.muH) (n5 : 9 ≤ (tailF Pf).s5.L.S.k)
    (e5 : Pf.fp.gp.e = eRange (tailF Pf).s5.L.S.k n5) : ∀ j, j < P.rd.muH → pt gl o.hd.r j =
      (gatedEAt Pf.fp ((tailF Pf).b5 ((k4Tail W' P hp t0 nz a).z7 x)).2
        ((tailF Pf).b6 ((k4Tail W' P hp t0 nz a).z7 x)).2).r5 j := by
  intro j hj
  obtain ⟨v5, c5⟩ := Ld.c5
  have q5 : (orderRange P.rd.muH).Perm (List.range (tailF Pf).s5.L.S.k) := by
    rw [k5]
    exact range_perm _ (by rw [← k5]; exact n5)
  exact r5_at Pf W' (ksOf P hp) (t0.drop 1) nz a x O5 k5 c5 q5
    (e5.trans (ordE_congr (by rw [k5]) _ q5)) (by rw [k5]; exact hj)

/-- The second product layer. -/
theorem r6_of_led {p6 : Psc} (O6 : OutIs gl (k4Tail W' P hp t0 nz a).d6 p6)
    (k6 : (tailF Pf).s6.L.S.k = P.rd.muH2) (n6 : 9 ≤ (tailF Pf).s6.L.S.k)
    (e6 : Pf.fp.rt.L.e = eRange (tailF Pf).s6.L.S.k n6) : ∀ j, j < P.rd.muH2 → pt gl hd2.r j =
      (gatedEAt Pf.fp ((tailF Pf).b5 ((k4Tail W' P hp t0 nz a).z7 x)).2
        ((tailF Pf).b6 ((k4Tail W' P hp t0 nz a).z7 x)).2).r6 j := by
  intro j hj
  have q6 : (orderRange P.rd.muH2).Perm (List.range (tailF Pf).s6.L.S.k) := by
    rw [k6]
    exact range_perm _ (by rw [← k6]; exact n6)
  exact r6_at Pf W' (ksOf P hp) (t0.drop 1) nz a x O6 k6 Ld.c6 q6
    (e6.trans (ordE_congr (by rw [k6]) _ q6)) (by rw [k6]; exact hj)

/-- The clause sqW. -/
theorem sqW_of_led {p1 : Psc} (O1 : OutIs gl (k4Tail W' P hp t0 nz a).d1 p1)
    (k1 : (tailF Pf).s1.L.S.k = P.rd.muV) (e1 : Pf.nr.sq.R.L.e = eDefault (tailF Pf).s1.L.S.k)
    (zt : ℕ → Cb.Gl.E) {b B : ℕ} (hw : P.rd.lNI + P.y.lPd - P.y.ls = Pf.D.lL + 1 + b)
    (hm : Pf.D.lL + 1 + b ≤ P.rd.muV) (hP : P.y.Pd = 2 ^ b * P.y.S2) (hS : 0 < P.y.S2)
    (hn : Pf.D.nNu ≤ 2 ^ (Pf.D.lL + 1)) (hB : B ≤ 2 ^ b) :
    ∀ e, (hiTab o.H.wpl.r P.y.h.la (P.rd.lNI + P.y.lPd - P.y.ls)).toOption = some e →
      ∀ i kh, i < Pf.D.nNu → kh < B →
        gl.val (e.getD (i * P.y.Pd / P.y.S2 + kh) zeroE) = eqN (Pf.D.lL + 1 + b) 0
          (eAt Pf.toOwnPar Pf.wPart ((k4Tail W' P hp t0 nz a).z7 x) zt).r1 (i * 2 ^ b + kh) :=
  sqW_of hw (fun j hj => r1_of_led Pf W' Ld nz a x O1 k1 e1 zt j (Nat.lt_of_lt_of_le hj hm)) hP hS
    hn hB

/-- The clause g5W. -/
theorem g5W_of_led {p5 : Psc} (O5 : OutIs gl (k4Tail W' P hp t0 nz a).d5 p5)
    (k5 : (tailF Pf).s5.L.S.k = P.rd.muH) (n5 : 9 ≤ (tailF Pf).s5.L.S.k)
    (e5 : Pf.fp.gp.e = eRange (tailF Pf).s5.L.S.k n5) {sG : ℕ}
    (hw : P.y.h.ll + P.y.lPf - P.y.ls = Pf.D.lL + lF Pf.D - sG)
    (hm : Pf.D.lL + lF Pf.D - sG ≤ P.rd.muH) (hs : P.y.Pf / P.y.S2 = 2 ^ (lF Pf.D - sG))
    (gs : sG ≤ lF Pf.D) :
    ∀ e, (hiTab o.hd.r P.y.h.la (P.y.h.ll + P.y.lPf - P.y.ls)).toOption = some e →
      ∀ y, y < 2 ^ Pf.D.lL * 2 ^ (lF Pf.D - sG) →
        gl.val (e.getD (y / 2 ^ (lF Pf.D - sG) * (P.y.Pf / P.y.S2) + y % 2 ^ (lF Pf.D - sG))
          zeroE) = eqN (Pf.D.lL + lF Pf.D - sG) 0
            (gatedEAt Pf.fp ((tailF Pf).b5 ((k4Tail W' P hp t0 nz a).z7 x)).2
              ((tailF Pf).b6 ((k4Tail W' P hp t0 nz a).z7 x)).2).r5 y :=
  gW_of hw (fun j hj => r5_of_led Pf W' Ld nz a x O5 k5 n5 e5 j (Nat.lt_of_lt_of_le hj hm)) hs
    (by rw [← Nat.pow_add, Nat.add_sub_assoc gs])

/-- The clause g6W. -/
theorem g6W_of_led {p6 : Psc} (O6 : OutIs gl (k4Tail W' P hp t0 nz a).d6 p6)
    (k6 : (tailF Pf).s6.L.S.k = P.rd.muH2) (n6 : 9 ≤ (tailF Pf).s6.L.S.k)
    (e6 : Pf.fp.rt.L.e = eRange (tailF Pf).s6.L.S.k n6) {sG : ℕ}
    (hw : P.y.h.ll - 1 + P.y.lfe - P.y.ls = Pf.D.lL - 1 + lFe Pf.D - sG)
    (hm : Pf.D.lL - 1 + lFe Pf.D - sG ≤ P.rd.muH2) (gs : sG ≤ lFe Pf.D) :
    ∀ o2 e, o.hd2 = some o2 →
      (hiTab o2.r P.y.h.la (P.y.h.ll - 1 + P.y.lfe - P.y.ls)).toOption = some e →
      ∀ y, y < 2 ^ (Pf.D.lL - 1) * 2 ^ (lFe Pf.D - sG) →
        gl.val (e.getD (y / 2 ^ (lFe Pf.D - sG) * 2 ^ (lFe Pf.D - sG) + y % 2 ^ (lFe Pf.D - sG))
          zeroE) = eqN (Pf.D.lL - 1 + lFe Pf.D - sG) 0
            (gatedEAt Pf.fp ((tailF Pf).b5 ((k4Tail W' P hp t0 nz a).z7 x)).2
              ((tailF Pf).b6 ((k4Tail W' P hp t0 nz a).z7 x)).2).r6 y := by
  intro o2 e h2
  obtain rfl : hd2 = o2 := Option.some.inj (Ld.eHd2.symm.trans h2)
  exact gW_of hw (fun j hj => r6_of_led Pf W' Ld nz a x O6 k6 n6 e6 j (Nat.lt_of_lt_of_le hj hm))
    rfl (by rw [← Nat.pow_add, Nat.add_sub_assoc gs]) e

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.sqW_of_led
#print axioms OnBytes.Road.K4.g5W_of_led
#print axioms OnBytes.Road.K4.g6W_of_led
