-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/OfLedFirst.lean: THE FIRST GROUP's twin of PointsOfLed.lean and WeightsOfLed.lean:
PointTies, the batched sumcheck's end point, StackTies and the three clauses of SlotTies on the
verifier's tables of weights, at a hearing of K4's text, for the first group's chain: from the
record LedG of the hearing's calls and ledgers (Johnson/Road/K4/OwnLedgersG.lean), which
stands in every group: the tail's tape is t0.drop (k0 g).

The statements and proofs are those of the two files, turned to the first group's letters
(Johnson/Road/K4/AtFirst.lean says which) by a program and compiled; each name bears an F.

Main names: `points_of_ledF` · `hpt_of_ledF` · `stackTies_of_ledF` · `r1_of_ledF`, `r5_of_ledF`,
`r6_of_ledF` · `sqW_of_ledF`, `g5W_of_ledF`, `g6W_of_ledF`.
Limits. As the two files': LedG; OutIs at the stages named; the typed stages' numbers of rounds; the
typed permutations; sizes; the numbering of the terms' end values; the fourth stage's claim; that
the statement's token point reads the words drawn; the two clauses on the lookup's point. Identities
on public numbers: nothing on a world, on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.AtFirst
import Johnson.Road.K4.WeightsOfLed
import Johnson.Road.K4.OwnLedgersG

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc
open Inst.Model (Scl)
open Inst.Model.FFSeg (lF lFe)
open OnBytes.Model (Fork Psc Level Tsc lastOf orderDefault orderRange powers hiTab)
open OnBytes.Model.Layer (Pub Own Heard HPlan2 Lay nEndT)
open OnBytes.Tie.Pv.Lay (OutIs ordE eDefault eRange default_perm range_perm)
open OnBytes.Desc.First.P1 (gl pscT NzT Adds7 TailM TailR tailT tapeEps drawnOf shown_some
  tsc_shown tscIn_heard tscVals)
open OnBytes.Desc.First.K4 (hearNorms_tape k0)
open Blocks (eqN)

section PointsF

variable [scl : Scl] {M X : Type} (Pf : FullFPar Cb.Gl.E M X) {R : TailR}
  (W' : TailM (tailW Pf) R) {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Model.Forest.Heard} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}
  (Ld : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
  (nz : NzT (tailW Pf) (ksOf P hp) (t0.drop (k0 g))) (a : Adds7 (tailW Pf)) (x : Pf.ofp.fs.X3)

include Ld

/-- **seven_parts' premise hPt at a hearing.** -/
theorem points_of_ledF {p1 p2 p3 p5 p6 : Psc} (O1 : OutIs gl (tailT W' (ksOf P hp) (t0.drop (k0 g))
    nz a).d1 p1)
    (O2 : OutIs gl (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d2 p2) (O3 : OutIs gl (tailT W'
        (ksOf P hp) (t0.drop (k0 g)) nz a).d3 p3)
    (O5 : OutIs gl (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d5 p5) (O6 : OutIs gl (tailT W'
        (ksOf P hp) (t0.drop (k0 g)) nz a).d6 p6)
    (k1 : (tailW Pf).s1.L.S.k = P.rd.muV) (k2 : (tailW Pf).s2.L.S.k = P.y.h.lt)
    (k3 : (tailW Pf).s3.L.S.k = P.y.h.lt) (k5 : (tailW Pf).s5.L.S.k = P.rd.muH)
    (k6 : (tailW Pf).s6.L.S.k = P.rd.muH2) (e1 : Pf.ofp.nr.sq.R.L.e = eDefault (tailW Pf).s1.L.S.k)
    (n5 : 9 ≤ (tailW Pf).s5.L.S.k) (e5 : Pf.fp.gp.e = eRange (tailW Pf).s5.L.S.k n5)
    (n6 : 9 ≤ (tailW Pf).s6.L.S.k) (e6 : Pf.fp.rt.L.e = eRange (tailW Pf).s6.L.S.k n6)
    {b sG la : ℕ} (hla : la = sG + Pf.D.lT) (s1 : P.rd.muV = Pf.D.lL + 1 + b + la)
    (s5 : P.rd.muH = Pf.D.lL + lF Pf.D - sG + la)
    (s6 : P.rd.muH2 = Pf.D.lL - 1 + lFe Pf.D - sG + la) (s2 : P.y.h.lt = Pf.D.lT)
    (hx : ∀ i : Fin Pf.D.lT, Pf.ofp.fs.pvF x i = gl.val ((drawnOf t0).getD i.val zeroE))
    (zt uz : ℕ → Cb.Gl.E) (hzt : ∀ j, j < Pf.D.lT → uz j = zt j) :
    ∀ ZV ZA ZB, lastOf o.H.wpl.r la = .ok ZV → lastOf o.hd.r la = .ok ZA →
      lastOf hd2.r la = .ok ZB →
      PointTies Pf.D (eAtF Pf.ofp Pf.wfPart ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x) zt)
        (termsEAt Pf.tp ((tailW Pf).b3 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2)
        (gatedEAt Pf.fp ((tailW Pf).b5 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2
          ((tailW Pf).b6 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2) b sG uz (pt gl
              tT.r) (pt gl tT.r)
        (pt gl ZV) (fun j => pt gl ZV (sG + j)) (pt gl o.H.PV) (pt gl o.H.tV.r) (pt gl ZA)
        (fun j => pt gl ZA (sG + j)) (pt gl ZB) (fun j => pt gl ZB (sG + j)) := by
  intro ZV ZA ZB hZV hZA hZB
  obtain ⟨v1, c1⟩ := Ld.c1
  obtain ⟨v2, c2⟩ := Ld.c2
  obtain ⟨v5, c5⟩ := Ld.c5
  obtain ⟨u1, hN, -⟩ := Ld.nt
  obtain ⟨-, -, -, -, -, -, -, -, w0, -, d0, -, ht, -, hPV, -⟩ := hearNorms_tape hN
  have hd : drawnOf t0 = d0 := by
    rw [ht]
    rfl
  have hP : H1.PV.toList = drawnOf t0 := by rw [hPV, hd]
  have q1 : (orderDefault P.rd.muV).Perm (List.range (tailW Pf).s1.L.S.k) := by
    rw [k1]
    exact default_perm _
  have q5 : (orderRange P.rd.muH).Perm (List.range (tailW Pf).s5.L.S.k) := by
    rw [k5]
    exact range_perm _ (by rw [← k5]; exact n5)
  have q6 : (orderRange P.rd.muH2).Perm (List.range (tailW Pf).s6.L.S.k) := by
    rw [k6]
    exact range_perm _ (by rw [← k6]; exact n6)
  rw [Ld.kWpl] at hZV
  rw [Ld.kPV, Ld.kTV]
  exact pointTies_atF Pf W' (ksOf P hp) (t0.drop (k0 g)) nz a x O1 O2 O3 O5 O6 k1 k2 k3 k5 k6 c1 c2
    Ld.c3 c5 Ld.c6 q1 q5 q6 (e1.trans (ordE_congr (by rw [k1]) _ q1))
    (e5.trans (ordE_congr (by rw [k5]) _ q5)) (e6.trans (ordE_congr (by rw [k6]) _ q6)) hla s1 s5
    s6 s2 s2 hZV hZA hZB hP hx zt uz hzt

/-- **seven_parts' premise hpt at a hearing.** -/
theorem hpt_of_ledF {p4 : Psc} (O4 : OutIs gl (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d4 p4)
    (k4 : kS Pf.D = hp.lamS) :
    ∀ j, j < kS Pf.D → Blocks.nat (Pf.ip.inn.Kp.outPt Pf.ip.inn.Mk
        ((tailW Pf).b4 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2) j =
      gl.val (o.K.rs.getD (kS Pf.D - 1 - j) zeroE) :=
  hpt_atF Pf W' (ksOf P hp) (t0.drop (k0 g)) nz a x O4 k4 Ld.c4

/-- **seven_parts' premise T at a hearing.** shownT: the run of shown values that the batched
sumcheck's stretch reads off its first ledger; om: the two weights of the joined claims. -/
theorem stackTies_of_ledF
    (hc : (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d4.Claim ((tailT W' (ksOf P hp) (t0.drop (k0
        g)) nz a).y4 x)) {p3 : Psc}
    (O3 : OutIs gl (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d3 p3) (k3 : (tailW Pf).s3.L.S.k =
        P.y.h.lt)
    (hnum : ∀ q : ShA Pf.D, W'.w3.num q = numA Pf.D q) {yl : Lay}
    (hN : yl.NN * yl.Lam = Pf.D.nNu) (hM : yl.LamM = Pf.D.ne) (hE : yl.h.NE = Pf.D.nx)
    (hEnd : Pf.D.nNu + Pf.D.ne + Pf.D.ne * Pf.D.nx ≤ nEndT P.y) {shownT om : Array E}
    (hsh : ((Array.range (nEndT P.y)).mapM fun i => G2.shown (tT.sEnd + i)) = some shownT)
    (hom : om = powers (tapeEps ((ksOf P hp).tc4 (t0.drop (k0 g)))) 2) {z : ℕ → Cb.Gl.E}
    (hz0 : ((tailW Pf).b4 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2.st.z = z)
    (hz3 : Pf.ip.zP ((tailW Pf).b4 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2.st .QK =
        z) :
    StackTies Pf.ip ((tailW Pf).b4 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2.st gl yl
        shownT om z
      (pt gl tT.r) := by
  obtain ⟨hlt, -⟩ := tscIn_heard Ld.c3
  have hl : (H1.ztF.toList.take P.y.h.lt).length = P.y.h.lt := by
    rw [List.length_take, Array.length_toList]
    exact Nat.min_eq_left hlt
  refine stackTies_atF Pf W' (ksOf P hp) (t0.drop (k0 g)) nz a x hc O3 k3 Ld.c3 hnum hN hM hE
    (fun n hn => ?_) ?_ hz0 hz3
  · rw [shown_at hsh (Nat.lt_of_lt_of_le hn hEnd),
      tsc_shown Ld.s1 Ld.c3 G2 Ld.l1 n (Nat.lt_of_lt_of_le hn hEnd)]
    unfold tscVals
    rw [hl]
    rfl
  · rw [hom, Desc.First.P1.powers_val gl _ 2 1 (by omega), pow_one]

end PointsF

section WeightsF

variable [scl : Scl] {M X : Type} (Pf : FullFPar Cb.Gl.E M X) {R : TailR}
  (W' : TailM (tailW Pf) R) {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Model.Forest.Heard} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}
  (Ld : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
  (nz : NzT (tailW Pf) (ksOf P hp) (t0.drop (k0 g))) (a : Adds7 (tailW Pf)) (x : Pf.ofp.fs.X3)

include Ld

/-- The squares' point. -/
theorem r1_of_ledF {p1 : Psc} (O1 : OutIs gl (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d1 p1)
    (k1 : (tailW Pf).s1.L.S.k = P.rd.muV) (e1 : Pf.ofp.nr.sq.R.L.e = eDefault (tailW Pf).s1.L.S.k)
    (zt : ℕ → Cb.Gl.E) : ∀ j, j < P.rd.muV → pt gl o.H.wpl.r j =
      (eAtF Pf.ofp Pf.wfPart ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x) zt).r1 j := by
  intro j hj
  obtain ⟨v1, c1⟩ := Ld.c1
  have q1 : (orderDefault P.rd.muV).Perm (List.range (tailW Pf).s1.L.S.k) := by
    rw [k1]
    exact default_perm _
  rw [Ld.kWpl]
  exact r1_atF Pf W' (ksOf P hp) (t0.drop (k0 g)) nz a x O1 k1 c1 q1
    (e1.trans (ordE_congr (by rw [k1]) _ q1)) zt (by rw [k1]; exact hj)

/-- The first product layer of the gated products. -/
theorem r5_of_ledF {p5 : Psc} (O5 : OutIs gl (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d5 p5)
    (k5 : (tailW Pf).s5.L.S.k = P.rd.muH) (n5 : 9 ≤ (tailW Pf).s5.L.S.k)
    (e5 : Pf.fp.gp.e = eRange (tailW Pf).s5.L.S.k n5) : ∀ j, j < P.rd.muH → pt gl o.hd.r j =
      (gatedEAt Pf.fp ((tailW Pf).b5 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2
        ((tailW Pf).b6 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2).r5 j := by
  intro j hj
  obtain ⟨v5, c5⟩ := Ld.c5
  have q5 : (orderRange P.rd.muH).Perm (List.range (tailW Pf).s5.L.S.k) := by
    rw [k5]
    exact range_perm _ (by rw [← k5]; exact n5)
  exact r5_atF Pf W' (ksOf P hp) (t0.drop (k0 g)) nz a x O5 k5 c5 q5
    (e5.trans (ordE_congr (by rw [k5]) _ q5)) (by rw [k5]; exact hj)

/-- The second product layer. -/
theorem r6_of_ledF {p6 : Psc} (O6 : OutIs gl (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d6 p6)
    (k6 : (tailW Pf).s6.L.S.k = P.rd.muH2) (n6 : 9 ≤ (tailW Pf).s6.L.S.k)
    (e6 : Pf.fp.rt.L.e = eRange (tailW Pf).s6.L.S.k n6) : ∀ j, j < P.rd.muH2 → pt gl hd2.r j =
      (gatedEAt Pf.fp ((tailW Pf).b5 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2
        ((tailW Pf).b6 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2).r6 j := by
  intro j hj
  have q6 : (orderRange P.rd.muH2).Perm (List.range (tailW Pf).s6.L.S.k) := by
    rw [k6]
    exact range_perm _ (by rw [← k6]; exact n6)
  exact r6_atF Pf W' (ksOf P hp) (t0.drop (k0 g)) nz a x O6 k6 Ld.c6 q6
    (e6.trans (ordE_congr (by rw [k6]) _ q6)) (by rw [k6]; exact hj)

/-- The clause sqW. -/
theorem sqW_of_ledF {p1 : Psc} (O1 : OutIs gl (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d1 p1)
    (k1 : (tailW Pf).s1.L.S.k = P.rd.muV) (e1 : Pf.ofp.nr.sq.R.L.e = eDefault (tailW Pf).s1.L.S.k)
    (zt : ℕ → Cb.Gl.E) {b B : ℕ} (hw : P.rd.lNI + P.y.lPd - P.y.ls = Pf.D.lL + 1 + b)
    (hm : Pf.D.lL + 1 + b ≤ P.rd.muV) (hP : P.y.Pd = 2 ^ b * P.y.S2) (hS : 0 < P.y.S2)
    (hn : Pf.D.nNu ≤ 2 ^ (Pf.D.lL + 1)) (hB : B ≤ 2 ^ b) :
    ∀ e, (hiTab o.H.wpl.r P.y.h.la (P.rd.lNI + P.y.lPd - P.y.ls)).toOption = some e →
      ∀ i kh, i < Pf.D.nNu → kh < B →
        gl.val (e.getD (i * P.y.Pd / P.y.S2 + kh) zeroE) = eqN (Pf.D.lL + 1 + b) 0
          (eAtF Pf.ofp Pf.wfPart ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x) zt).r1 (i * 2 ^
              b + kh) :=
  sqW_of hw (fun j hj => r1_of_ledF Pf W' Ld nz a x O1 k1 e1 zt j (Nat.lt_of_lt_of_le hj hm)) hP hS
    hn hB

/-- The clause g5W. -/
theorem g5W_of_ledF {p5 : Psc} (O5 : OutIs gl (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d5 p5)
    (k5 : (tailW Pf).s5.L.S.k = P.rd.muH) (n5 : 9 ≤ (tailW Pf).s5.L.S.k)
    (e5 : Pf.fp.gp.e = eRange (tailW Pf).s5.L.S.k n5) {sG : ℕ}
    (hw : P.y.h.ll + P.y.lPf - P.y.ls = Pf.D.lL + lF Pf.D - sG)
    (hm : Pf.D.lL + lF Pf.D - sG ≤ P.rd.muH) (hs : P.y.Pf / P.y.S2 = 2 ^ (lF Pf.D - sG))
    (gs : sG ≤ lF Pf.D) :
    ∀ e, (hiTab o.hd.r P.y.h.la (P.y.h.ll + P.y.lPf - P.y.ls)).toOption = some e →
      ∀ y, y < 2 ^ Pf.D.lL * 2 ^ (lF Pf.D - sG) →
        gl.val (e.getD (y / 2 ^ (lF Pf.D - sG) * (P.y.Pf / P.y.S2) + y % 2 ^ (lF Pf.D - sG))
          zeroE) = eqN (Pf.D.lL + lF Pf.D - sG) 0
            (gatedEAt Pf.fp ((tailW Pf).b5 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2
              ((tailW Pf).b6 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2).r5 y :=
  gW_of hw (fun j hj => r5_of_ledF Pf W' Ld nz a x O5 k5 n5 e5 j (Nat.lt_of_lt_of_le hj hm)) hs
    (by rw [← Nat.pow_add, Nat.add_sub_assoc gs])

/-- The clause g6W. -/
theorem g6W_of_ledF {p6 : Psc} (O6 : OutIs gl (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d6 p6)
    (k6 : (tailW Pf).s6.L.S.k = P.rd.muH2) (n6 : 9 ≤ (tailW Pf).s6.L.S.k)
    (e6 : Pf.fp.rt.L.e = eRange (tailW Pf).s6.L.S.k n6) {sG : ℕ}
    (hw : P.y.h.ll - 1 + P.y.lfe - P.y.ls = Pf.D.lL - 1 + lFe Pf.D - sG)
    (hm : Pf.D.lL - 1 + lFe Pf.D - sG ≤ P.rd.muH2) (gs : sG ≤ lFe Pf.D) :
    ∀ o2 e, o.hd2 = some o2 →
      (hiTab o2.r P.y.h.la (P.y.h.ll - 1 + P.y.lfe - P.y.ls)).toOption = some e →
      ∀ y, y < 2 ^ (Pf.D.lL - 1) * 2 ^ (lFe Pf.D - sG) →
        gl.val (e.getD (y / 2 ^ (lFe Pf.D - sG) * 2 ^ (lFe Pf.D - sG) + y % 2 ^ (lFe Pf.D - sG))
          zeroE) = eqN (Pf.D.lL - 1 + lFe Pf.D - sG) 0
            (gatedEAt Pf.fp ((tailW Pf).b5 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2
              ((tailW Pf).b6 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2).r6 y := by
  intro o2 e h2
  obtain rfl : hd2 = o2 := Option.some.inj (Ld.eHd2.symm.trans h2)
  exact gW_of hw (fun j hj => r6_of_ledF Pf W' Ld nz a x O6 k6 n6 e6 j (Nat.lt_of_lt_of_le hj hm))
    rfl (by rw [← Nat.pow_add, Nat.add_sub_assoc gs]) e

end WeightsF

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.points_of_ledF
#print axioms OnBytes.Road.K4.hpt_of_ledF
#print axioms OnBytes.Road.K4.stackTies_of_ledF
#print axioms OnBytes.Road.K4.sqW_of_ledF
#print axioms OnBytes.Road.K4.g5W_of_ledF
#print axioms OnBytes.Road.K4.g6W_of_ledF
