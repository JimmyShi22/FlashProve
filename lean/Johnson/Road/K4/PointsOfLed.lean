-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/PointsOfLed.lean: three premises of seven_parts (Johnson/Road/K4/SevenParts.lean),
PointTies, the batched sumcheck's end point and StackTies, at a hearing of K4's text in a group that
is not the first: from the record Led7 of the hearing's calls and ledgers
(Johnson/Road/K4/OwnLedgers.lean) and the typed outputs' record OutIs.

Johnson/Road/K4/PointTiesAt.lean, StackPointAt.lean and StackTiesAt.lean have these at the chain's
data off any tape, each asking the flat function's return on its stage's tape. Led7 holds these
returns at K4's tape. Here they are laid in.

Main names:
  `ordE_congr`: the permutation of a list does not look at how the list is written.
  `shown_at`: a member of a run of shown values.
  `points_of_led`: seven_parts' premise hPt, in the hearing's own letters.
  `hpt_of_led`: its premise hpt.
  `stackTies_of_led`: its premise T.
Limits. Premises: Led7; OutIs at the stages named; that each typed stage has as many variables'
rounds as the plan says; that the three typed permutations are eDefault and eRange; the
plan's numbers as sums of the library's sizes; the numbering of the terms' end values; the fourth
stage's claim; that the statement's token point reads the words drawn; the two clauses on the
lookup's point as they stand. A group that is not the first. Identities on public numbers: nothing
on a world, on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.PointTiesAt
import Johnson.Road.K4.StackPointAt
import Johnson.Road.K4.StackTiesAt
import Johnson.Road.K4.OwnLedgers
import Johnson.Road.K4.OwnJoint
import OnBytes.Desc.First.P1.BatchPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc
open Inst.Model (Scl)
open Inst.Model.FFSeg (lF lFe)
open OnBytes.Model (Fork Psc Level Tsc lastOf orderDefault orderRange powers)
open OnBytes.Model.Layer (Pub Own Heard HPlan2 Lay nEndT)
open OnBytes.Tie.Pv.Lay (OutIs ordE eDefault eRange default_perm range_perm)
open OnBytes.Desc.First.P1 (gl pscT NzT Adds7 TailM TailR tapeEps drawnOf shown_some tsc_shown
  tscIn_heard tscVals)
open OnBytes.Desc.First.K4 (hearNorms_tape)

/-- The permutation of a list does not look at how the list is written. -/
theorem ordE_congr {mu : ℕ} {or or' : List ℕ} (e : or = or') (h : or.Perm (List.range mu))
    (h' : or'.Perm (List.range mu)) : ordE mu or h = ordE mu or' h' := by
  subst e
  rfl

/-- A member of a run of shown values. -/
theorem shown_at {F : Fork} {s n : ℕ} {r : Array E}
    (h : ((Array.range n).mapM fun i => F.shown (s + i)) = some r) {i : ℕ} (hi : i < n) :
    r.getD i zeroE = F.vp.getD (s + i) zeroE := by
  rw [Array.mapM_eq_mapM_toList] at h
  obtain ⟨ys, hl, e⟩ := map_some h
  subst e
  have hl' : ((List.range n).mapM fun i => F.shown (s + i)) = some ys := by simpa using hl
  obtain ⟨b, hb, hg⟩ := Desc.First.K4.mapM_range_get _ hl' hi
  rw [getD_toList, List.getD_eq_getElem?_getD]
  show (ys[i]?).getD zeroE = _
  rw [hg]
  exact (shown_some hb).2.2

variable [scl : Scl] {M X : Type} (Pf : FullPar Cb.Gl.E M X) {R : TailR}
  (W' : TailM (tailF Pf) R) {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Model.Forest.Heard} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}
  (Ld : Led7 P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
  (nz : NzT (tailF Pf) (ksOf P hp) (t0.drop 1)) (a : Adds7 (tailF Pf)) (x : Pf.XT)

include Ld

/-- **seven_parts' premise hPt at a hearing.** -/
theorem points_of_led {p1 p2 p3 p5 p6 : Psc} (O1 : OutIs gl (k4Tail W' P hp t0 nz a).d1 p1)
    (O2 : OutIs gl (k4Tail W' P hp t0 nz a).d2 p2) (O3 : OutIs gl (k4Tail W' P hp t0 nz a).d3 p3)
    (O5 : OutIs gl (k4Tail W' P hp t0 nz a).d5 p5) (O6 : OutIs gl (k4Tail W' P hp t0 nz a).d6 p6)
    (k1 : (tailF Pf).s1.L.S.k = P.rd.muV) (k2 : (tailF Pf).s2.L.S.k = P.y.h.lt)
    (k3 : (tailF Pf).s3.L.S.k = P.y.h.lt) (k5 : (tailF Pf).s5.L.S.k = P.rd.muH)
    (k6 : (tailF Pf).s6.L.S.k = P.rd.muH2) (e1 : Pf.nr.sq.R.L.e = eDefault (tailF Pf).s1.L.S.k)
    (n5 : 9 ≤ (tailF Pf).s5.L.S.k) (e5 : Pf.fp.gp.e = eRange (tailF Pf).s5.L.S.k n5)
    (n6 : 9 ≤ (tailF Pf).s6.L.S.k) (e6 : Pf.fp.rt.L.e = eRange (tailF Pf).s6.L.S.k n6)
    {b sG la : ℕ} (hla : la = sG + Pf.D.lT) (s1 : P.rd.muV = Pf.D.lL + 1 + b + la)
    (s5 : P.rd.muH = Pf.D.lL + lF Pf.D - sG + la)
    (s6 : P.rd.muH2 = Pf.D.lL - 1 + lFe Pf.D - sG + la) (s2 : P.y.h.lt = Pf.D.lT)
    (hx : ∀ i : Fin Pf.D.lT, x.2 i = gl.val ((drawnOf t0).getD i.val zeroE))
    (zt uz : ℕ → Cb.Gl.E) (hzt : ∀ j, j < Pf.D.lT → uz j = zt j) :
    ∀ ZV ZA ZB, lastOf o.H.wpl.r la = .ok ZV → lastOf o.hd.r la = .ok ZA →
      lastOf hd2.r la = .ok ZB →
      PointTies Pf.D (eAt Pf.toOwnPar Pf.wPart ((k4Tail W' P hp t0 nz a).z7 x) zt)
        (termsEAt Pf.tp ((tailF Pf).b3 ((k4Tail W' P hp t0 nz a).z7 x)).2)
        (gatedEAt Pf.fp ((tailF Pf).b5 ((k4Tail W' P hp t0 nz a).z7 x)).2
          ((tailF Pf).b6 ((k4Tail W' P hp t0 nz a).z7 x)).2) b sG uz (pt gl tT.r) (pt gl tT.r)
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
  have q1 : (orderDefault P.rd.muV).Perm (List.range (tailF Pf).s1.L.S.k) := by
    rw [k1]
    exact default_perm _
  have q5 : (orderRange P.rd.muH).Perm (List.range (tailF Pf).s5.L.S.k) := by
    rw [k5]
    exact range_perm _ (by rw [← k5]; exact n5)
  have q6 : (orderRange P.rd.muH2).Perm (List.range (tailF Pf).s6.L.S.k) := by
    rw [k6]
    exact range_perm _ (by rw [← k6]; exact n6)
  rw [Ld.kWpl] at hZV
  rw [Ld.kPV, Ld.kTV]
  exact pointTies_at Pf W' (ksOf P hp) (t0.drop 1) nz a x O1 O2 O3 O5 O6 k1 k2 k3 k5 k6 c1 c2
    Ld.c3 c5 Ld.c6 q1 q5 q6 (e1.trans (ordE_congr (by rw [k1]) _ q1))
    (e5.trans (ordE_congr (by rw [k5]) _ q5)) (e6.trans (ordE_congr (by rw [k6]) _ q6)) hla s1 s5
    s6 s2 s2 hZV hZA hZB hP hx zt uz hzt

/-- **seven_parts' premise hpt at a hearing.** -/
theorem hpt_of_led {p4 : Psc} (O4 : OutIs gl (k4Tail W' P hp t0 nz a).d4 p4)
    (k4 : kS Pf.D = hp.lamS) :
    ∀ j, j < kS Pf.D → Blocks.nat (Pf.ip.inn.Kp.outPt Pf.ip.inn.Mk
        ((tailF Pf).b4 ((k4Tail W' P hp t0 nz a).z7 x)).2) j =
      gl.val (o.K.rs.getD (kS Pf.D - 1 - j) zeroE) :=
  hpt_at Pf W' (ksOf P hp) (t0.drop 1) nz a x O4 k4 Ld.c4

/-- **seven_parts' premise T at a hearing.** shownT: the run of shown values that the batched
sumcheck's stretch reads off its first ledger; om: the two weights of the joined claims. -/
theorem stackTies_of_led
    (hc : (k4Tail W' P hp t0 nz a).d4.Claim ((k4Tail W' P hp t0 nz a).y4 x)) {p3 : Psc}
    (O3 : OutIs gl (k4Tail W' P hp t0 nz a).d3 p3) (k3 : (tailF Pf).s3.L.S.k = P.y.h.lt)
    (hnum : ∀ q : ShA Pf.D, W'.w3.num q = numA Pf.D q) {yl : Lay}
    (hN : yl.NN * yl.Lam = Pf.D.nNu) (hM : yl.LamM = Pf.D.ne) (hE : yl.h.NE = Pf.D.nx)
    (hEnd : Pf.D.nNu + Pf.D.ne + Pf.D.ne * Pf.D.nx ≤ nEndT P.y) {shownT om : Array E}
    (hsh : ((Array.range (nEndT P.y)).mapM fun i => G2.shown (tT.sEnd + i)) = some shownT)
    (hom : om = powers (tapeEps ((ksOf P hp).tc4 (t0.drop 1))) 2) {z : ℕ → Cb.Gl.E}
    (hz0 : ((tailF Pf).b4 ((k4Tail W' P hp t0 nz a).z7 x)).2.st.z = z)
    (hz3 : Pf.ip.zP ((tailF Pf).b4 ((k4Tail W' P hp t0 nz a).z7 x)).2.st .QK = z) :
    StackTies Pf.ip ((tailF Pf).b4 ((k4Tail W' P hp t0 nz a).z7 x)).2.st gl yl shownT om z
      (pt gl tT.r) := by
  obtain ⟨hlt, -⟩ := tscIn_heard Ld.c3
  have hl : (H1.ztF.toList.take P.y.h.lt).length = P.y.h.lt := by
    rw [List.length_take, Array.length_toList]
    exact Nat.min_eq_left hlt
  refine stackTies_at Pf W' (ksOf P hp) (t0.drop 1) nz a x hc O3 k3 Ld.c3 hnum hN hM hE
    (fun n hn => ?_) ?_ hz0 hz3
  · rw [shown_at hsh (Nat.lt_of_lt_of_le hn hEnd),
      tsc_shown Ld.s1 Ld.c3 G2 Ld.l1 n (Nat.lt_of_lt_of_le hn hEnd)]
    unfold tscVals
    rw [hl]
    rfl
  · rw [hom, Desc.First.P1.powers_val gl _ 2 1 (by omega), pow_one]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.points_of_led
#print axioms OnBytes.Road.K4.hpt_of_led
#print axioms OnBytes.Road.K4.stackTies_of_led
