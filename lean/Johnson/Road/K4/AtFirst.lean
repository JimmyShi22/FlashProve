-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/AtFirst.lean: THE FIRST GROUP's twin of four files: PointsAt.lean (its
typed part), PointTiesAt.lean, StackTiesAt.lean and StackPointAt.lean: the records PointTies and
StackTies and the batched sumcheck's end point, at the last statement that the chain's data off a
tape make, for the first group's chain.

The first group's chain has its own letters: the parameters FullFPar, the chain behind the token
point tailW P, the norms' record eAtF, statements that hold three points (the token point is
P.ofp.fs.pvF x). Its seven stages are written as a later group's. The statements and proofs here are
those of the four files, turned to these letters by a program and compiled; each name bears an F.

Main names: `eAt_r1F`, `eAt_pVF`, `eAt_r2F`, `tAt_rtF`, `gAt_r5F`, `gAt_r6F` (what the records
read, by definition) · `r1_atF`, `pV_atF`, `r4_atF`, `r2_atF`, `rt_atF`, `r5_atF`, `r6_atF` ·
`pointTies_atF` · `st_of_claimF`, `o3_valsF`, `stackTies_atF` · `hpt_atF`, `zt_atF`.
Limits. As the four files': OutIs at the stages named, the flat functions' returns on the stages'
tapes, the typed permutations, sizes, the fourth stage's claim and the two clauses on the lookup's
point are premises. Identities on public numbers: nothing on a world, on a draw, on soundness or on
hiding.


-/
import Johnson.Road.K4.PointTiesAt
import Johnson.Road.K4.StackTiesAt
import Johnson.Road.K4.StackPointAt
import Cb.Pv.Lay.End.LayFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc
open Inst.Model (Scl)
open Inst.Model.FFSeg (lF lFe zpos)
open OnBytes.Model (Fork Psc Level Aff Tsc RoundName lastOf)
open OnBytes.Model.Layer (Pub Env Heard HeardStack Lay)
open OnBytes.Desc.First.K4 (hearStack engFl)
open OnBytes.Tie.Pv.Lay (OutIs ordE)
open OnBytes.Desc.First.P1 (gl pscT Ks NzT Adds7 tailT TailM TailR tapeEps tscIn_heard tscWs)

/-! ## What the library's records read of a last statement -/

section Reads

variable {E' : Type} [Field E'] [Fintype E'] [scl : Scl] {M X : Type} (P : OwnFPar E' M X)
  (W : P.WFPart) (e : (tailFst P W).s7.Nx) (zt : ℕ → E')

theorem eAt_r1F : (eAtF P W e zt).r1 = Blocks.nat fun i =>
    (tailFst P W).s1.L.Q.outPt (tailFst P W).s1.L.M ((tailFst P W).b1 e).2
      (P.nr.sq.R.L.e.symm i) := rfl

theorem eAt_pVF : (eAtF P W e zt).pV = Blocks.nat (P.fs.pvF ((tailFst P W).xL e)) := rfl

theorem eAt_r2F : (eAtF P W e zt).r2 = Blocks.nat
    ((tailFst P W).s2.L.Q.outPt (tailFst P W).s2.L.M ((tailFst P W).b2 e).2) := rfl

theorem tAt_rtF : (termsEAt P.tp ((tailFst P W).b3 e).2).rt = Blocks.nat
    ((tailFst P W).s3.L.Q.outPt (tailFst P W).s3.L.M ((tailFst P W).b3 e).2) := rfl

end Reads

section ReadsF

variable {E' : Type} [Field E'] [Fintype E'] [scl : Scl] {M X : Type} (P : FullFPar E' M X)
  (e : (tailW P).s7.Nx)

theorem gAt_r5F : (gatedEAt P.fp ((tailW P).b5 e).2 ((tailW P).b6 e).2).r5 = Blocks.nat fun i =>
    (tailW P).s5.L.Q.outPt (tailW P).s5.L.M ((tailW P).b5 e).2 (P.fp.gp.e.symm i) := rfl

theorem gAt_r6F : (gatedEAt P.fp ((tailW P).b5 e).2 ((tailW P).b6 e).2).r6 = Blocks.nat fun i =>
    (tailW P).s6.L.Q.outPt (tailW P).s6.L.M ((tailW P).b6 e).2 (P.fp.rt.L.e.symm i) := rfl

end ReadsF

/-! ## The seven points at the chain's data off a tape -/

section Points

variable [scl : Scl] {M X : Type} (P : FullFPar Cb.Gl.E M X) {R : TailR} (W' : TailM (tailW P) R)
  (k : Ks) (t : Tape) (nz : NzT (tailW P) k t) (a : Adds7 (tailW P)) (x : P.ofp.fs.X3)

/-- The squares' point. -/
theorem r1_atF {p : Psc} (O : OutIs gl (tailT W' k t nz a).d1 p)
    (hk : (tailW P).s1.L.S.k = k.k1) {rho : Array E} {C : Aff} {order : List ℕ} {F G : Fork}
    {u : Tape} {L : Level} (h : Fl.levelIn k.k1 rho C order F (k.tc1 t) = some (L, G, u))
    (hp : order.Perm (List.range (tailW P).s1.L.S.k))
    (he : P.ofp.nr.sq.R.L.e = ordE (tailW P).s1.L.S.k order hp) (zt : ℕ → Cb.Gl.E) {j : ℕ}
    (hj : j < (tailW P).s1.L.S.k) :
    pt gl L.r j = (eAtF P.ofp P.wfPart ((tailT W' k t nz a).z7 x) zt).r1 j := by
  rw [eAt_r1F, he]
  exact stgT_level_point W'.w1.num k.k1 (k.tc1 t) nz.b1 a.st1 a.t1 O hk h hp hj

/-- The norms' token point. d0: the words that the point's round drew. -/
theorem pV_atF {PV : Array E} {d0 : List E} (hP : PV.toList = d0)
    (hx : ∀ i : Fin P.D.lT, P.ofp.fs.pvF x i = gl.val (d0.getD i.val zeroE)) (zt : ℕ → Cb.Gl.E) {j :
        ℕ}
    (hj : j < P.D.lT) :
    pt gl PV j = (eAtF P.ofp P.wfPart ((tailT W' k t nz a).z7 x) zt).pV j := by
  rw [eAt_pVF]
  exact heard_point hP hx hj

/-- The batched sumcheck's end point. -/
theorem r4_atF {p : Psc} (O : OutIs gl (tailT W' k t nz a).d4 p)
    (hk : (tailW P).s4.L.S.k = k.k4) {Pp : Pub} {v : Env} {H : Heard} {NCLp : ℕ} {F G : Fork}
    {u : Tape} {K : HeardStack}
    (h : hearStack engFl Pp v H k.k4 NCLp F (k.tc4 t) = some (K, G, u)) {j : ℕ}
    (hj : j < (tailW P).s4.L.S.k) :
    Blocks.nat ((tailW P).s4.L.Q.outPt (tailW P).s4.L.M
        ((tailW P).b4 ((tailT W' k t nz a).z7 x)).2) j =
      gl.val (K.rs.getD ((tailW P).s4.L.S.k - 1 - j) zeroE) :=
  stgT_stack_point W'.w4.num k.k4 (k.tc4 t) nz.b4 a.st4 a.t4 O hk h hj

/-- The end point of the token sumcheck of the row products. -/
theorem r2_atF {p : Psc} (O : OutIs gl (tailT W' k t nz a).d2 p)
    (hk : (tailW P).s2.L.S.k = k.k2) {Pv : Array E} {n dY : ℕ} {F G : Fork} {u : Tape} {o : Tsc}
    (h : Fl.tscIn Pv k.k2 n dY F ((k.tcP t).drop 1) = some (o, G, u)) (zt : ℕ → Cb.Gl.E) {j : ℕ}
    (hj : j < (tailW P).s2.L.S.k) :
    pt gl o.r j = (eAtF P.ofp P.wfPart ((tailT W' k t nz a).z7 x) zt).r2 j := by
  rw [eAt_r2F]
  exact stgT_tsc_point W'.w2.num k.k2 ((k.tcP t).drop 1) nz.b2 a.st2 a.t2 O hk h hj

/-- The end point of the sumcheck of the terms. -/
theorem rt_atF {p : Psc} (O : OutIs gl (tailT W' k t nz a).d3 p)
    (hk : (tailW P).s3.L.S.k = k.k3) {Pv : Array E} {n dY : ℕ} {F G : Fork} {u : Tape} {o : Tsc}
    (h : Fl.tscIn Pv k.k3 n dY F (((k.tcP t).drop 1).drop (k.k2 + 3)) = some (o, G, u)) {j : ℕ}
    (hj : j < (tailW P).s3.L.S.k) :
    pt gl o.r j = (termsEAt P.tp ((tailW P).b3 ((tailT W' k t nz a).z7 x)).2).rt j := by
  show pt gl o.r j = Blocks.nat ((tailW P).s3.L.Q.outPt (tailW P).s3.L.M
    ((tailW P).b3 ((tailT W' k t nz a).z7 x)).2) j
  exact stgT_tsc_point W'.w3.num k.k3 (((k.tcP t).drop 1).drop (k.k2 + 3)) nz.b3 a.st3 a.t3 O hk h
    hj

/-- The first product layer of the gated products. -/
theorem r5_atF {p : Psc} (O : OutIs gl (tailT W' k t nz a).d5 p)
    (hk : (tailW P).s5.L.S.k = k.k5) {rho : Array E} {C : Aff} {order : List ℕ} {F G : Fork}
    {u : Tape} {L : Level} (h : Fl.levelIn k.k5 rho C order F (k.tc5 t) = some (L, G, u))
    (hp : order.Perm (List.range (tailW P).s5.L.S.k))
    (he : P.fp.gp.e = ordE (tailW P).s5.L.S.k order hp) {j : ℕ}
    (hj : j < (tailW P).s5.L.S.k) :
    pt gl L.r j = (gatedEAt P.fp ((tailW P).b5 ((tailT W' k t nz a).z7 x)).2
      ((tailW P).b6 ((tailT W' k t nz a).z7 x)).2).r5 j := by
  rw [gAt_r5F, he]
  exact stgT_level_point W'.w5.num k.k5 (k.tc5 t) nz.b5 a.st5 a.t5 O hk h hp hj

/-- The second product layer. -/
theorem r6_atF {p : Psc} (O : OutIs gl (tailT W' k t nz a).d6 p)
    (hk : (tailW P).s6.L.S.k = k.k6) {rho : Array E} {C : Aff} {order : List ℕ} {F G : Fork}
    {u : Tape} {L : Level} (h : Fl.levelIn k.k6 rho C order F (k.tc6 t) = some (L, G, u))
    (hp : order.Perm (List.range (tailW P).s6.L.S.k))
    (he : P.fp.rt.L.e = ordE (tailW P).s6.L.S.k order hp) {j : ℕ}
    (hj : j < (tailW P).s6.L.S.k) :
    pt gl L.r j = (gatedEAt P.fp ((tailW P).b5 ((tailT W' k t nz a).z7 x)).2
      ((tailW P).b6 ((tailT W' k t nz a).z7 x)).2).r6 j := by
  rw [gAt_r6F, he]
  exact stgT_level_point W'.w6.num k.k6 (k.tc6 t) nz.b6 a.st6 a.t6 O hk h hp hj

end Points

section TiesF

variable [scl : Scl] {M X : Type} (P : FullFPar Cb.Gl.E M X) {R : TailR} (W' : TailM (tailW P) R)
  (k : Ks) (t : Tape) (nz : NzT (tailW P) k t) (a : Adds7 (tailW P)) (x : P.ofp.fs.X3)

/-- **PointTies at the chain's data off a tape.** -/
theorem pointTies_atF {p1 p2 p3 p5 p6 : Psc} (O1 : OutIs gl (tailT W' k t nz a).d1 p1)
    (O2 : OutIs gl (tailT W' k t nz a).d2 p2) (O3 : OutIs gl (tailT W' k t nz a).d3 p3)
    (O5 : OutIs gl (tailT W' k t nz a).d5 p5) (O6 : OutIs gl (tailT W' k t nz a).d6 p6)
    (k1 : (tailW P).s1.L.S.k = k.k1) (k2 : (tailW P).s2.L.S.k = k.k2)
    (k3 : (tailW P).s3.L.S.k = k.k3) (k5 : (tailW P).s5.L.S.k = k.k5)
    (k6 : (tailW P).s6.L.S.k = k.k6)
    {rho1 rho5 rho6 : Array E} {C1 C5 C6 : Aff} {or1 or5 or6 : List ℕ}
    {F1 G1 F2 G2 F3 G3 F5 G5 F6 G6 : Fork} {u1 u2 u3 u5 u6 : Tape} {L1 L5 L6 : Level}
    {Pv2 Pv3 : Array E} {n2 n3 dY2 dY3 : ℕ} {o2 o3 : Tsc}
    (c1 : Fl.levelIn k.k1 rho1 C1 or1 F1 (k.tc1 t) = some (L1, G1, u1))
    (c2 : Fl.tscIn Pv2 k.k2 n2 dY2 F2 ((k.tcP t).drop 1) = some (o2, G2, u2))
    (c3 : Fl.tscIn Pv3 k.k3 n3 dY3 F3 (((k.tcP t).drop 1).drop (k.k2 + 3)) = some (o3, G3, u3))
    (c5 : Fl.levelIn k.k5 rho5 C5 or5 F5 (k.tc5 t) = some (L5, G5, u5))
    (c6 : Fl.levelIn k.k6 rho6 C6 or6 F6 (k.tc6 t) = some (L6, G6, u6))
    (q1 : or1.Perm (List.range (tailW P).s1.L.S.k))
    (q5 : or5.Perm (List.range (tailW P).s5.L.S.k))
    (q6 : or6.Perm (List.range (tailW P).s6.L.S.k))
    (e1 : P.ofp.nr.sq.R.L.e = ordE (tailW P).s1.L.S.k or1 q1)
    (e5 : P.fp.gp.e = ordE (tailW P).s5.L.S.k or5 q5)
    (e6 : P.fp.rt.L.e = ordE (tailW P).s6.L.S.k or6 q6)
    {b sG la : ℕ} (hla : la = sG + P.D.lT) (s1 : k.k1 = P.D.lL + 1 + b + la)
    (s5 : k.k5 = P.D.lL + lF P.D - sG + la) (s6 : k.k6 = P.D.lL - 1 + lFe P.D - sG + la)
    (s2 : k.k2 = P.D.lT) (s3 : k.k3 = P.D.lT) {ZV ZA ZB PV : Array E} {d0 : List E}
    (hZV : lastOf L1.r la = .ok ZV) (hZA : lastOf L5.r la = .ok ZA)
    (hZB : lastOf L6.r la = .ok ZB) (hP : PV.toList = d0)
    (hx : ∀ i : Fin P.D.lT, P.ofp.fs.pvF x i = gl.val (d0.getD i.val zeroE)) (zt u : ℕ → Cb.Gl.E)
    (hzt : ∀ j, j < P.D.lT → u j = zt j) :
    PointTies P.D (eAtF P.ofp P.wfPart ((tailT W' k t nz a).z7 x) zt)
      (termsEAt P.tp ((tailW P).b3 ((tailT W' k t nz a).z7 x)).2)
      (gatedEAt P.fp ((tailW P).b5 ((tailT W' k t nz a).z7 x)).2
        ((tailW P).b6 ((tailT W' k t nz a).z7 x)).2) b sG u (pt gl o3.r) (pt gl o3.r) (pt gl ZV)
      (fun j => pt gl ZV (sG + j)) (pt gl PV) (pt gl o2.r) (pt gl ZA)
      (fun j => pt gl ZA (sG + j)) (pt gl ZB) (fun j => pt gl ZB (sG + j)) :=
  pointTies_of hla hZV hZA hZB (by rw [level_size c1, s1]) (by rw [level_size c5, s5])
    (by rw [level_size c6, s6])
    (fun j hj => r1_atF P W' k t nz a x O1 k1 c1 q1 e1 zt (by rw [k1, ← level_size c1]; exact hj))
    (fun j hj => r5_atF P W' k t nz a x O5 k5 c5 q5 e5 (by rw [k5, ← level_size c5]; exact hj))
    (fun j hj => r6_atF P W' k t nz a x O6 k6 c6 q6 e6 (by rw [k6, ← level_size c6]; exact hj))
    hzt (fun j hj => rt_atF P W' k t nz a x O3 k3 c3 (by rw [k3, s3]; exact hj))
    (fun j hj => pV_atF P W' k t nz a x hP hx zt hj)
    (fun j hj => r2_atF P W' k t nz a x O2 k2 c2 zt (by rw [k2, s2]; exact hj))

end TiesF

section StackF

variable [scl : Scl] {M X : Type} (P : FullFPar Cb.Gl.E M X) {R : TailR} (W' : TailM (tailW P) R)
  (k : Ks) (t : Tape) (nz : NzT (tailW P) k t) (a : Adds7 (tailW P)) (x : P.ofp.fs.X3)

/-- The state in the fourth stage's output is the chain's. -/
theorem st_of_claimF (hc : (tailT W' k t nz a).d4.Claim ((tailT W' k t nz a).y4 x)) :
    ((tailW P).b4 ((tailT W' k t nz a).z7 x)).2.st =
      ((tailW P).s4.cl ((tailT W' k t nz a).y4 x) (tailT W' k t nz a).d4.rd).2 :=
  (congrArg Prod.snd hc).symm

/-- What the output of the sumcheck of the terms shows. -/
theorem o3_valsF {p : Psc} (O : OutIs gl (tailT W' k t nz a).d3 p)
    (hnum : ∀ q : ShA P.D, W'.w3.num q = numA P.D q) (q : ShA P.D) :
    (tailT W' k t nz a).d3.out.vals q =
      gl.val ((pscT 0 k.k3 (((k.tcP t).drop 1).drop (k.k2 + 3))).v.getD (numA P.D q) zeroE) := by
  rw [congrFun O.vals q, ← hnum q]
  rfl

/-- **StackTies at the chain's data off a tape.** -/
theorem stackTies_atF (hc : (tailT W' k t nz a).d4.Claim ((tailT W' k t nz a).y4 x)) {p : Psc}
    (O : OutIs gl (tailT W' k t nz a).d3 p) (hk : (tailW P).s3.L.S.k = k.k3) {Pv : Array E}
    {nn dY : ℕ} {F G : Fork} {u : Tape} {o : Tsc}
    (h : Fl.tscIn Pv k.k3 nn dY F (((k.tcP t).drop 1).drop (k.k2 + 3)) = some (o, G, u))
    (hnum : ∀ q : ShA P.D, W'.w3.num q = numA P.D q) {yl : Lay}
    (hN : yl.NN * yl.Lam = P.D.nNu) (hM : yl.LamM = P.D.ne) (hE : yl.h.NE = P.D.nx)
    {shownT om : Array E}
    (hsh : ∀ n, n < P.D.nNu + P.D.ne + P.D.ne * P.D.nx → shownT.getD n zeroE =
      (pscT 0 k.k3 (((k.tcP t).drop 1).drop (k.k2 + 3))).v.getD n zeroE)
    (hom : gl.val (om.getD 1 zeroE) = gl.val (tapeEps (k.tc4 t))) {z : ℕ → Cb.Gl.E}
    (hz0 : ((tailW P).b4 ((tailT W' k t nz a).z7 x)).2.st.z = z)
    (hz3 : P.ip.zP ((tailW P).b4 ((tailT W' k t nz a).z7 x)).2.st .QK = z) :
    StackTies P.ip ((tailW P).b4 ((tailT W' k t nz a).z7 x)).2.st gl yl shownT om z
      (pt gl o.r) := by
  have hs := st_of_claimF P W' k t nz a x hc
  have hv : ∀ q : ShA P.D, ((tailW P).b4 ((tailT W' k t nz a).z7 x)).2.st.o3.vals q =
      gl.val ((pscT 0 k.k3 (((k.tcP t).drop 1).drop (k.k2 + 3))).v.getD (numA P.D q) zeroE) := by
    intro q
    rw [hs]
    exact o3_valsF P W' k t nz a O hnum q
  have hrt : P.ip.rt ((tailW P).b4 ((tailT W' k t nz a).z7 x)).2.st = Blocks.nat
      ((tailW P).s3.L.Q.outPt (tailW P).s3.L.M (tailT W' k t nz a).d3.out) := by
    rw [hs]
    rfl
  refine ⟨hz0, hz3, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrt]
    funext j
    by_cases hj : j < (tailW P).s3.L.S.k
    · exact (stgT_tsc_point W'.w3.num k.k3 (((k.tcP t).drop 1).drop (k.k2 + 3)) nz.b3 a.st3 a.t3
        O hk h hj).symm
    · obtain ⟨hlt, hw, -, -, -, -, -, -, -, -, -, hr, -⟩ := tscIn_heard h
      have hsz : o.r.size = k.k3 := by
        rw [← Array.length_toList, hr, List.length_map, ← List.length_map (f := (·.1)), hw]
        unfold tscWs
        rw [List.length_map, List.length_take, Array.length_toList]
        exact Nat.min_eq_left hlt
      have hj' : ¬ j < o.r.size := by rw [hsz, ← hk]; exact hj
      unfold Blocks.nat pt
      rw [dif_neg hj, Array.getD, dif_neg hj', gl.zero]
  · rw [hs, hom]
    rfl
  · intro ν hν
    have hν' : ν < P.D.nNu := hν
    rw [hv]
    unfold sentAt
    rw [hsh ν (by omega)]
    rfl
  · intro l hl
    have hl' : l < P.D.ne := hl
    rw [hv]
    unfold sentAt
    rw [hN, hsh (P.D.nNu + l) (by omega)]
    rfl
  · intro l e he
    rw [hv]
    unfold sentAt
    have hb : l * P.D.nx + e < P.D.ne * P.D.nx := by
      calc l * P.D.nx + e < l * P.D.nx + P.D.nx := Nat.add_lt_add_left he.2 _
        _ = (l + 1) * P.D.nx := by ring
        _ ≤ P.D.ne * P.D.nx := Nat.mul_le_mul_right _ he.1
    rw [hN, hM, hE, hsh (P.D.nNu + P.D.ne + l * P.D.nx + e) (by omega)]
    rfl

end StackF

section StackPointF

variable [scl : Scl] {M X : Type} (P : FullFPar Cb.Gl.E M X) {R : TailR} (W' : TailM (tailW P) R)
  (k : Ks) (t : Tape) (nz : NzT (tailW P) k t) (a : Adds7 (tailW P)) (x : P.ofp.fs.X3)

/-- The premise hpt of seven_parts. -/
theorem hpt_atF {p : Psc} (O : OutIs gl (tailT W' k t nz a).d4 p) (hk : kS P.D = k.k4) {Pp : Pub}
    {v : Env} {H : Heard} {NCLp : ℕ} {F G : Fork} {u : Tape} {K : HeardStack}
    (h : hearStack engFl Pp v H k.k4 NCLp F (k.tc4 t) = some (K, G, u)) :
    ∀ j, j < kS P.D → Blocks.nat (P.ip.inn.Kp.outPt P.ip.inn.Mk
        ((tailW P).b4 ((tailT W' k t nz a).z7 x)).2) j =
      gl.val (K.rs.getD (kS P.D - 1 - j) zeroE) :=
  fun _ hj => r4_atF P W' k t nz a x O hk h hj

/-- The clause zt of PointTies. -/
theorem zt_atF {z : ℕ → Cb.Gl.E}
    (hz0 : ((tailW P).b4 ((tailT W' k t nz a).z7 x)).2.st.z = z) :
    ∀ j, j < P.D.lT → zpos P.D z j =
      zpos P.D ((tailW P).b4 ((tailT W' k t nz a).z7 x)).2.st.z j :=
  fun _ _ => by rw [hz0]

end StackPointF

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.pointTies_atF
#print axioms OnBytes.Road.K4.stackTies_atF
#print axioms OnBytes.Road.K4.hpt_atF
#print axioms OnBytes.Road.K4.zt_atF
