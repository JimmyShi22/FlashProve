-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/PointsAt.lean: the points that the flat functions of a product layer and of a token
sumcheck leave, read, are the points of the typed outputs that are read off the same tape.

Johnson/Road/K4/LevelPoint.lean has the ties for any function on the rounds that reads the
challenges in the order heard. OutIs.pt (OnBytes/Tie/Pv/Lay/HearTieL.lean) says that of a
typed stage's output, in the words of the stage's data. Here the data are those that stgT
reads off a tape (OnBytes/Desc/First/P1/TailTape.lean), and the flat functions run on that same
tape: so the challenges are the same words.

Main names:
  `pair_snd`: the second members of a list of pairs.
  `heard_chal`: the challenges in the stage's data are those of the rounds read under any weights.
  `stgT_level_point`: a product layer's point L.r against the typed output's point carried through
    the inverse of the layer's permutation ordE k order h.
  `stgT_tsc_point`: a token sumcheck's point o.r against the typed output's point.
  `stgT_stack_point`: the batched sumcheck's typed output's point against the verifier's challenges
    turned round (K.rs).
  `pV_at`, `r1_at`, `r2_at`, `rt_at`, `r4_at`, `r5_at`, `r6_at`: the points of the library's records
    eAt, termsEAt and gatedEAt, and the batched sumcheck's, at the last statement made from the
    chain's data off a tape (tailT … .z7 x).
Limits. OutIs, the flat function's return on that tape, and that the stage has as many variables'
rounds as the flat function, are premises. Identities on public numbers: nothing on a world, on a
draw, on soundness or on hiding.


-/
import Johnson.Road.K4.LevelPoint
import OnBytes.Desc.First.P1.Heard
import OnBytes.Desc.First.P1.TailTape
import OnBytes.Desc.First.P1.TailParts
import OnBytes.Desc.First.K4.StackTape
import OnBytes.Tie.Pv.Lay.HearTieL
import Cb.Pv.Lay.End.LayAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc
open Inst.Model (Scl)
open OnBytes.Model (Fork Psc Level Aff Tsc RoundName)
open OnBytes.Model.Layer (Pub Env Heard HeardStack)
open OnBytes.Desc.First.K4 (hearStack engFl hearStack_tape)
open OnBytes.Tie.Pv.Lay (OutIs ordE)
open OnBytes.Desc.First.P1 (gl pscT stgT msOf heardPairs pairs_congr levelIn_heard levelMs levelWs
  levelR tscIn_heard tscMs tscWs Ks NzT Adds7 tailT TailM TailR plainWs msOf_append_same)

/-- The second members of a list of pairs. -/
theorem pair_snd {α β γ : Type} (l : List γ) (a : γ → α) (b : γ → β) (x : α) (y : β) (i : ℕ) :
    ((l.map fun m => (a m, b m)).getD i (x, y)).2 = (l.map b).getD i y := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

/-- The challenges in the data that stgT reads off a tape are those of the rounds behind the tape's
first, read under any k weights. -/
theorem heard_chal (n : ℕ) (ws : List OnBytes.Psc.Weight) (t : Tape) (i : ℕ) :
    ((pscT n ws.length t).rs.getD i ([], zeroE)).2 =
      ((msOf ws (t.drop 1)).map (·.2.2)).getD i zeroE := by
  show ((heardPairs ws.length (t.drop 1)).getD i ([], zeroE)).2 = _
  rw [← pairs_congr ws (t.drop 1)]
  exact pair_snd _ _ _ _ _ i

/-- **A product layer's point.** -/
theorem stgT_level_point {M X : Type} {S : Stg Cb.Gl.E M X} (num : S.L.S.A → ℕ) (k : ℕ)
    (t : Tape) (hβ : gl.val (pscT S.n k t).beta ≠ 0) (st : S.L.St) (tg : E) {p : Psc}
    (O : OutIs gl (stgT num k t hβ st tg) p) (hk : S.L.S.k = k) {rho : Array E} {C : Aff}
    {order : List ℕ} {F G : Fork} {u : Tape} {L : Level}
    (h : Fl.levelIn k rho C order F t = some (L, G, u))
    (hp : order.Perm (List.range S.L.S.k)) {j : ℕ} (hj : j < S.L.S.k) :
    pt gl L.r j = Blocks.nat (fun i => S.L.Q.outPt S.L.M (stgT num k t hβ st tg).out
      ((ordE S.L.S.k order hp).symm i)) j := by
  subst hk
  obtain ⟨hom, -, -, hw, -, -, -, -, -, -, -, -, -, hr, -⟩ := levelIn_heard h
  have hl : (levelWs S.L.S.k rho order).length = S.L.S.k := by
    unfold levelWs
    rw [List.length_map, hom]
  have hx : ((levelMs S.L.S.k rho order t).map (·.2.2)).length = S.L.S.k := by
    rw [List.length_map, ← List.length_map (f := (·.1)), hw, hl]
  rw [hr]
  refine level_point hp hx (by rw [Array.size_replicate]) (fun i => ?_) hj
  rw [O.pt i]
  congr 1
  have e := heard_chal S.n (levelWs S.L.S.k rho order) t i.val
  rw [hl] at e
  exact e

/-- **A token sumcheck's point.** -/
theorem stgT_tsc_point {M X : Type} {S : Stg Cb.Gl.E M X} (num : S.L.S.A → ℕ) (k : ℕ)
    (t : Tape) (hβ : gl.val (pscT S.n k t).beta ≠ 0) (st : S.L.St) (tg : E) {p : Psc}
    (O : OutIs gl (stgT num k t hβ st tg) p) (hk : S.L.S.k = k) {P : Array E} {n dY : ℕ}
    {F G : Fork} {u : Tape} {o : Tsc} (h : Fl.tscIn P k n dY F t = some (o, G, u)) {j : ℕ}
    (hj : j < S.L.S.k) :
    pt gl o.r j = Blocks.nat (S.L.Q.outPt S.L.M (stgT num k t hβ st tg).out) j := by
  subst hk
  obtain ⟨hlt, -, -, -, -, -, -, -, -, -, -, hr, -⟩ := tscIn_heard h
  have hl : (tscWs (P.toList.take S.L.S.k)).length = S.L.S.k := by
    unfold tscWs
    rw [List.length_map, List.length_take, Array.length_toList]
    exact Nat.min_eq_left hlt
  refine heard_point hr (fun i => ?_) hj
  rw [O.pt i]
  congr 1
  have e := heard_chal S.n (tscWs (P.toList.take S.L.S.k)) t i.val
  rw [hl] at e
  exact e

/-- **The batched sumcheck's point**: the typed output's point reads as the verifier's challenges
turned round. t: the tape from the round on that draws the element joining the two claims; the
stage's data are read off the tape behind that round. -/
theorem stgT_stack_point {M X : Type} {S : Stg Cb.Gl.E M X} (num : S.L.S.A → ℕ) (k : ℕ)
    (t : Tape) (hβ : gl.val (pscT S.n k (t.drop 1)).beta ≠ 0) (st : S.L.St) (tg : E) {p : Psc}
    (O : OutIs gl (stgT num k (t.drop 1) hβ st tg) p) (hk : S.L.S.k = k) {P : Pub} {v : Env}
    {H : Heard} {NCLp : ℕ} {F G : Fork} {u : Tape} {K : HeardStack}
    (h : hearStack engFl P v H k NCLp F t = some (K, G, u)) {j : ℕ} (hj : j < S.L.S.k) :
    Blocks.nat (S.L.Q.outPt S.L.M (stgT num k (t.drop 1) hβ st tg).out) j =
      gl.val (K.rs.getD (S.L.S.k - 1 - j) zeroE) := by
  subst hk
  obtain ⟨x, mu0, eps, beta, T, rs, sentY, vals, w1, wY, wV, C, G1, ms, y, p', ht, hrs, -, -, -,
    hms, -, -, a1, -, -, hK, -⟩ := hearStack_tape h
  have hl : (plainWs S.L.S.k).length = S.L.S.k := List.length_replicate
  have hx : (ms.map (·.2.2)).length = S.L.S.k := by
    rw [List.length_map, ← List.length_map (f := (·.1)), a1, hl]
  refine turned_point hK hx (fun i => ?_) hj
  rw [O.pt i]
  congr 1
  have e := heard_chal S.n (plainWs S.L.S.k) (t.drop 1) i.val
  rw [hl] at e
  have hd : (t.drop 1).drop 1 = rs ++ ⟨some RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
      ⟨some RoundName.pscValues.name, 0, wV, vals.toList, []⟩ :: u := by
    rw [ht]
    rfl
  rw [hd, msOf_append_same _ _ _ (by rw [hl, hrs]), ← hms] at e
  exact e

/-! ## What the library's records read of a last statement -/

section Reads

variable {E' : Type} [Field E'] [Fintype E'] [scl : Scl] {M X : Type} (P : OwnPar E' M X)
  (W : P.WPart) (e : (tailAt P W).s7.Nx) (zt : ℕ → E')

theorem eAt_r1 : (eAt P W e zt).r1 = Blocks.nat fun i =>
    (tailAt P W).s1.L.Q.outPt (tailAt P W).s1.L.M ((tailAt P W).b1 e).2
      (P.nr.sq.R.L.e.symm i) := rfl

theorem eAt_pV : (eAt P W e zt).pV = Blocks.nat ((tailAt P W).xL e).2 := rfl

theorem eAt_r2 : (eAt P W e zt).r2 = Blocks.nat
    ((tailAt P W).s2.L.Q.outPt (tailAt P W).s2.L.M ((tailAt P W).b2 e).2) := rfl

theorem tAt_rt : (termsEAt P.tp ((tailAt P W).b3 e).2).rt = Blocks.nat
    ((tailAt P W).s3.L.Q.outPt (tailAt P W).s3.L.M ((tailAt P W).b3 e).2) := rfl

end Reads

section ReadsF

variable {E' : Type} [Field E'] [Fintype E'] [scl : Scl] {M X : Type} (P : FullPar E' M X)
  (e : (tailF P).s7.Nx)

theorem gAt_r5 : (gatedEAt P.fp ((tailF P).b5 e).2 ((tailF P).b6 e).2).r5 = Blocks.nat fun i =>
    (tailF P).s5.L.Q.outPt (tailF P).s5.L.M ((tailF P).b5 e).2 (P.fp.gp.e.symm i) := rfl

theorem gAt_r6 : (gatedEAt P.fp ((tailF P).b5 e).2 ((tailF P).b6 e).2).r6 = Blocks.nat fun i =>
    (tailF P).s6.L.Q.outPt (tailF P).s6.L.M ((tailF P).b6 e).2 (P.fp.rt.L.e.symm i) := rfl

end ReadsF

/-! ## The seven points at the chain's data off a tape -/

section Points

variable [scl : Scl] {M X : Type} (P : FullPar Cb.Gl.E M X) {R : TailR} (W' : TailM (tailF P) R)
  (k : Ks) (t : Tape) (nz : NzT (tailF P) k t) (a : Adds7 (tailF P)) (x : P.XT)

/-- The squares' point. -/
theorem r1_at {p : Psc} (O : OutIs gl (tailT W' k t nz a).d1 p)
    (hk : (tailF P).s1.L.S.k = k.k1) {rho : Array E} {C : Aff} {order : List ℕ} {F G : Fork}
    {u : Tape} {L : Level} (h : Fl.levelIn k.k1 rho C order F (k.tc1 t) = some (L, G, u))
    (hp : order.Perm (List.range (tailF P).s1.L.S.k))
    (he : P.nr.sq.R.L.e = ordE (tailF P).s1.L.S.k order hp) (zt : ℕ → Cb.Gl.E) {j : ℕ}
    (hj : j < (tailF P).s1.L.S.k) :
    pt gl L.r j = (eAt P.toOwnPar P.wPart ((tailT W' k t nz a).z7 x) zt).r1 j := by
  rw [eAt_r1, he]
  exact stgT_level_point W'.w1.num k.k1 (k.tc1 t) nz.b1 a.st1 a.t1 O hk h hp hj

/-- The norms' token point. d0: the words that the point's round drew. -/
theorem pV_at {PV : Array E} {d0 : List E} (hP : PV.toList = d0)
    (hx : ∀ i : Fin P.D.lT, x.2 i = gl.val (d0.getD i.val zeroE)) (zt : ℕ → Cb.Gl.E) {j : ℕ}
    (hj : j < P.D.lT) :
    pt gl PV j = (eAt P.toOwnPar P.wPart ((tailT W' k t nz a).z7 x) zt).pV j := by
  rw [eAt_pV]
  exact heard_point hP hx hj

/-- The batched sumcheck's end point. -/
theorem r4_at {p : Psc} (O : OutIs gl (tailT W' k t nz a).d4 p)
    (hk : (tailF P).s4.L.S.k = k.k4) {Pp : Pub} {v : Env} {H : Heard} {NCLp : ℕ} {F G : Fork}
    {u : Tape} {K : HeardStack}
    (h : hearStack engFl Pp v H k.k4 NCLp F (k.tc4 t) = some (K, G, u)) {j : ℕ}
    (hj : j < (tailF P).s4.L.S.k) :
    Blocks.nat ((tailF P).s4.L.Q.outPt (tailF P).s4.L.M
        ((tailF P).b4 ((tailT W' k t nz a).z7 x)).2) j =
      gl.val (K.rs.getD ((tailF P).s4.L.S.k - 1 - j) zeroE) :=
  stgT_stack_point W'.w4.num k.k4 (k.tc4 t) nz.b4 a.st4 a.t4 O hk h hj

/-- The end point of the token sumcheck of the row products. -/
theorem r2_at {p : Psc} (O : OutIs gl (tailT W' k t nz a).d2 p)
    (hk : (tailF P).s2.L.S.k = k.k2) {Pv : Array E} {n dY : ℕ} {F G : Fork} {u : Tape} {o : Tsc}
    (h : Fl.tscIn Pv k.k2 n dY F ((k.tcP t).drop 1) = some (o, G, u)) (zt : ℕ → Cb.Gl.E) {j : ℕ}
    (hj : j < (tailF P).s2.L.S.k) :
    pt gl o.r j = (eAt P.toOwnPar P.wPart ((tailT W' k t nz a).z7 x) zt).r2 j := by
  rw [eAt_r2]
  exact stgT_tsc_point W'.w2.num k.k2 ((k.tcP t).drop 1) nz.b2 a.st2 a.t2 O hk h hj

/-- The end point of the sumcheck of the terms. -/
theorem rt_at {p : Psc} (O : OutIs gl (tailT W' k t nz a).d3 p)
    (hk : (tailF P).s3.L.S.k = k.k3) {Pv : Array E} {n dY : ℕ} {F G : Fork} {u : Tape} {o : Tsc}
    (h : Fl.tscIn Pv k.k3 n dY F (((k.tcP t).drop 1).drop (k.k2 + 3)) = some (o, G, u)) {j : ℕ}
    (hj : j < (tailF P).s3.L.S.k) :
    pt gl o.r j = (termsEAt P.tp ((tailF P).b3 ((tailT W' k t nz a).z7 x)).2).rt j := by
  rw [tAt_rt]
  exact stgT_tsc_point W'.w3.num k.k3 (((k.tcP t).drop 1).drop (k.k2 + 3)) nz.b3 a.st3 a.t3 O hk h
    hj

/-- The first product layer of the gated products. -/
theorem r5_at {p : Psc} (O : OutIs gl (tailT W' k t nz a).d5 p)
    (hk : (tailF P).s5.L.S.k = k.k5) {rho : Array E} {C : Aff} {order : List ℕ} {F G : Fork}
    {u : Tape} {L : Level} (h : Fl.levelIn k.k5 rho C order F (k.tc5 t) = some (L, G, u))
    (hp : order.Perm (List.range (tailF P).s5.L.S.k))
    (he : P.fp.gp.e = ordE (tailF P).s5.L.S.k order hp) {j : ℕ}
    (hj : j < (tailF P).s5.L.S.k) :
    pt gl L.r j = (gatedEAt P.fp ((tailF P).b5 ((tailT W' k t nz a).z7 x)).2
      ((tailF P).b6 ((tailT W' k t nz a).z7 x)).2).r5 j := by
  rw [gAt_r5, he]
  exact stgT_level_point W'.w5.num k.k5 (k.tc5 t) nz.b5 a.st5 a.t5 O hk h hp hj

/-- The second product layer. -/
theorem r6_at {p : Psc} (O : OutIs gl (tailT W' k t nz a).d6 p)
    (hk : (tailF P).s6.L.S.k = k.k6) {rho : Array E} {C : Aff} {order : List ℕ} {F G : Fork}
    {u : Tape} {L : Level} (h : Fl.levelIn k.k6 rho C order F (k.tc6 t) = some (L, G, u))
    (hp : order.Perm (List.range (tailF P).s6.L.S.k))
    (he : P.fp.rt.L.e = ordE (tailF P).s6.L.S.k order hp) {j : ℕ}
    (hj : j < (tailF P).s6.L.S.k) :
    pt gl L.r j = (gatedEAt P.fp ((tailF P).b5 ((tailT W' k t nz a).z7 x)).2
      ((tailF P).b6 ((tailT W' k t nz a).z7 x)).2).r6 j := by
  rw [gAt_r6, he]
  exact stgT_level_point W'.w6.num k.k6 (k.tc6 t) nz.b6 a.st6 a.t6 O hk h hp hj

end Points

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.pV_at
#print axioms OnBytes.Road.K4.r4_at
#print axioms OnBytes.Road.K4.r1_at
#print axioms OnBytes.Road.K4.r2_at
#print axioms OnBytes.Road.K4.rt_at
#print axioms OnBytes.Road.K4.r5_at
#print axioms OnBytes.Road.K4.r6_at
#print axioms OnBytes.Road.K4.stgT_level_point
#print axioms OnBytes.Road.K4.stgT_tsc_point
