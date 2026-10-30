-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/StackTiesAt.lean: the record StackTies (Johnson/Road/K4/StackTyped.lean), which the
port of the batched sumcheck's two side claims asks, at the last statement made from the chain's
data off a tape (tailT): five of its seven clauses concluded.

The state of the typed batched sumcheck is read off the chain's statement
(Cb/Pv/Lay/At/Mid.lean: st4): the output of the sumcheck of the terms, the element drawn, the
lookup's point. Where the letters' claim of the fourth stage holds (TailH.Claims.c4), the state in
the data is that state.

Main names:
  `st_of_claim`: the state in the fourth stage's output is the chain's.
  `o3_vals`: what the output of the sumcheck of the terms shows, in the words of the tape.
  `stackTies_at`: StackTies, at zh := the reading of the verifier's end point of the sumcheck of the
    terms.
Limits. The two clauses on the lookup's point (z0, z3) are premises as they stand. Premises beside:
the fourth stage's claim; OutIs at the third stage; the token sumcheck's return on the stage's tape;
the numbering of the end values; three sizes; that shownT holds the words of the values' round; that
om's entry 1 reads as the word drawn. Identities on public numbers: nothing on a world, on a draw,
on soundness or on hiding.


-/
import Johnson.Road.K4.PointsAt
import Johnson.Road.K4.StackTyped

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End
open OnBytes OnBytes.K.Kc
open Inst.Model (Scl)
open OnBytes.Model (Fork Psc Tsc)
open OnBytes.Model.Layer (Lay)
open OnBytes.Tie.Pv.Lay (OutIs)
open OnBytes.Desc.First.P1 (gl pscT Ks NzT Adds7 tailT TailM TailR tapeEps tscIn_heard tscWs)

variable [scl : Scl] {M X : Type} (P : FullPar Cb.Gl.E M X) {R : TailR} (W' : TailM (tailF P) R)
  (k : Ks) (t : Tape) (nz : NzT (tailF P) k t) (a : Adds7 (tailF P)) (x : P.XT)

/-- The state in the fourth stage's output is the chain's. -/
theorem st_of_claim (hc : (tailT W' k t nz a).d4.Claim ((tailT W' k t nz a).y4 x)) :
    ((tailF P).b4 ((tailT W' k t nz a).z7 x)).2.st =
      ((tailF P).s4.cl ((tailT W' k t nz a).y4 x) (tailT W' k t nz a).d4.rd).2 :=
  (congrArg Prod.snd hc).symm

/-- What the output of the sumcheck of the terms shows. -/
theorem o3_vals {p : Psc} (O : OutIs gl (tailT W' k t nz a).d3 p)
    (hnum : ∀ q : ShA P.D, W'.w3.num q = numA P.D q) (q : ShA P.D) :
    (tailT W' k t nz a).d3.out.vals q =
      gl.val ((pscT 0 k.k3 (((k.tcP t).drop 1).drop (k.k2 + 3))).v.getD (numA P.D q) zeroE) := by
  rw [congrFun O.vals q, ← hnum q]
  rfl

/-- **StackTies at the chain's data off a tape.** -/
theorem stackTies_at (hc : (tailT W' k t nz a).d4.Claim ((tailT W' k t nz a).y4 x)) {p : Psc}
    (O : OutIs gl (tailT W' k t nz a).d3 p) (hk : (tailF P).s3.L.S.k = k.k3) {Pv : Array E}
    {nn dY : ℕ} {F G : Fork} {u : Tape} {o : Tsc}
    (h : Fl.tscIn Pv k.k3 nn dY F (((k.tcP t).drop 1).drop (k.k2 + 3)) = some (o, G, u))
    (hnum : ∀ q : ShA P.D, W'.w3.num q = numA P.D q) {yl : Lay}
    (hN : yl.NN * yl.Lam = P.D.nNu) (hM : yl.LamM = P.D.ne) (hE : yl.h.NE = P.D.nx)
    {shownT om : Array E}
    (hsh : ∀ n, n < P.D.nNu + P.D.ne + P.D.ne * P.D.nx → shownT.getD n zeroE =
      (pscT 0 k.k3 (((k.tcP t).drop 1).drop (k.k2 + 3))).v.getD n zeroE)
    (hom : gl.val (om.getD 1 zeroE) = gl.val (tapeEps (k.tc4 t))) {z : ℕ → Cb.Gl.E}
    (hz0 : ((tailF P).b4 ((tailT W' k t nz a).z7 x)).2.st.z = z)
    (hz3 : P.ip.zP ((tailF P).b4 ((tailT W' k t nz a).z7 x)).2.st .QK = z) :
    StackTies P.ip ((tailF P).b4 ((tailT W' k t nz a).z7 x)).2.st gl yl shownT om z
      (pt gl o.r) := by
  have hs := st_of_claim P W' k t nz a x hc
  have hv : ∀ q : ShA P.D, ((tailF P).b4 ((tailT W' k t nz a).z7 x)).2.st.o3.vals q =
      gl.val ((pscT 0 k.k3 (((k.tcP t).drop 1).drop (k.k2 + 3))).v.getD (numA P.D q) zeroE) := by
    intro q
    rw [hs]
    exact o3_vals P W' k t nz a O hnum q
  have hrt : P.ip.rt ((tailF P).b4 ((tailT W' k t nz a).z7 x)).2.st = Blocks.nat
      ((tailF P).s3.L.Q.outPt (tailF P).s3.L.M (tailT W' k t nz a).d3.out) := by
    rw [hs]
    rfl
  refine ⟨hz0, hz3, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrt]
    funext j
    by_cases hj : j < (tailF P).s3.L.S.k
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

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.stackTies_at
