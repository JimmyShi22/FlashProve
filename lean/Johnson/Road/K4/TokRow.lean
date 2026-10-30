-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/TokRow.lean: the own claim of the token sumcheck of the row products: where the
claim that the text of the layers' own rounds lists for it is worth 0, the form in which the
library's ledger writes that sumcheck's first output claim (u2At, Cb/Pv/Lay/End/NormsRows.lean) is
worth 0.

Johnson/Road/K4/OwnRows.lean (stgT_rowUp) holds a record's row form against the ledger's form at a
stage's own typed output, under four conditions (D1) to (D4). Here two of them are shown for the
second stage. (D3): the stage has no kept map, and the text hands the empty form to its row. (D4):
the library's summand on the end values (LdPartSm.pol, Cb/Part/LdPartPsc.lean, at the terms of
Cb/Pv/Lay/Rows.lean and Cb/Pv/Lay/At/Norms.lean) is the text's summand rowsSummand
(OnBytes/Desc/First/K4/Claims.lean), read: both are the sum over the norms ν and the seven products
r of the power 7 ν + r of the batching element times two of the four end values of ν, and the seven
pairs stand in the same order on both sides.

Main names:
  `tok_pol`: the library's summand of a sumcheck of products, written out.
  `facs_pair`, `pr_val`, `rows_pol`: at the norms' rows: as one sum over 7 nNu numbers.
  `tsc_shown_psc`: what a later ledger shows under a token sumcheck's end values, in pscT's words.
  `d4_of_led`: (D4) at a hearing. `u2_of_led`: the ledger's form is worth 0.
Limits. PREMISES OF u2_of_led, NONE SHOWN HERE: Led7; NumTies; that the state a.st2 holds the
element that the products' round drew (hst) and the target a.t2 is the record's (ht); StgFits; the
lawful pick (hF); (D1): the sumcheck's own mask coefficients; (D2): the incoming form; that the
ledger at which the claims are made is later than the hearing's; that the stage has one further
scalar; three equations on public numbers. One direction: from returns. A group that is not the
first. Nothing on soundness.


-/
import Johnson.Road.K4.OwnRows
import Johnson.Road.K4.SlotsOfLed
import Johnson.Road.K4.PointsOfLed
import Johnson.Road.K4.NormsConsts
import OnBytes.Desc.First.K4.BatchLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Finset
open Iop Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Reading World Fork Psc Level Tsc Aff ledNP ledNO)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard)
open OnBytes.Tie.Pv.Lay (RecAt StgFits)
open OnBytes.Desc.First.P1 (gl Ks NzT Adds7 TailM TailR pscT stgT sentOf tapeEps tscWs tsc_shown
  tscIn_heard tscVals)
open OnBytes.Desc.First.K4 (rowsSummand rowsSummand_val powers_val formsFrontWith
  formsFrontWith_some mem_front)
open D6.Bridge (pairA pairB sumTerms_pr)
open Inst.Model (Scl)

/-! ## The library's summand, written out -/

section Algebra

variable {E' : Type} [Field E'] [Fintype E']

/-- The summand of a sumcheck of products on values v of the shown vectors: product n under the
power n of the state's batching element. It does not read the point. -/
theorem tok_pol (L : RowsL E') (st : L.X2) (z : Fin L.k → E') (v : L.A → E') :
    L.tok.Sm.pol st z v = ∑ n : Fin L.np, st.2 ^ (n : ℕ) * (v (L.pr n).1 * v (L.pr n).2) := by
  unfold LdPartSm.pol
  rw [Fin.sum_univ_def]
  show ((((List.finRange L.np).map _).map L.tok.tm).map _).sum = _
  rw [List.map_map, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun n _ => ?_)
  simp [TokL.tm]

/-- The library's seven pairs of factors are the text's. -/
theorem facs_pair : ∀ r : Fin 7,
    ((facs r).1 : ℕ) = pairA (r : ℕ) ∧ ((facs r).2 : ℕ) = pairB (r : ℕ) := by decide

variable [scl : Scl] (Pn : NormPar0 E')

/-- The two factors of product n of the norms' rows, on values that are read off one list f: end
value k of norm ν at place 4 ν + k. -/
theorem pr_val (f : ℕ → E') (v : Fin Pn.D.nNu × Fin 4 → E')
    (hv : ∀ q, v q = f (4 * (q.1 : ℕ) + (q.2 : ℕ))) (n : Fin (Pn.D.nNu * 7)) :
    v (Pn.rows.pr n).1 = f (4 * ((n : ℕ) / 7) + pairA ((n : ℕ) % 7)) ∧
      v (Pn.rows.pr n).2 = f (4 * ((n : ℕ) / 7) + pairB ((n : ℕ) % 7)) := by
  constructor
  · rw [hv]
    show f (4 * ((n : ℕ) / 7) + ((facs (finProdFinEquiv.symm n).2).1 : ℕ)) = _
    rw [(facs_pair _).1]
    rfl
  · rw [hv]
    show f (4 * ((n : ℕ) / 7) + ((facs (finProdFinEquiv.symm n).2).2 : ℕ)) = _
    rw [(facs_pair _).2]
    rfl

/-- The library's summand at the norms' rows, as one sum over 7 nNu numbers. -/
theorem rows_pol (st : Pn.rows.X2) (z : Fin Pn.D.lT → E') (f : ℕ → E')
    (v : Fin Pn.D.nNu × Fin 4 → E') (hv : ∀ q, v q = f (4 * (q.1 : ℕ) + (q.2 : ℕ))) :
    Pn.rows.tok.Sm.pol st z v = ∑ m ∈ range (7 * Pn.D.nNu),
      st.2 ^ m * (f (4 * (m / 7) + pairA (m % 7)) * f (4 * (m / 7) + pairB (m % 7))) := by
  rw [tok_pol Pn.rows st z v, Nat.mul_comm 7,
    ← Fin.sum_univ_eq_sum_range
      (fun m => st.2 ^ m * (f (4 * (m / 7) + pairA (m % 7)) * f (4 * (m / 7) + pairB (m % 7))))
      (Pn.D.nNu * 7)]
  exact Finset.sum_congr rfl fun n _ => by
    rw [(pr_val Pn f v hv n).1, (pr_val Pn f v hv n).2]

end Algebra

/-! ## The tape's words -/

/-- Every later ledger shows, under a token sumcheck's end values' slots, what the values round
sent, in the words that the chain's data read. -/
theorem tsc_shown_psc {Pt : Array E} {lt nn dY : ℕ} {F G : Fork} {t u : Tape} {o : Tsc}
    (hF : OnBytes.PscRun.Sized F) (h : Fl.tscIn Pt lt nn dY F t = some (o, G, u)) {Hl : Fork}
    (lH : Fo.Later G Hl) {e : ℕ} (he : e < nn) (n : ℕ) :
    Hl.vp.getD (o.sEnd + e) zeroE = (pscT n lt t).v.getD e zeroE := by
  have hl : (Pt.toList.take lt).length = lt := by
    rw [List.length_take, Array.length_toList]
    exact Nat.min_eq_left (tscIn_heard h).1
  rw [tsc_shown hF h Hl lH e he]
  unfold tscVals
  rw [hl]
  rfl

/-! ## At a hearing -/

section Led

variable [scl : Scl] {M X : Type} (Pf : FullPar Cb.Gl.E M X) {R : TailR} (W' : TailM (tailF Pf) R)
  {P : Pub} {hp : HPlan2} {g : ℕ} {fo : OnBytes.Model.Forest.Heard} {o : Own} {F G : Fork}
  {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc} {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}

/-- **(D4) at a hearing**: the library's summand on the stage's end values, at any point z, is the
text's summand on what the ledger F0 shows, read. -/
theorem d4_of_led (Ld : Led7 P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (nz : NzT (tailF Pf) (ksOf P hp) (t0.drop 1)) (a : Adds7 (tailF Pf))
    (Nm : NumTies Pf W' P.y.LamM) (hNI : P.y.NI = Pf.D.nNu) (hNP : ledNP P.y.h.xl = 7)
    (hNO : ledNO P.y.h.xl = 4)
    (hst : (a.st2 : Pf.nr.rows.X2).2 = gl.val (tapeEps ((ksOf P hp).tcP (t0.drop 1))))
    {F0 : Fork} (l0 : Fo.Later G F0) {sh : Array E}
    (hsh : ((Array.range (4 * P.y.NI)).mapM fun i => F0.shown (o.H.tV.sEnd + i)) = some sh)
    (z : Fin Pf.D.lT → Cb.Gl.E) :
    Pf.nr.rows.tok.Sm.pol a.st2 z (k4Tail W' P hp t0 nz a).d2.v =
      gl.val (rowsSummand P.y o.H sh) := by
  obtain ⟨v2, c2⟩ := Ld.c2
  have hom : ∀ m, m < 7 * P.y.NI → gl.val (o.H.omV.getD m zeroE) =
      gl.val (tapeEps ((ksOf P hp).tcP (t0.drop 1))) ^ m := fun m hm =>
    (congrArg (fun w : Array E => gl.val (w.getD m zeroE)) (Ld.kOmV.trans Ld.omV)).trans
      (powers_val gl _ (n := ledNP P.y.h.xl * P.y.NI) (s := m) (by rw [hNP]; exact hm))
  have hv : ∀ q : Fin Pf.D.nNu × Fin 4, (k4Tail W' P hp t0 nz a).d2.v q =
      gl.val (sh.getD (4 * (q.1 : ℕ) + (q.2 : ℕ)) zeroE) := by
    intro q
    have hq : 4 * (q.1 : ℕ) + (q.2 : ℕ) < 4 * P.y.NI := by
      have h1 := q.1.2
      have h2 := q.2.2
      rw [hNI]
      omega
    have e1 : W'.w2.num q = 4 * (q.1 : ℕ) + (q.2 : ℕ) := by
      rw [Nm.n2, finProdFinEquiv_apply_val]
      exact Nat.add_comm _ _
    rw [shown_at hsh hq, congrArg Tsc.sEnd Ld.kTV,
      tsc_shown_psc Ld.s8 c2 (Ld.g1.trans l0) (by rw [hNO]; exact hq) (tailF Pf).s2.n, ← e1]
    rfl
  rw [rows_pol Pf.nr a.st2 z (fun e => gl.val (sh.getD e zeroE)) _ hv, hst,
    rowsSummand_val gl P.y o.H sh _ hom, sumTerms_pr, hNI]

/-- **The ledger's form of the sumcheck's first output claim is worth 0**, where the claims of the
text's run "front" are worth 0 in the world W1 of the ledger that the run returns. -/
theorem u2_of_led (Ld : Led7 P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (nz : NzT (tailF Pf) (ksOf P hp) (t0.drop 1)) (a : Adds7 (tailF Pf)) (x : Pf.XT)
    (Nm : NumTies Pf W' P.y.LamM) (hNI : P.y.NI = Pf.D.nNu) (hNP : ledNP P.y.h.xl = 7)
    (hNO : ledNO P.y.h.xl = 4)
    (hst : (a.st2 : Pf.nr.rows.X2).2 = gl.val (tapeEps ((ksOf P hp).tcP (t0.drop 1))))
    (hn : (tailF Pf).s2.n = 1) (ht : a.t2 = H1.tV.p.target)
    (f : StgFits gl (tailF Pf).s2 a.st2 (tscWs (H1.PV.toList.take P.y.h.lt)) P.y.h.lt 2)
    (hF : ∀ st, HFixs.OK _ ((tailF Pf).s2.F st)) (Ex : ExtSpec) (y : Ex.Str) {F0 F1 : Fork}
    (l0 : Fo.Later G F0) {rows : Bool} {fs : Array Aff}
    (h : formsFrontWith rows P g o F0 = some (fs, F1)) (W1 : World Cb.Gl.E)
    (hz : ∀ q ∈ fs.toList, q.value gl W1 = 0) (m : M)
    (D1 : (tailF Pf).s2.L.T.par.W a.st2 (Pf.msg m) =
      OnBytes.Road.Hd.place W1.slot ((tailF Pf).s2.L.T.par.vars a.st2) H1.tV.p.first)
    (D2 : (tailF Pf).s2.L.T.par.inc a.st2 (Pf.msg m) =
      gl.val H1.tV.p.target - H1.tV.p.start.value gl W1)
    {J₂ : Type} [Fintype J₂] (w : J₂ → Cb.Gl.E) :
    Blocks.Form.val (Sum.elim (Pf.msg m) w)
      (u2At Pf.nr ((tailF Pf).b2 ((k4Tail W' P hp t0 nz a).z7 x)).2) = 0 := by
  obtain ⟨v2, c2⟩ := Ld.c2
  obtain ⟨sh, pp, l, _, _, hsh, _, hl, hfs, _⟩ := formsFrontWith_some h
  have hmem : o.H.tV.p.rowForm (rowsSummand P.y o.H sh) {} ∈ fs.toList := by
    rw [hfs]
    exact (mem_front hl).2.2.1
  have hrow : (H1.tV.p.rowForm (rowsSummand P.y o.H sh) {}).value gl W1 = 0 := by
    have q := hz _ hmem
    rw [Ld.kTV] at q
    exact q
  exact (stgT_rowUp W'.w2.num P.y.h.lt (((ksOf P hp).tcP (t0.drop 1)).drop 1) nz.b2 a.st2 a.t2 hn
    (tsc_recAt c2) ht f hF Ex y W1 (rowsSummand P.y o.H sh) {} (Pf.msg m) D1 D2
    (by
      rw [Aff.value_empty]
      exact Finset.sum_eq_zero fun b _ => (show Empty from b).elim)
    (d4_of_led Pf W' Ld nz a Nm hNI hNP hNO hst l0 hsh _)
    (fun _ b _ _ => Empty.elim b) (fun _ _ b _ => Empty.elim b) w).1 hrow

end Led

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.tok_pol
#print axioms OnBytes.Road.K4.facs_pair
#print axioms OnBytes.Road.K4.pr_val
#print axioms OnBytes.Road.K4.rows_pol
#print axioms OnBytes.Road.K4.tsc_shown_psc
#print axioms OnBytes.Road.K4.d4_of_led
#print axioms OnBytes.Road.K4.u2_of_led
