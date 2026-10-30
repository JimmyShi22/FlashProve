-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/TokRowFirst.lean: THE FIRST GROUP's twin of the part "at a hearing" of
Johnson/Road/K4/TokRow.lean: the own claim of the token sumcheck of the row products: where the
claim that the text of the layers' own rounds lists for it is worth 0, the form in which the
library's ledger of the first group's chain writes that sumcheck's first output claim is worth 0.

What is general in TokRow.lean (the library's summand written out; the tape's words) is imported.
The calls and ledgers are the record LedG (Johnson/Road/K4/OwnLedgersG.lean), which holds in
every group. The statements and proofs here are that file's, turned to the first group's letters by
a program and compiled; each name bears an F.

Main names: `d4_of_ledF`: (D4) of the second stage at a hearing · `u2_of_ledF`: the ledger's form is
worth 0.
Limits. As TokRow.lean's: LedG; NumTiesF; that the state a.st2 holds the element that the products'
round drew and the target a.t2 is the record's; StgFits; the lawful pick; (D1); (D2); that the
ledger at which the claims are made is later than the hearing's; that the stage has one further
scalar; three equations on public numbers: all premises. One direction: from returns. Nothing on
soundness.


-/
import Johnson.Road.K4.TokRow
import Johnson.Road.K4.SlotsOfLedFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Finset
open Iop Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Reading World Fork Psc Level Tsc Aff ledNP ledNO)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard)
open OnBytes.Tie.Pv.Lay (RecAt StgFits)
open OnBytes.Desc.First.P1 (gl Ks NzT Adds7 TailM TailR pscT stgT sentOf tapeEps tscWs)
open OnBytes.Desc.First.K4 (k0 rowsSummand rowsSummand_val powers_val formsFrontWith
  formsFrontWith_some mem_front)
open D6.Bridge (pairA pairB sumTerms_pr)
open Inst.Model (Scl)

/-! ## At a hearing -/

section Led

variable [scl : Scl] {M X : Type} (Pf : FullFPar Cb.Gl.E M X) {R : TailR} (W' : TailM (tailW Pf) R)
  {P : Pub} {hp : HPlan2} {g : ℕ} {fo : OnBytes.Model.Forest.Heard} {o : Own} {F G : Fork}
  {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc} {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork}
  {u5 : Tape}

/-- **(D4) at a hearing**: the library's summand on the stage's end values, at any point z, is the
text's summand on what the ledger F0 shows, read. -/
theorem d4_of_ledF (Ld : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (nz : NzT (tailW Pf) (ksOf P hp) (t0.drop (k0 g))) (a : Adds7 (tailW Pf))
    (Nm : NumTiesF Pf W' P.y.LamM) (hNI : P.y.NI = Pf.D.nNu) (hNP : ledNP P.y.h.xl = 7)
    (hNO : ledNO P.y.h.xl = 4)
    (hst : (a.st2 : Pf.ofp.nr.rows.X2).2 = gl.val (tapeEps ((ksOf P hp).tcP (t0.drop (k0 g)))))
    {F0 : Fork} (l0 : Fo.Later G F0) {sh : Array E}
    (hsh : ((Array.range (4 * P.y.NI)).mapM fun i => F0.shown (o.H.tV.sEnd + i)) = some sh)
    (z : Fin Pf.D.lT → Cb.Gl.E) :
    Pf.ofp.nr.rows.tok.Sm.pol a.st2 z (k4TailG W' P hp g t0 nz a).d2.v =
      gl.val (rowsSummand P.y o.H sh) := by
  obtain ⟨v2, c2⟩ := Ld.c2
  have hom : ∀ m, m < 7 * P.y.NI → gl.val (o.H.omV.getD m zeroE) =
      gl.val (tapeEps ((ksOf P hp).tcP (t0.drop (k0 g)))) ^ m := fun m hm =>
    (congrArg (fun w : Array E => gl.val (w.getD m zeroE)) (Ld.kOmV.trans Ld.omV)).trans
      (powers_val gl _ (n := ledNP P.y.h.xl * P.y.NI) (s := m) (by rw [hNP]; exact hm))
  have hv : ∀ q : Fin Pf.D.nNu × Fin 4, (k4TailG W' P hp g t0 nz a).d2.v q =
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
      tsc_shown_psc Ld.s8 c2 (Ld.g1.trans l0) (by rw [hNO]; exact hq) (tailW Pf).s2.n, ← e1]
    rfl
  rw [rows_pol Pf.ofp.nr a.st2 z (fun e => gl.val (sh.getD e zeroE)) _ hv, hst,
    rowsSummand_val gl P.y o.H sh _ hom, sumTerms_pr, hNI]

/-- **The ledger's form of the sumcheck's first output claim is worth 0**, where the claims of the
text's run "front" are worth 0 in the world W1 of the ledger that the run returns. -/
theorem u2_of_ledF (Ld : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (nz : NzT (tailW Pf) (ksOf P hp) (t0.drop (k0 g))) (a : Adds7 (tailW Pf)) (x : Pf.ofp.fs.X3)
    (Nm : NumTiesF Pf W' P.y.LamM) (hNI : P.y.NI = Pf.D.nNu) (hNP : ledNP P.y.h.xl = 7)
    (hNO : ledNO P.y.h.xl = 4)
    (hst : (a.st2 : Pf.ofp.nr.rows.X2).2 = gl.val (tapeEps ((ksOf P hp).tcP (t0.drop (k0 g)))))
    (hn : (tailW Pf).s2.n = 1) (ht : a.t2 = H1.tV.p.target)
    (f : StgFits gl (tailW Pf).s2 a.st2 (tscWs (H1.PV.toList.take P.y.h.lt)) P.y.h.lt 2)
    (hF : ∀ st, HFixs.OK _ ((tailW Pf).s2.F st)) (Ex : ExtSpec) (y : Ex.Str) {F0 F1 : Fork}
    (l0 : Fo.Later G F0) {rows : Bool} {fs : Array Aff}
    (h : formsFrontWith rows P g o F0 = some (fs, F1)) (W1 : World Cb.Gl.E)
    (hz : ∀ q ∈ fs.toList, q.value gl W1 = 0) (m : M)
    (D1 : (tailW Pf).s2.L.T.par.W a.st2 (Pf.msg m) =
      OnBytes.Road.Hd.place W1.slot ((tailW Pf).s2.L.T.par.vars a.st2) H1.tV.p.first)
    (D2 : (tailW Pf).s2.L.T.par.inc a.st2 (Pf.msg m) =
      gl.val H1.tV.p.target - H1.tV.p.start.value gl W1)
    {J₂ : Type} [Fintype J₂] (w : J₂ → Cb.Gl.E) :
    Blocks.Form.val (Sum.elim (Pf.msg m) w)
      (u2At Pf.ofp.nr ((tailW Pf).b2 ((k4TailG W' P hp g t0 nz a).z7 x)).2) = 0 := by
  obtain ⟨v2, c2⟩ := Ld.c2
  obtain ⟨sh, pp, l, _, _, hsh, _, hl, hfs, _⟩ := formsFrontWith_some h
  have hmem : o.H.tV.p.rowForm (rowsSummand P.y o.H sh) {} ∈ fs.toList := by
    rw [hfs]
    exact (mem_front hl).2.2.1
  have hrow : (H1.tV.p.rowForm (rowsSummand P.y o.H sh) {}).value gl W1 = 0 := by
    have q := hz _ hmem
    rw [Ld.kTV] at q
    exact q
  exact (stgT_rowUp W'.w2.num P.y.h.lt (((ksOf P hp).tcP (t0.drop (k0 g))).drop 1) nz.b2 a.st2
    a.t2 hn (tsc_recAt c2) ht f hF Ex y W1 (rowsSummand P.y o.H sh) {} (Pf.msg m) D1 D2
    (by
      rw [Aff.value_empty]
      exact Finset.sum_eq_zero fun b _ => (show Empty from b).elim)
    (d4_of_ledF Pf W' Ld nz a Nm hNI hNP hNO hst l0 hsh _)
    (fun _ b _ _ => Empty.elim b) (fun _ _ b _ => Empty.elim b) w).1 hrow

end Led

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.d4_of_ledF
#print axioms OnBytes.Road.K4.u2_of_ledF
