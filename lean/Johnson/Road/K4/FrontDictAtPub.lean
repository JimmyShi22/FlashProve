-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/FrontDictAtPub.lean: the dictionary FrontDict
(Johnson/Road/K4/ValuesOfClaims.lean) at a run's record whose environment is that of a public record
Pub34 (Johnson/Road/Rows/LayerEnds34.lean), on true reads: the records of true tables that
Johnson/Road/K4/FrontDictOf.lean asks are paid by Johnson/Road/K4/TruthsOfPub.lean.

  `frontDict_at`: FrontDict, from: a record X with ReadsTrue; a run's record o with o.v = X.p.v;
    sizes; the library's three records on the library-side entries, at the cells of the matrices
    Mm; PointTies at the readings of the verifier's own points; SlotTies; K4's run "front" returns.
Limits. All of these are premises. With routed experts and a second product layer alone. Nothing on
a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.FrontDictOf
import Johnson.Road.K4.TruthsOfPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes.Model (World Aff Fork Level lastOf)
open OnBytes.Model.Layer (Pub Own)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell lF lFe zpos)
open Cb.Pv.Lay.End (NormsNames NormsE TermsNames TermsE TablesTrue TermsTrue)
open Cb.Pv.Lay.End.Gated (GatedNames GatedE GatedTables)

variable {K : Type} [Field K] {J : Type}

/-- **FrontDict at a record Pub34, on true reads.** -/
theorem frontDict_at [scl : Scl] (X : Rows.Pub34 K) (Wo : World K) (Mm : Mats K)
    (hRd : X.ReadsTrue Wo Mm) (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam) {P : Pub}
    {o : Own} (hv : o.v = X.p.v) {o2 : Level} (h2 : o.hd2 = some o2) (h2X : X.hd2 = some o2)
    (hyv : o.v.y = P.y) {b B sG : ℕ} (hls : o.v.y.ls = sG) {D : Dim} (hD : X.D = D)
    (Z : P.y.Lam = 2 ^ D.lL ∧ P.y.h.f / P.y.S2 = 2 ^ (lF D - P.y.ls) ∧
      P.y.LamM = 2 ^ (D.lL - 1) ∧ P.y.h.fe / P.y.S2 = 2 ^ (lFe D - P.y.ls) ∧ P.y.xb.nl = 5 ∧
      Model.ledNP P.y.h.xl * P.y.NI = 7 * D.nNu ∧ P.y.NI = D.nNu)
    (hB : P.y.h.d / P.y.S2 = B) (h0 : 0 < D.nNu) {t : Cell → K}
    (ht : cellsOf D (cellsAt X.p.v.y Mm) = t) {NN : NormsNames J} {eN : NormsE K}
    {NT : TermsNames J} {eT : TermsE K} {NG : GatedNames J} {eG : GatedE K} {y : J → K}
    (TN : TablesTrue NN eN D t (D.lL + 1) b sG B y) (TT : TermsTrue NT eT D t y)
    (TG : GatedTables NG eG D t sG y)
    (hPt : ∀ ZV ZA ZB, lastOf X.H.wpl.r X.p.v.y.h.la = .ok ZV →
      lastOf X.hd.r X.p.v.y.h.la = .ok ZA → lastOf o2.r X.p.v.y.h.la = .ok ZB →
      PointTies D eN eT eG b sG (zpos D (zOf X.ρ X.H.fo.zx X.H.fo.zy)) (pt X.ρ X.c.rt)
        (pt X.ρ X.c.rt) (pt X.ρ ZV) (fun j => pt X.ρ ZV (sG + j)) (pt X.ρ X.H.PV)
        (pt X.ρ X.H.tV.r) (pt X.ρ ZA) (fun j => pt X.ρ ZA (sG + j)) (pt X.ρ ZB)
        (fun j => pt X.ρ ZB (sG + j)))
    (Sl : SlotTies X.ρ Wo P o D NN eN NT eT NG eG b B sG y) {g : ℕ} {rows : Bool} {F0 G : Fork}
    {fs : Array Aff} (h : Desc.First.K4.formsFrontWith rows P g o F0 = some (fs, G)) :
    FrontDict X.ρ Wo P o D NN eN NT eT NG eG b B sG y := by
  subst hD
  subst ht
  obtain ⟨ZV, ZA, ZB, a1, a2, a3, PF, T2, T3, T4, L, S⟩ := truths_of_pub34 X Wo Mm hRd h2X
  rw [← hscl] at PF
  have hlsX : X.p.v.y.ls = sG := by rw [← hv]; exact hls
  rw [hlsX] at T3 T4
  exact frontDict_of hyv hls Z hB h0 (c := cellsAt X.p.v.y Mm) (by rw [hv]; exact PF.fits)
    (by rw [hv]; exact T2) (by rw [hv]; exact T3) (by rw [hv]; exact T4) (by rw [hv]; exact PF)
    (by rw [hv]; exact L) (by rw [hv]; exact S) TN TT TG (hPt ZV ZA ZB a1 a2 a3) Sl h2 h

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.frontDict_at
