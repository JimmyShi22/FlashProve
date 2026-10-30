-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/SevenParts.lean: seven of the eight parts of the library's ledger of a layers'
sub-proof hold at the late entries' forms' values, where the claims of K4's two runs are worth 0 on
true reads: called in one theorem.

  `seven_parts`: the parts sq, bat, led, terms, gated, hot and stack of clF (the ledger clAt at the
    names, late entries and forms of Johnson/Road/K4/LateNames.lean) hold of yL (the messages, and
    each late entry at its form's value: Johnson/Road/K4/LateMeet.lean).
It calls: parts_of_claims (PartsOfClaims.lean) · frontDict_at (FrontDictAtPub.lean) · late_norms,
late_terms, late_gated (LateMeet.lean) · normsOk_of, termsOk_of, gatedOk_of (LateNames.lean) ·
stack_port_pub34 (StackAtPub.lean).
What is asked, and by nothing here shown:
  a public record X : Pub34 and a run's record o with the same environment and second product layer;
  two worlds, W1 for the run "front" and W2 for the run "back", in each of which every table of the
    reads holds what it says of the matrices Mm (ReadsTrue);
  the forms of the run "front" are worth 0 in W1; the record's two claims on the sides' hidden end
    values are worth 0 in W2;
  the typed parameters' table of scales, sizes, tables and first layer are the record's, and the
    typed cells at the messages m are the cells of Mm;
  sizes (those of FrontDict, NormsOk and GatedOk);
  PointTies, SlotTies (FrontDictOf.lean) in W1; StackTies (StackTyped.lean), the number of rounds,
    the end point and the two hidden end values of the batched sumcheck in W2;
  the five claims that the sumchecks themselves leave are worth 0 at yL.
Limits. All of these are premises. The part merge is not spoken of. With routed experts and a second
product layer alone. Implications in given worlds: no draw, nothing on soundness or on hiding.


-/
import Johnson.Road.K4.PartsOfClaims
import Johnson.Road.K4.FrontDictAtPub
import Johnson.Road.K4.LateNames
import Johnson.Road.K4.StackAtPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open TWhole Cb Cb.Sub Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes.Model (World Fork Level lastOf)
open OnBytes.Model.Layer (Pub Own)
open Inst.Model (Scl)
open Inst.Model.FFSeg (lDd lF lFe zpos)

variable {K : Type} [Field K] [Fintype K] [scl : Scl] {M X0 : Type} (P : FullPar K M X0)
  (b B sG : ℕ) (R : (tailF P).s7.Nx → Rest3 K (P.J ⊕ J3 (roomFor P.D B sG)))
  (zt : (tailF P).s7.Nx → ℕ → K) (e : (tailF P).s7.Nx) (m : M)

/-- **Seven parts of the ledger at the late entries' forms' values.** -/
theorem seven_parts (X : Rows.Pub34 K) (W1 W2 : World K) (Mm : Mats K)
    (hR1 : X.ReadsTrue W1 Mm) (hR2 : X.ReadsTrue W2 Mm)
    (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam) {Pp : Pub} {o : Own}
    (hv : o.v = X.p.v) {o2 : Level} (h2 : o.hd2 = some o2) (h2X : X.hd2 = some o2)
    (hyv : o.v.y = Pp.y) (hls : o.v.y.ls = sG) (hD : X.D = P.D) (htb : X.tb = P.ip.tb)
    (hL0 : X.c.v.g * X.c.v.y.Lam = P.ip.L0)
    (Z : Pp.y.Lam = 2 ^ P.D.lL ∧ Pp.y.h.f / Pp.y.S2 = 2 ^ (lF P.D - Pp.y.ls) ∧
      Pp.y.LamM = 2 ^ (P.D.lL - 1) ∧ Pp.y.h.fe / Pp.y.S2 = 2 ^ (lFe P.D - Pp.y.ls) ∧
      Pp.y.xb.nl = 5 ∧ Model.ledNP Pp.y.h.xl * Pp.y.NI = 7 * P.D.nNu ∧ Pp.y.NI = P.D.nNu)
    (hB : Pp.y.h.d / Pp.y.S2 = B) (h0 : 0 < P.D.nNu)
    (nl : lDd P.D = b + sG) (nd : P.D.d = B * 2 ^ sG) (nB : B ≤ 2 ^ b)
    (g1 : 1 ≤ P.D.lL) (gs1 : sG ≤ lF P.D) (gs2 : sG ≤ lFe P.D) (gfe : P.D.fe = 2 ^ lFe P.D)
    (hcells : cellsOf P.D (cellsAt X.p.v.y Mm) = P.rd (P.msg m))
    (hPt : ∀ ZV ZA ZB, lastOf X.H.wpl.r X.p.v.y.h.la = .ok ZV →
      lastOf X.hd.r X.p.v.y.h.la = .ok ZA → lastOf o2.r X.p.v.y.h.la = .ok ZB →
      PointTies P.D (eAt P.toOwnPar P.wPart e (zt e)) (termsEAt P.tp ((tailF P).b3 e).2)
        (gatedEAt P.fp ((tailF P).b5 e).2 ((tailF P).b6 e).2) b sG
        (zpos P.D (zOf X.ρ X.H.fo.zx X.H.fo.zy)) (pt X.ρ X.c.rt) (pt X.ρ X.c.rt) (pt X.ρ ZV)
        (fun j => pt X.ρ ZV (sG + j)) (pt X.ρ X.H.PV) (pt X.ρ X.H.tV.r) (pt X.ρ ZA)
        (fun j => pt X.ρ ZA (sG + j)) (pt X.ρ ZB) (fun j => pt X.ρ ZB (sG + j)))
    (Sl : SlotTies X.ρ W1 Pp o P.D
      (namesAt P.nr (readsAt (lateOf (roomFor P.D B sG)) Sum.inl))
      (eAt P.toOwnPar P.wPart e (zt e))
      (namesT P.tp (readsT (lateOf (roomFor P.D B sG)) fun x => Sum.inr (Sum.inl x)))
      (termsEAt P.tp ((tailF P).b3 e).2)
      (gNamesAt P.fp (gReadsAt (lateOf (roomFor P.D B sG)) fun x => Sum.inr (Sum.inr x)))
      (gatedEAt P.fp ((tailF P).b5 e).2 ((tailF P).b6 e).2) b B sG
      (yL P (lateOf (roomFor P.D B sG)) (fmOf P zt b sG sG) e m))
    {g : ℕ} {rows : Bool} {F0 G : Fork} {fs : Array OnBytes.Model.Aff}
    (h : Desc.First.K4.formsFrontWith rows Pp g o F0 = some (fs, G))
    (hz : ∀ f ∈ fs.toList, f.value X.ρ W1 = 0) (hS : ∀ f ∈ X.sideClaims, f.value X.ρ W2 = 0)
    (T : StackTies P.ip ((tailF P).b4 e).2.st X.ρ X.p.v.y X.p.shownT X.om
      (zOf X.ρ X.H.fo.zx X.H.fo.zy) (pt X.ρ X.c.rt))
    (hk : X.lam = kS P.D)
    (hpt : ∀ j, j < kS P.D → Blocks.nat (P.ip.inn.Kp.outPt P.ip.inn.Mk ((tailF P).b4 e).2) j =
      X.ρ.val (X.c.rs.getD (kS P.D - 1 - j) zeroE))
    (hA : W2.slot X.sA0 = ((tailF P).b4 e).2.vals (.inl (.inl ())) -
      P.ip.inn.Kp.outB P.ip.inn.Mk ((tailF P).b4 e).2 * P.msg m (P.ip.cI (.inl (.inl ()))))
    (hBs : W2.slot X.sB0 = ((tailF P).b4 e).2.vals (.inr (.inl ())) -
      P.ip.inn.Kp.outB P.ip.inn.Mk ((tailF P).b4 e).2 * P.msg m (P.ip.cI (.inr (.inl ()))))
    (u1 : Blocks.Form.val (yL P (lateOf (roomFor P.D B sG)) (fmOf P zt b sG sG) e m)
      (u1At P.nr ((tailF P).b1 e).2) = 0)
    (u2 : Blocks.Form.val (yL P (lateOf (roomFor P.D B sG)) (fmOf P zt b sG sG) e m)
      (u2At P.nr ((tailF P).b2 e).2) = 0)
    (u5 : Blocks.Form.val (yL P (lateOf (roomFor P.D B sG)) (fmOf P zt b sG sG) e m)
      (prodU P.fp.gp ((tailF P).b5 e).2) = 0)
    (u6 : Blocks.Form.val (yL P (lateOf (roomFor P.D B sG)) (fmOf P zt b sG sG) e m)
      (prodU P.fp.rt.L ((tailF P).b6 e).2) = 0)
    (u4 : Blocks.Form.val (yL P (lateOf (roomFor P.D B sG)) (fmOf P zt b sG sG) e m)
      (upForm (J₂ := J3 (roomFor P.D B sG)) (Cb.Sub.formU P.ip.inn.toSum.T.par
        (fun _ b _ _ => PEmpty.elim b) ((tailF P).b4 e).2)) = 0) :
    Ledger.Holds (clF P (lateOf (roomFor P.D B sG)) Sum.inl (fun x => Sum.inr (Sum.inl x))
        (fun x => Sum.inr (Sum.inr x)) R sG zt b B e).sq
        (yL P (lateOf (roomFor P.D B sG)) (fmOf P zt b sG sG) e m) ∧
      Ledger.Holds (clF P (lateOf (roomFor P.D B sG)) Sum.inl (fun x => Sum.inr (Sum.inl x))
        (fun x => Sum.inr (Sum.inr x)) R sG zt b B e).bat
        (yL P (lateOf (roomFor P.D B sG)) (fmOf P zt b sG sG) e m) ∧
      Ledger.Holds (clF P (lateOf (roomFor P.D B sG)) Sum.inl (fun x => Sum.inr (Sum.inl x))
        (fun x => Sum.inr (Sum.inr x)) R sG zt b B e).led
        (yL P (lateOf (roomFor P.D B sG)) (fmOf P zt b sG sG) e m) ∧
      Ledger.Holds (clF P (lateOf (roomFor P.D B sG)) Sum.inl (fun x => Sum.inr (Sum.inl x))
        (fun x => Sum.inr (Sum.inr x)) R sG zt b B e).terms
        (yL P (lateOf (roomFor P.D B sG)) (fmOf P zt b sG sG) e m) ∧
      Ledger.Holds (clF P (lateOf (roomFor P.D B sG)) Sum.inl (fun x => Sum.inr (Sum.inl x))
        (fun x => Sum.inr (Sum.inr x)) R sG zt b B e).gated
        (yL P (lateOf (roomFor P.D B sG)) (fmOf P zt b sG sG) e m) ∧
      Ledger.Holds (clF P (lateOf (roomFor P.D B sG)) Sum.inl (fun x => Sum.inr (Sum.inl x))
        (fun x => Sum.inr (Sum.inr x)) R sG zt b B e).hot
        (yL P (lateOf (roomFor P.D B sG)) (fmOf P zt b sG sG) e m) ∧
      Ledger.Holds (clF P (lateOf (roomFor P.D B sG)) Sum.inl (fun x => Sum.inr (Sum.inl x))
        (fun x => Sum.inr (Sum.inr x)) R sG zt b B e).stack
        (yL P (lateOf (roomFor P.D B sG)) (fmOf P zt b sG sG) e m) :=
  have Dc := frontDict_at X W1 Mm hR1 hscl hv h2 h2X hyv hls hD Z hB h0 hcells
    (late_norms P (normsOk_of P zt b sG B sG nl nd nB) e m)
    (late_terms P (termsOk_of P zt b sG B sG) e m)
    (late_gated P (gatedOk_of P zt b sG B sG g1 gs1 gs2 gfe) e m) hPt Sl h
  have hp3 : o.v.y.h.p3 = true := Dc.hot.p3
  have rr := stack_port_pub34 X W2 Mm hR2 hS hscl P.ip P.hrd hD htb hL0 ((tailF P).b4 e).2
    (lateAt P (lateOf (roomFor P.D B sG)) (fmOf P zt b sG sG) e m) hcells T hk hpt hA hBs
  parts_of_claims P (lateOf (roomFor P.D B sG)) Sum.inl (fun x => Sum.inr (Sum.inl x))
    (fun x => Sum.inr (Sum.inr x)) R sG zt b B e _ Dc hp3 h2 h hz u1 u2 u5 u6 u4 rr.1 rr.2

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.seven_parts
