-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/SevenPartsFirst.lean: THE FIRST GROUP's twin of Johnson/Road/K4/SevenParts.lean:
eight parts of the library's ledger of the first group's layers' sub-proof hold at the late entries'
forms' values, where the claims of K4's two runs are worth 0 on true reads.

  `yLF`: the entries: the messages, and each late entry at its form's value, at the names, late
    entries and forms of Johnson/Road/K4/LateNamesFirst.lean.
  `late_normsF`, `late_termsF`, `late_gatedF`: the three families of tables are true at yLF.
  `eight_parts_first`: the parts sq, bat, led, terms, gated, hot, stack and emb of clFirst
    (Cb/Pv/Lay/End/LayFirst.lean) hold of yLF.
It calls: parts_of_claims_first (PartsFirst.lean) · frontDict_at (FrontDictAtPub.lean) ·
normsOkF_of, termsOkF_of, gatedOkF_of (LateNamesFirst.lean) · stack_port_pub34 (StackAtPub.lean):
the two ports are general in the names and the records, and serve here as they stand.
What is asked, and by nothing here shown: all that seven_parts asks, at the first group's letters
(the chain's last statements (tailW P).s7.Nx; the norms' record eAtF), and one premise more: the
embedding's claim is worth 0 at yLF.
Limits. All of these are premises. The parts merge, look and planes are not spoken of. With routed
experts and a second product layer alone. Implications in given worlds: no draw, nothing on
soundness or on hiding.


-/
import Johnson.Road.K4.PartsFirst
import Johnson.Road.K4.FrontDictAtPub
import Johnson.Road.K4.LateNamesFirst
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

variable {K : Type} [Field K] [Fintype K] [scl : Scl] {M X0 : Type} (P : FullFPar K M X0)
  (zt : (tailW P).s7.Nx → ℕ → K) (b B sG : ℕ)

/-- The late entries, each at its form's value. -/
noncomputable abbrev lateLF (e : (tailW P).s7.Nx) (m : M) : J4 (roomF P.D B sG P.nb) → K :=
  fun i => (lateA (lateF (roomF P.D B sG P.nb)) (fmOfF P zt b sG sG e) i).val (P.msg m)

/-- The entries: the early ones of the messages m, each late one at its form's value. -/
noncomputable abbrev yLF (e : (tailW P).s7.Nx) (m : M) : P.J ⊕ J4 (roomF P.D B sG P.nb) → K :=
  Sum.elim (P.msg m) (lateLF P zt b B sG e m)

/-- The norms' tables are true at yLF. -/
theorem late_normsF (nl : lDd P.D = b + sG) (nd : P.D.d = B * 2 ^ sG) (nB : B ≤ 2 ^ b)
    (e : (tailW P).s7.Nx) (m : M) :
    TablesTrue (namesAt P.ofp.nr (readsAt (lateF (roomF P.D B sG P.nb)) fun x => Sum.inl (Sum.inl
        x)))
      (eAtF P.ofp P.wfPart e (zt e)) P.D (P.rd (P.msg m)) (P.D.lL + 1) b sG B
      (yLF P zt b B sG e m) :=
  have O := normsOkF_of P zt b sG B sG nl nd nB
  tables_true P.ofp.nr P.hrd (lateF (roomF P.D B sG P.nb)) (fun x => Sum.inl (Sum.inl x)) (fmOfF P
      zt b sG sG e) _
    (P.D.lL + 1) b sG B (O.hfm e) O.gXi O.gP O.gR O.gS (P.msg m)

/-- The terms' tables are true at yLF. -/
theorem late_termsF (e : (tailW P).s7.Nx) (m : M) :
    TermsTrue (namesT P.tp (readsT (lateF (roomF P.D B sG P.nb)) fun x => Sum.inl (Sum.inr (Sum.inl
        x))))
      (termsEAt P.tp ((tailW P).b3 e).2) P.D (P.rd (P.msg m)) (yLF P zt b B sG e m) :=
  have O := termsOkF_of P zt b sG B sG
  terms_true P.tp P.hrd (lateF (roomF P.D B sG P.nb)) (fun x => Sum.inl (Sum.inr (Sum.inl x)))
      (fmOfF P zt b sG sG e) _
    (O.hfm e) O.gR O.gC O.gS (P.msg m)

/-- The gated products' tables are true at yLF. -/
theorem late_gatedF (g1 : 1 ≤ P.D.lL) (gs1 : sG ≤ lF P.D) (gs2 : sG ≤ lFe P.D)
    (gfe : P.D.fe = 2 ^ lFe P.D) (e : (tailW P).s7.Nx) (m : M) :
    GatedTables (gNamesAt P.fp (gReadsAt (lateF (roomF P.D B sG P.nb)) fun x => Sum.inl (Sum.inr
        (Sum.inr x))))
      (gatedEAt P.fp ((tailW P).b5 e).2 ((tailW P).b6 e).2) P.D (P.rd (P.msg m)) sG
      (yLF P zt b B sG e m) :=
  have O := gatedOkF_of P zt b sG B sG g1 gs1 gs2 gfe
  gated_tables P.fp P.hrd (lateF (roomF P.D B sG P.nb)) (fun x => Sum.inl (Sum.inr (Sum.inr x)))
      (fmOfF P zt b sG sG e) _
    sG (O.hfm e) O.hY (P.msg m)

variable (R : (tailW P).s7.Nx → Rest2 K (P.J ⊕ J4 (roomF P.D B sG P.nb))) (e : (tailW P).s7.Nx)
  (m : M)

/-- **Eight parts of the first group's ledger at the late entries' forms' values.** -/
theorem eight_parts_first (X : Rows.Pub34 K) (W1 W2 : World K) (Mm : Mats K)
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
      PointTies P.D (eAtF P.ofp P.wfPart e (zt e)) (termsEAt P.tp ((tailW P).b3 e).2)
        (gatedEAt P.fp ((tailW P).b5 e).2 ((tailW P).b6 e).2) b sG
        (zpos P.D (zOf X.ρ X.H.fo.zx X.H.fo.zy)) (pt X.ρ X.c.rt) (pt X.ρ X.c.rt) (pt X.ρ ZV)
        (fun j => pt X.ρ ZV (sG + j)) (pt X.ρ X.H.PV) (pt X.ρ X.H.tV.r) (pt X.ρ ZA)
        (fun j => pt X.ρ ZA (sG + j)) (pt X.ρ ZB) (fun j => pt X.ρ ZB (sG + j)))
    (Sl : SlotTies X.ρ W1 Pp o P.D
      (namesAt P.ofp.nr (readsAt (lateF (roomF P.D B sG P.nb)) fun x => Sum.inl (Sum.inl x)))
      (eAtF P.ofp P.wfPart e (zt e))
      (namesT P.tp (readsT (lateF (roomF P.D B sG P.nb)) fun x => Sum.inl (Sum.inr (Sum.inl x))))
      (termsEAt P.tp ((tailW P).b3 e).2)
      (gNamesAt P.fp (gReadsAt (lateF (roomF P.D B sG P.nb)) fun x => Sum.inl (Sum.inr (Sum.inr
          x))))
      (gatedEAt P.fp ((tailW P).b5 e).2 ((tailW P).b6 e).2) b B sG
      (yLF P zt b B sG e m))
    {g : ℕ} {rows : Bool} {F0 G : Fork} {fs : Array OnBytes.Model.Aff}
    (h : Desc.First.K4.formsFrontWith rows Pp g o F0 = some (fs, G))
    (hz : ∀ f ∈ fs.toList, f.value X.ρ W1 = 0) (hS : ∀ f ∈ X.sideClaims, f.value X.ρ W2 = 0)
    (T : StackTies P.ip ((tailW P).b4 e).2.st X.ρ X.p.v.y X.p.shownT X.om
      (zOf X.ρ X.H.fo.zx X.H.fo.zy) (pt X.ρ X.c.rt))
    (hk : X.lam = kS P.D)
    (hpt : ∀ j, j < kS P.D → Blocks.nat (P.ip.inn.Kp.outPt P.ip.inn.Mk ((tailW P).b4 e).2) j =
      X.ρ.val (X.c.rs.getD (kS P.D - 1 - j) zeroE))
    (hA : W2.slot X.sA0 = ((tailW P).b4 e).2.vals (.inl (.inl ())) -
      P.ip.inn.Kp.outB P.ip.inn.Mk ((tailW P).b4 e).2 * P.msg m (P.ip.cI (.inl (.inl ()))))
    (hBs : W2.slot X.sB0 = ((tailW P).b4 e).2.vals (.inr (.inl ())) -
      P.ip.inn.Kp.outB P.ip.inn.Mk ((tailW P).b4 e).2 * P.msg m (P.ip.cI (.inr (.inl ()))))
    (u1 : Blocks.Form.val (yLF P zt b B sG e m)
      (u1At P.ofp.nr ((tailW P).b1 e).2) = 0)
    (u2 : Blocks.Form.val (yLF P zt b B sG e m)
      (u2At P.ofp.nr ((tailW P).b2 e).2) = 0)
    (u5 : Blocks.Form.val (yLF P zt b B sG e m)
      (prodU P.fp.gp ((tailW P).b5 e).2) = 0)
    (u6 : Blocks.Form.val (yLF P zt b B sG e m)
      (prodU P.fp.rt.L ((tailW P).b6 e).2) = 0)
    (u4 : Blocks.Form.val (yLF P zt b B sG e m)
      (upForm (J₂ := J4 (roomF P.D B sG P.nb)) (Cb.Sub.formU P.ip.inn.toSum.T.par
        (fun _ b _ _ => PEmpty.elim b) ((tailW P).b4 e).2)) = 0)
    (uE : Blocks.Form.val (yLF P zt b B sG e m) (embClaim (lateF (roomF P.D B sG P.nb)) Sum.inr
      (((tailW P).y7 e).1.2 (0 : Fin 1)) P.mkE P.nb P.gB (stF P e).pb) = 0) :
    Ledger.Holds (clFirst P (lateF (roomF P.D B sG P.nb)) (fun x => Sum.inl (Sum.inl x))
        (fun x => Sum.inl (Sum.inr (Sum.inl x))) (fun x => Sum.inl (Sum.inr (Sum.inr x))) Sum.inr R
        zt b B sG e).sq (yLF P zt b B sG e m) ∧
      Ledger.Holds (clFirst P (lateF (roomF P.D B sG P.nb)) (fun x => Sum.inl (Sum.inl x))
        (fun x => Sum.inl (Sum.inr (Sum.inl x))) (fun x => Sum.inl (Sum.inr (Sum.inr x))) Sum.inr R
        zt b B sG e).bat (yLF P zt b B sG e m) ∧
      Ledger.Holds (clFirst P (lateF (roomF P.D B sG P.nb)) (fun x => Sum.inl (Sum.inl x))
        (fun x => Sum.inl (Sum.inr (Sum.inl x))) (fun x => Sum.inl (Sum.inr (Sum.inr x))) Sum.inr R
        zt b B sG e).led (yLF P zt b B sG e m) ∧
      Ledger.Holds (clFirst P (lateF (roomF P.D B sG P.nb)) (fun x => Sum.inl (Sum.inl x))
        (fun x => Sum.inl (Sum.inr (Sum.inl x))) (fun x => Sum.inl (Sum.inr (Sum.inr x))) Sum.inr R
        zt b B sG e).terms (yLF P zt b B sG e m) ∧
      Ledger.Holds (clFirst P (lateF (roomF P.D B sG P.nb)) (fun x => Sum.inl (Sum.inl x))
        (fun x => Sum.inl (Sum.inr (Sum.inl x))) (fun x => Sum.inl (Sum.inr (Sum.inr x))) Sum.inr R
        zt b B sG e).gated (yLF P zt b B sG e m) ∧
      Ledger.Holds (clFirst P (lateF (roomF P.D B sG P.nb)) (fun x => Sum.inl (Sum.inl x))
        (fun x => Sum.inl (Sum.inr (Sum.inl x))) (fun x => Sum.inl (Sum.inr (Sum.inr x))) Sum.inr R
        zt b B sG e).hot (yLF P zt b B sG e m) ∧
      Ledger.Holds (clFirst P (lateF (roomF P.D B sG P.nb)) (fun x => Sum.inl (Sum.inl x))
        (fun x => Sum.inl (Sum.inr (Sum.inl x))) (fun x => Sum.inl (Sum.inr (Sum.inr x))) Sum.inr R
        zt b B sG e).stack (yLF P zt b B sG e m) ∧
      Ledger.Holds (clFirst P (lateF (roomF P.D B sG P.nb)) (fun x => Sum.inl (Sum.inl x))
        (fun x => Sum.inl (Sum.inr (Sum.inl x))) (fun x => Sum.inl (Sum.inr (Sum.inr x))) Sum.inr R
        zt b B sG e).emb (yLF P zt b B sG e m) :=
  have Dc := frontDict_at X W1 Mm hR1 hscl hv h2 h2X hyv hls hD Z hB h0 hcells
    (late_normsF P zt b B sG nl nd nB e m) (late_termsF P zt b B sG e m)
    (late_gatedF P zt b B sG g1 gs1 gs2 gfe e m) hPt Sl h
  have hp3 : o.v.y.h.p3 = true := Dc.hot.p3
  have rr := stack_port_pub34 X W2 Mm hR2 hS hscl P.ip P.hrd hD htb hL0 ((tailW P).b4 e).2
    (lateLF P zt b B sG e m) hcells T hk hpt hA hBs
  parts_of_claims_first P (lateF (roomF P.D B sG P.nb)) (fun x => Sum.inl (Sum.inl x))
    (fun x => Sum.inl (Sum.inr (Sum.inl x))) (fun x => Sum.inl (Sum.inr (Sum.inr x))) Sum.inr R zt
    b B sG e _ Dc hp3 h2 h hz u1 u2 u5 u6 u4 rr.1 rr.2 uE

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.eight_parts_first
