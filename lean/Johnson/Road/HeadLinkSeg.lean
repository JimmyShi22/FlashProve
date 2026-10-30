-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/HeadLinkSeg.lean: the output head's link lands on the library's own segment of the
head.

Johnson/Road/HeadLinkPort.lean goes from routines of the verifier that succeed, and from what the
protocol's random steps are meant to give, to the field relation of the library's plain head at the
cells read in the verifier's matrices. The library's theorems on the target protocol do not speak of
cells: they speak of 25 matrices, one for each segment of a partition, and of conditions on them
(Cm/TargetSegModelOf.lean: segOf; its segment 24 is segHeadY of Cm/TargetSegHeadY.lean: the plain
head's segment segHead with one identity more, on the reply of a request with e < 1,024). This file
carries the relation there: the matrices of the verifier's lists, stacked as
Johnson/Road/HeadPlace.lean says (stackedH), meet the conditions of segHeadY at the final
normalisation's numbers npOf R.h. It is here that the places of the cells in the library's matrices
are used (readsAt_cellsH, through Johnson/Road/HeadSeg.lean).

Main theorem: head_link_seg.

What is not claimed. As in Johnson/Road/HeadLinkPort.lean. Besides: LentH, that the matrix which the
head borrows has the entries of the lender's matrix, is a hypothesis. The index matrix is the digit
matrix that the library makes of the index i (Cm.Idx.ofIndex); nothing ties it to a commitment. The
library's partition has the numbers s.nf of a table of scales s where this theorem has npOf R.h:
that the two are one is a public fact that is not stated here. While Mg is a free letter LentH is no
burden: it binds only when the layers' link speaks of the same Mg. Nothing is said about the other
24 segments. The program does not import this file.
-/
import Johnson.Road.HeadLinkPort
import Johnson.Road.HeadSeg
import Cm.TargetSegHeadY

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Inst.Model Inst.Model.Head
open OnBytes.Model (Reading World Aff Fork SubM)

/-- **The head's link lands on the library's last segment.** Under the hypotheses of
head_link_rf_of_port, with e = 1,024 and the stream's record taken from a layers' layout of the
library's sizes, the conditions of the last segment of the library's partition (segHeadY, at the
numbers npOf R.h) hold, for the digit matrix of the
index i, at the matrices stacked from the verifier's: Mz for the head, Mg g for the feed-forward
group g, Ma for the attention segments. -/
theorem head_link_seg {R : Model.Head.Run} {tl tl' tl0 : Model.HTailF2}
    {wo : Model.WsForkOut} {Lc Lc' : Model.LinkCtx} {F G F0 F1 F2 G2 : Fork}
    {C D C0 C1 C2 D2 : Ctx} {W : World Cb.Gl.E} {plain : Array E}
    {g : Model.Settings} {O : Model.Head.Owner} {NGr lkW : ℕ} {H0 : Model.Head.HPlanH2}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hFull : FullH R.h) (hsh : R.h.digSh = 8)
    (hF : R.h.famF = 24) (hTs : R.h.tabS = 4)
    {hyL : Model.Layer.Shape} {pc : List (List String)} {y : Model.Layer.Lay}
    (hlay : Model.Layer.layout hyL pc = .ok y) (Sw : Switches hyL) (Z : Sized hyL All.DF)
    (Z2 : Sized2 hyL All.DF) (hb : R.b = Model.Verify.borderOf y)
    (Mg : ℕ → Mats ℤ) (Ma : ℕ → ℕ → ℕ → ℤ)
    (hpl : Model.Head.planH2 g R.h R.L R.b O NGr lkW = .ok H0)
    (hm0 : R.hp.tl.mats = H0.tl.mats) (hN0 : R.hp.tl.NM = H0.tl.NM)
    (hd : C0.ch.dry = false) (hx : Ok (Model.Head.hear R.h R.L R.hp R.cov plain) F0 C0 R.x F1 C1)
    (ht : Ok (Model.Head.tablesOf R.h R.L R.hp R.cov R.x) F2 C2 R.t G2 D2)
    (hs : F.LS.size = F.ns) (hT : Walk.Keeps (tl.objectsF R.t.funs))
    (hwalk : Walk.OkL (Model.Head.walk R tl wo) Lc F C tl' Lc' G D)
    (i : Index ppref) (x : Instance ppref) (hr : x.r = 1023) (he : x.e = 1024)
    (Y : ReqFits R HeadSizes.ref (Cm.reqOf x)) {Mz : Mats ℤ} (hlent : LentH R.h y Mz (Mg 11))
    (hm : tl0.mats = R.hp.tl.mats) (hNM : tl0.NM = R.hp.tl.NM)
    (holds : ∀ Fn ∈ R.t.funs, Holds Reading.gl W tl0 R.iU3 (colsOf F R.iU3)
      (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)) Fn)
    (small : ∀ a r c, |Mz a r c| < 2 ^ 18) {fn : ℕ → ℕ → ℕ → Cb.Gl.E}
    (Kf : ∀ q w, (R.L.calls.getD q default).segs.foldlM
        (fun w g => Model.Head.markColumns R w g)
        (Array.replicate (R.L.calls.getD q default).J 0) = some w →
      KeyFn (R.L.calls.getD q default).segs w (R.L.calls.getD q default).J
      (kvOf (Reading.gl.val (invE (Model.Head.pw (R.h.digSh + 15)))) HeadSizes.ref (npOf R.h)
        (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
        (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Cm.reqOf x))
      (Reading.gl.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0))) (fn q))
    (claims : ClaimsHold W R F)
    (S : SlotsHold Reading.gl W R (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
      (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Cm.reqOf x)
      (fun j => pt Reading.gl R.x.Zl (R.h.ls + j)))
    (hW : ∀ s, s < 9 → W.slot (R.x.sW + s) = Blocks.ext R.h.lt (fun a => Ledger.Wsum nD
      (fun l j => bl (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)) l j a) s)
      (pt Reading.gl R.x.PV))
    (hP : ∀ j, j < 7 → W.slot (R.x.sPv + j) = Blocks.ext R.h.lt (fun a => Ledger.prods
      (fun n => Dv (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)) n a) j)
      (pt Reading.gl R.x.PV))
    (stepP : StepPoint (npOf R.h) (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
      R.h.lt (pt Reading.gl R.x.PV))
    (stepL : StepLookupAt W R F fn fun q => pt Reading.gl (R.x.g1.zk.getD q #[])) :
    (Cm.Seg.TS.segHeadY (npOf R.h)).Holds Cm.Seg.TS.fmtRef x
      (fun r c => (((Cm.Idx.ofIndex i).mat r c : ℤ) : Cb.Gl.F))
      (Cb.Partition.castM (E := Cb.Gl.E) (stackedH y Mg Ma Mz)) := by
  have Bd : BorderH R.b := by
    rw [hb]
    exact borderH_of_layout hlay Sw Z Z2
  have rf := head_link_rf_of_port hy hFull hsh hF hTs Bd hpl hm0 hN0 hd hx ht hs hT hwalk i x hr Y
    hm hNM holds small Kf claims S hW hP stepP stepL
  rw [hb] at rf
  exact (Cm.Seg.TS.headY_holds (npOf R.h) _ x _ _).2
    ⟨seg_of_rf_index hFull hy hlay Sw Z Z2 Mg Ma Mz hlent i rf,
      fun hlt => absurd hlt (by rw [he]; decide)⟩

#print axioms head_link_seg

end OnBytes.Road.Hd
