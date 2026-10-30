-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/HeadLinkPort.lean: the output head's link, from five routines of the verifier that
succeed and from what the protocol's random steps are meant to give.

Johnson/Road/HeadLinkRun.lean still has three records among its hypotheses: what was heard has
passed hear's tests, the point P_V has lt coordinates, and the reads are true of the cells. Here
they are conclusions:
  the first two of "the routine hear succeeds in a run on a view" (Johnson/Road/HeadView.lean);
  the third of "planH2 and tablesOf succeed, and every record of the list of tables holds what it
    says of its matrix" (Johnson/Road/HeadReads.lean).

Main theorems: head_link_rf_of_port, head_link_of_port.

What its hypotheses are, sorted.
  The verifier's own words: layout (at the array tauFCw of Johnson/Road/HeadTabs.lean; by
    tauFC_of_layout there it is the array of a layers' layout that Layer.layout returns), planH2,
    hear (on a view), tablesOf and walk return, each from a state and a context of its own; the
    run's plan has the list of matrices of planH2's plan; the record tl0 of the smallness test has
    that list.
  Public numbers: FullH (nine numbers of the shape), sh = 8, F = 24, sT = 4; BorderH (the stream's
    matrix); the final normalisation's numbers are lawful.
  The request: ReqFits at the library's term for the instance x (Johnson/Road/HeadLaid.lean
    concludes it from the verifier's stFromCall and coveredOf and from three ties that it names);
    r = 1,023, e = 1,024.
  States: the walk begins with one coefficient for each slot; hT.
  What random steps are meant to give: Holds and small (the smallness test); ClaimsHold (the
    batching of the claims); SlotsHold, hW, hP (four sumchecks); StepPoint; StepLookupAt.
  The layers: LayersGive.
None of the last two groups is derived from a verifier's acceptance here. The program
does not import this file.
-/
import Johnson.Road.HeadLinkRun
import Johnson.Road.HeadView

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Inst.Model Inst.Model.Head
open OnBytes.Model (Reading World Aff Fork SubM)

/-- The same as head_link_of_port below, as far as the field relation of the library's plain head
over the challenge field. -/
theorem head_link_rf_of_port {R : Model.Head.Run} {tl tl' tl0 : Model.HTailF2}
    {wo : Model.WsForkOut} {Lc Lc' : Model.LinkCtx} {F G F0 F1 F2 G2 : Fork}
    {C D C0 C1 C2 D2 : Ctx} {W : World Cb.Gl.E} {plain : Array E}
    {g : Model.Settings} {O : Model.Head.Owner} {NGr lkW : ℕ} {H0 : Model.Head.HPlanH2}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hFull : FullH R.h) (hsh : R.h.digSh = 8)
    (hF : R.h.famF = 24) (hTs : R.h.tabS = 4) (Bd : BorderH R.b)
    (hpl : Model.Head.planH2 g R.h R.L R.b O NGr lkW = .ok H0)
    (hm0 : R.hp.tl.mats = H0.tl.mats) (hN0 : R.hp.tl.NM = H0.tl.NM)
    (hd : C0.ch.dry = false) (hx : Ok (Model.Head.hear R.h R.L R.hp R.cov plain) F0 C0 R.x F1 C1)
    (ht : Ok (Model.Head.tablesOf R.h R.L R.hp R.cov R.x) F2 C2 R.t G2 D2)
    (hs : F.LS.size = F.ns) (hT : Walk.Keeps (tl.objectsF R.t.funs))
    (hwalk : Walk.OkL (Model.Head.walk R tl wo) Lc F C tl' Lc' G D)
    (i : Index ppref) (x : Instance ppref) (hr : x.r = 1023)
    (Y : ReqFits R HeadSizes.ref (Cm.reqOf x)) {Mz : Mats ℤ}
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
    Cm.Plain.TP.RF (F := Cb.Gl.E) (npOf R.h) (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E))
      (Cm.reqOf x) (cellsH R.h R.L R.b Mz) :=
  head_link_rf_of_walk hy hFull.lt hFull.d hFull.V hsh hFull.XL hF hTs
    (View.heardFits_of_view hd hx) (View.PV_size hd hx) hs hT hwalk i x hr Y
    (trueH_of_holds hpl hm0 hN0 hFull (numH_of_layout hFull hy) Bd ht hm hNM holds)
    small Kf claims S hW hP stepP stepL

/-- **The head's link, from five routines that succeed.** See the head of this file. -/
theorem head_link_of_port {R : Model.Head.Run} {tl tl' tl0 : Model.HTailF2}
    {wo : Model.WsForkOut} {Lc Lc' : Model.LinkCtx} {F G F0 F1 F2 G2 : Fork}
    {C D C0 C1 C2 D2 : Ctx} {W : World Cb.Gl.E} {plain : Array E}
    {g : Model.Settings} {O : Model.Head.Owner} {NGr lkW : ℕ} {H0 : Model.Head.HPlanH2}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hFull : FullH R.h) (hsh : R.h.digSh = 8)
    (hF : R.h.famF = 24) (hTs : R.h.tabS = 4) (Bd : BorderH R.b)
    (hpl : Model.Head.planH2 g R.h R.L R.b O NGr lkW = .ok H0)
    (hm0 : R.hp.tl.mats = H0.tl.mats) (hN0 : R.hp.tl.NM = H0.tl.NM)
    (hd : C0.ch.dry = false) (hx : Ok (Model.Head.hear R.h R.L R.hp R.cov plain) F0 C0 R.x F1 C1)
    (ht : Ok (Model.Head.tablesOf R.h R.L R.hp R.cov R.x) F2 C2 R.t G2 D2)
    (hs : F.LS.size = F.ns) (hT : Walk.Keeps (tl.objectsF R.t.funs))
    (hwalk : Walk.OkL (Model.Head.walk R tl wo) Lc F C tl' Lc' G D)
    {κ : ℕ → LayerScale} {tbs : ℕ → Tables} (hn : (npOf R.h).OK)
    (i : Index ppref) (x : Instance ppref) (hr : x.r = 1023) (he : x.e = 1024)
    (Y : ReqFits R HeadSizes.ref (Cm.reqOf x)) {Mz : Mats ℤ}
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
    (stepL : StepLookupAt W R F fn fun q => pt Reading.gl (R.x.g1.zk.getD q #[]))
    (hl : Top.LayersGive κ tbs i.val x.prompt (cellsH R.h R.L R.b Mz)) (pol : AcceptancePolicy) :
    RinfR ppref κ (npOf R.h) tbs pol i x :=
  reply_of_rf hn i x hr he
    (head_link_rf_of_port hy hFull hsh hF hTs Bd hpl hm0 hN0 hd hx ht hs hT hwalk i x hr Y hm hNM
      holds small Kf claims S hW hP stepP stepL) hl pol

#print axioms head_link_rf_of_port
#print axioms head_link_of_port

end OnBytes.Road.Hd
