-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadLinkLPort.lean: the output head's link for every request with the shape's policy,
from routines of the verifier that succeed and from what the protocol's random steps are meant to
give.

Johnson/Road/HeadLinkL.lean has the link on the library's head with the cost ledger, under records
of hypotheses. Here the records are conclusions, in the manner of Johnson/Road/HeadLinkRun.lean and
Johnson/Road/HeadLinkPort.lean for the plain head:
  the states and the forms of the claims come from "the routine walk succeeds";
  the record on what was heard and the length of the point P_V from "hear succeeds in a run on a
    view" (Johnson/Road/HeadView.lean);
  the true tables from "planH2 and tablesOf succeed, and every record of the list of tables holds
    what it says of its matrix" (Johnson/Road/HeadReads.lean, HeadMet.lean, HeadFit.lean);
  the request's record, its form and its number of counted positions from the verifier's stFromCall
    and coveredOf and from "the plain scalar that hear was handed is the caller's reply"
    (Johnson/Road/HeadLaid.lean, HeadPub.lean, HeadReply.lean, HeadSumL.lean);
  F = 24, the lawful normalisation and the lawful policy from the layout's own tests
    (Johnson/Road/HeadPub.lean); that the smallness test's routine keeps the state from
    Johnson/Road/HeadTailKeeps.lean.
The policy is the shape's: clip, theta and cap of the parameter file (polOf).

Main definitions: polOf.
Main theorems: ClaimsPolicy.kept; head_linkL_rf_of_walk, head_linkL_of_walk; request_fits;
head_linkL_of_port.

What its hypotheses are, sorted (head_linkL_of_port).
  The verifier's own words: layout, planH2, hear (on a view), tablesOf, walk, stFromCall and
    coveredOf return; the run's plan has the list of matrices of planH2's plan; the record tl0 of
    the smallness test has that list; the plain scalar is the caller's reply.
  Public numbers: FullH (nine numbers of the shape), sh = 8, sT = 4, clip below 2^40, eps below
    2^48; BorderH (the stream's matrix).
  The instance: it has the r, e, tokens and reply of the request's files.
  A state: the walk begins with one coefficient for each slot.
  What random steps are meant to give: Holds and small (the smallness test); ClaimsHold and
    ClaimsPolicy (the batching of the claims); SlotsHold, hW, hP (four sumchecks); StepPoint,
    StepCost; StepLookupAt.
  The layers: LayersGive.
None of the last two groups is derived from a verifier's acceptance here. That these
hypotheses can be met together is not shown here. The program does not import this file.
-/
import Johnson.Road.HeadLinkL
import Johnson.Road.HeadLinkRun
import Johnson.Road.HeadReply
import Johnson.Road.HeadTailKeeps

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Inst.Model Inst.Model.Head
open OnBytes.Model (Reading World Aff Fork SubM)

/-- The policy of a shape, as the library's record. -/
def polOf (h : Model.Head.Shape) : AcceptancePolicy := ⟨h.clipC, h.theta, h.cap⟩

/-- The four claims on the costs, named from a later state that has kept the numbers of columns. -/
theorem ClaimsPolicy.kept {K : Type} [Field K] {ρ : Reading K} {W : World K}
    {R : Model.Head.Run} {F F' : Fork} (c : ClaimsPolicy ρ W R F) (k : Walk.Kept F F') :
    ClaimsPolicy ρ W R F' :=
  ⟨fun G C a k' P => c.1 G C a (k.trans k') P, fun G C a k' P => c.2.1 G C a (k.trans k') P,
    fun G C a k' P => c.2.2.1 G C a (k.trans k') P,
    fun G C a k' P => c.2.2.2 G C a (k.trans k') P⟩

/-- The same as head_linkL_of_walk below, as far as the field relation of the library's head with
the cost ledger over the challenge field. -/
theorem head_linkL_rf_of_walk {R : Model.Head.Run} {tl tl' : Model.HTailF2}
    {wo : Model.WsForkOut} {Lc Lc' : Model.LinkCtx} {F G : Fork} {C D : Ctx} {W : World Cb.Gl.E}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (h1 : R.h.lt = 10) (h2 : R.h.d = 5120)
    (h3 : R.h.V = 202048) (hsh : R.h.digSh = 8) (hXL : R.h.XL = 5) (hTs : R.h.tabS = 4)
    (Xh : HeardFits R.h R.L R.cov R.x) (hPs : R.x.PV.size = R.h.lt) (hs : F.LS.size = F.ns)
    (hwalk : Walk.OkL (Model.Head.walk R tl wo) Lc F C tl' Lc' G D)
    (i : Index ppref) (x : Instance ppref)
    (Y : ReqFits R HeadSizes.ref (Req.of (polOf R.h) x))
    (hNB : (Req.of (polOf R.h) x).NB = R.cov.hRC) {Mz : Mats ℤ}
    (T : TrueH Reading.gl W R (colsOf F R.iU3)
      (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)))
    (small : ∀ a r c, |Mz a r c| < 2 ^ 18) {fn : ℕ → ℕ → ℕ → Cb.Gl.E}
    (Kf : ∀ q w, (R.L.calls.getD q default).segs.foldlM
        (fun w g => Model.Head.markColumns R w g)
        (Array.replicate (R.L.calls.getD q default).J 0) = some w →
      KeyFn (R.L.calls.getD q default).segs w (R.L.calls.getD q default).J
      (kvOf (Reading.gl.val (invE (Model.Head.pw (R.h.digSh + 15)))) HeadSizes.ref (npOf R.h)
        (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
        (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Req.of (polOf R.h) x))
      (Reading.gl.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0))) (fn q))
    (claims : ClaimsHold W R F) (claimP : ClaimsPolicy Reading.gl W R F)
    (S : SlotsHold Reading.gl W R (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
      (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Req.of (polOf R.h) x)
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
    (stepC : StepCost (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
      (Req.of (polOf R.h) x) R.h.lt (fun j => pt Reading.gl R.x.Zl (R.h.ls + j))) :
    Policy.LedgerHead.RF (F := Cb.Gl.E) (npOf R.h) (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E))
      (Req.of (polOf R.h) x) (cellsH R.h R.L R.b Mz) := by
  choose w hw using marks_of_layout (R := R) hy
  have Sf : SegsFit R := segsFit_of_layout hy h1 h2 h3 hXL
  have A := callsLaid_of_layout hy
  obtain ⟨F1, F2, F3, F4, F5, F6, F8, F9, c1, c2, c3, c4, c5, c8, _, ⟨k2, a2, _⟩, _,
    ⟨k4, a4, _⟩, ⟨k5, a5, _⟩, _⟩ :=
    Walk.walk_states hXL hs (Parts.objectsF_keeps tl R.t.funs) hwalk
  obtain ⟨_, _, q5, _, hq5, _⟩ := ok_claimLedger hXL k2.1 a2
  rw [k2.2 R.iU3] at hq5
  obtain ⟨_, KF, hKF, _⟩ := claimJoin_form
    (fun q laid y G' D' hk => Walk.leaves_keyForm R q laid F4 c4 y G' D' hk) a4
  have X := linesFit_of_run hy Xh Reading.gl (R := R) rfl rfl rfl h1 h2 h3 hsh hXL Y
    (Req.of_ok (polOf R.h) x) T
  obtain ⟨hRho, hZ⟩ := costTables_of_run hy Xh Reading.gl (R := R) rfl rfl rfl X.laid Y T
  have hPV := shortAt_of_sum hPs T.hrPV
  obtain ⟨Fq, cq, _, _, kq, aq⟩ := walk_planes hXL hs hwalk
  obtain ⟨A', hA'⟩ := planesOf_of_claim aq
  rw [← k4.2 R.iU3] at X hPV hq5 hRho hZ
  exact head_linkL_rf hy h1 (famF_of_layout hy) hTs Sf (polOf R.h) i x X hPV small
    (callsAt_of_run Reading.gl hy Xh A) hw (fun q => Kf q (w q) (hw q)) hKF hq5
    (claims.2.1 F4 c4 KF k4 hKF)
    (fun k hk => claims.1 q5 (by rw [← k4.2 R.iU3]; exact hq5) k hk) S hW hP stepP
    ⟨claims.2.2.1, claims.2.2.2 Fq cq A' kq hA'⟩ (stepL Fq cq A' kq hA')
    ⟨k5.1, fun t => (k5.2 t).trans (k4.2 t).symm⟩ hNB rfl rfl rfl hRho hZ a5 (claimP.kept k4)
    stepC

/-- **The head's link for a request with the shape's policy, from the routine walk.** See the heads
of this file and of Johnson/Road/HeadLinkL.lean for what is a hypothesis. -/
theorem head_linkL_of_walk {R : Model.Head.Run} {tl tl' : Model.HTailF2}
    {wo : Model.WsForkOut} {Lc Lc' : Model.LinkCtx} {F G : Fork} {C D : Ctx} {W : World Cb.Gl.E}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (h1 : R.h.lt = 10) (h2 : R.h.d = 5120)
    (h3 : R.h.V = 202048) (hsh : R.h.digSh = 8) (hXL : R.h.XL = 5) (hTs : R.h.tabS = 4)
    (hC : R.h.clipC < 2 ^ 40) (heps : R.h.epsF < 2 ^ 48)
    (Xh : HeardFits R.h R.L R.cov R.x) (hPs : R.x.PV.size = R.h.lt) (hs : F.LS.size = F.ns)
    (hwalk : Walk.OkL (Model.Head.walk R tl wo) Lc F C tl' Lc' G D)
    {κ : ℕ → LayerScale} {tbs : ℕ → Tables} (i : Index ppref) (x : Instance ppref)
    (hx3 : Head3 x) (Y : ReqFits R HeadSizes.ref (Req.of (polOf R.h) x))
    (hNB : (Req.of (polOf R.h) x).NB = R.cov.hRC) {Mz : Mats ℤ}
    (T : TrueH Reading.gl W R (colsOf F R.iU3)
      (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)))
    (small : ∀ a r c, |Mz a r c| < 2 ^ 18) {fn : ℕ → ℕ → ℕ → Cb.Gl.E}
    (Kf : ∀ q w, (R.L.calls.getD q default).segs.foldlM
        (fun w g => Model.Head.markColumns R w g)
        (Array.replicate (R.L.calls.getD q default).J 0) = some w →
      KeyFn (R.L.calls.getD q default).segs w (R.L.calls.getD q default).J
      (kvOf (Reading.gl.val (invE (Model.Head.pw (R.h.digSh + 15)))) HeadSizes.ref (npOf R.h)
        (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
        (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Req.of (polOf R.h) x))
      (Reading.gl.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0))) (fn q))
    (claims : ClaimsHold W R F) (claimP : ClaimsPolicy Reading.gl W R F)
    (S : SlotsHold Reading.gl W R (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
      (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Req.of (polOf R.h) x)
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
    (stepC : StepCost (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
      (Req.of (polOf R.h) x) R.h.lt (fun j => pt Reading.gl R.x.Zl (R.h.ls + j)))
    (hl : Top.LayersGive κ tbs i.val x.prompt (cellsH R.h R.L R.b Mz)) :
    RinfR ppref κ (npOf R.h) tbs (polOf R.h) i x :=
  haveI : Cm.TI.Big Cb.Gl.p := Down.big_gl
  Top.rinfR_of_ledger (p := Cb.Gl.p) (normOK_of_policy (policy_of_layout hy) heps)
    (polOK_of_policy (policy_of_layout hy) hC) i x hx3 hl
    (Down.ledgerRF_gl.1 (head_linkL_rf_of_walk hy h1 h2 h3 hsh hXL hTs Xh hPs hs hwalk i x Y hNB T
      small Kf claims claimP S hW hP stepP stepL stepC))

/-- **What the theorems on the head ask of a request, for an instance with the words of the
request's files**: if the plain scalar that hear was handed is the caller's reply as an element of
the field. P, Q: the words of the request file and of the reply file. -/
theorem request_fits {P Q : Array UInt32} {so : Model.Head.StOwn} {R : Model.Head.Run}
    (hst : Model.Head.stFromCall P Q 1024 = .ok so)
    (hc : Model.Head.coveredOf so 1024 202048 = .ok R.cov) (hlt : R.h.lt = 10)
    {hp : Model.Head.HPlanH2} {plain : Array E} {F G : Fork} {C D : Ctx}
    (hx : Ok (Model.Head.hear R.h R.L hp R.cov plain) F C R.x G D)
    (hrep : plain[0]? = some (Model.ofNat so.y)) (x : Instance ppref) (hr : x.r = so.r)
    (he : x.e = so.e)
    (hp' : ∀ t (ht : t < ppref.T), (x.prompt ⟨t, ht⟩).val = (P.getD t 0).toNat)
    (hxy : x.y.val = so.y) :
    Head3 x ∧ ∀ pol, ReqFits R HeadSizes.ref (Req.of pol x) ∧
      (Req.of pol x).NB = R.cov.hRC := by
  have hy := coveredOf_y hc
  obtain ⟨q1, q2, q3, -⟩ := stFromCall_ok hst
  have hT : R.h.T = 1024 := by
    show 2 ^ R.h.lt = 1024
    rw [hlt]
  have hw : R.x.win = Model.Head.winOf R.cov 1024 so.y := by
    rw [hear_win hx, token_of_reply (by omega) hrep, hT]
  obtain ⟨_, f2⟩ := reqFits_of_instance hst hc rfl hw x hr he hp' hxy
  have k1 : x.r = (so.req.getD 1024 0).toNat := by rw [hr, q2, q1]
  have k2 : x.e = (so.req.getD (1024 + 1) 0).toNat := by rw [he, q3, q1]
  exact ⟨head3_of_call hst x hr he hxy, fun pol => ⟨f2 pol, nb_of_covered hc rfl k1 k2⟩⟩

/-- **The head's link for a request with the shape's policy, from seven routines that succeed.** See
the head of this file. -/
theorem head_linkL_of_port {R : Model.Head.Run} {tl tl' tl0 : Model.HTailF2}
    {wo : Model.WsForkOut} {Lc Lc' : Model.LinkCtx} {F G F0 F1 F2 G2 : Fork}
    {C D C0 C1 C2 D2 : Ctx} {W : World Cb.Gl.E} {plain : Array E}
    {g : Model.Settings} {O : Model.Head.Owner} {NGr lkW : ℕ} {H0 : Model.Head.HPlanH2}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hFull : FullH R.h) (hsh : R.h.digSh = 8)
    (hTs : R.h.tabS = 4) (hC : R.h.clipC < 2 ^ 40) (heps : R.h.epsF < 2 ^ 48) (Bd : BorderH R.b)
    (hpl : Model.Head.planH2 g R.h R.L R.b O NGr lkW = .ok H0)
    (hm0 : R.hp.tl.mats = H0.tl.mats) (hN0 : R.hp.tl.NM = H0.tl.NM)
    (hd : C0.ch.dry = false) (hx : Ok (Model.Head.hear R.h R.L R.hp R.cov plain) F0 C0 R.x F1 C1)
    (ht : Ok (Model.Head.tablesOf R.h R.L R.hp R.cov R.x) F2 C2 R.t G2 D2)
    (hs : F.LS.size = F.ns)
    (hwalk : Walk.OkL (Model.Head.walk R tl wo) Lc F C tl' Lc' G D)
    {P Q : Array UInt32} {so : Model.Head.StOwn}
    (hst : Model.Head.stFromCall P Q 1024 = .ok so)
    (hc : Model.Head.coveredOf so 1024 202048 = .ok R.cov)
    (hrep : plain[0]? = some (Model.ofNat so.y))
    {κ : ℕ → LayerScale} {tbs : ℕ → Tables} (i : Index ppref) (x : Instance ppref)
    (hr : x.r = so.r) (he : x.e = so.e)
    (hp' : ∀ t (ht : t < ppref.T), (x.prompt ⟨t, ht⟩).val = (P.getD t 0).toNat)
    (hxy : x.y.val = so.y) {Mz : Mats ℤ}
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
        (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Req.of (polOf R.h) x))
      (Reading.gl.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0))) (fn q))
    (claims : ClaimsHold W R F) (claimP : ClaimsPolicy Reading.gl W R F)
    (S : SlotsHold Reading.gl W R (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
      (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Req.of (polOf R.h) x)
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
    (stepC : StepCost (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
      (Req.of (polOf R.h) x) R.h.lt (fun j => pt Reading.gl R.x.Zl (R.h.ls + j)))
    (hl : Top.LayersGive κ tbs i.val x.prompt (cellsH R.h R.L R.b Mz)) :
    RinfR ppref κ (npOf R.h) tbs (polOf R.h) i x := by
  obtain ⟨hx3, hq⟩ := request_fits hst hc hFull.lt hx hrep x hr he hp' hxy
  exact head_linkL_of_walk hy hFull.lt hFull.d hFull.V hsh hFull.XL hTs hC heps
    (View.heardFits_of_view hd hx) (View.PV_size hd hx) hs hwalk i x hx3 (hq (polOf R.h)).1
    (hq (polOf R.h)).2
    (trueH_of_holds hpl hm0 hN0 hFull (numH_of_layout hFull hy) Bd ht hm hNM holds)
    small Kf claims claimP S hW hP stepP stepL stepC hl

#print axioms ClaimsPolicy.kept
#print axioms head_linkL_rf_of_walk
#print axioms head_linkL_of_walk
#print axioms request_fits
#print axioms head_linkL_of_port

end OnBytes.Road.Hd
