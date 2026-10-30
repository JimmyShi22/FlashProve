-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadLinkRun.lean: the output head's link, from the verifier's own routines.

Johnson/Road/HeadLink.lean has one theorem, head_link, on a run R of the head's check. Among its
hypotheses are records on the layout, on the calls' key points and on the tables of the reads, and
forms that the verifier's routines return. Here these come from the verifier's own words:
  the layout is what the function layout returns;
  what was heard has passed the tests of the routine hear (HeardFits,
    Johnson/Road/HeadPoint.lean);
  the tables of the reads are those that tablesOf returns, and every record of that list holds what
    it says of its matrix (through TrueH in Johnson/Road/HeadReads.lean);
  the routine walk, which adds all claims, succeeds.
The forms of which "the claim holds" is said are then forms that walk adds: for the ledger's and the
join's that is used here; for the lookup's other claims it is shown in
Johnson/Road/HeadWalkLists.lean (walk_lists), which no theorem of this file reads.

Main definitions: ClaimsHold (the named claims hold, whichever forms the routines return from a
state that the walk can be in); StepLookupAt.
Main theorems: callsLaid_of_layout, callsAt_of_run, walk_planes; head_link_rf_of_walk,
head_link_of_walk.

What is not claimed. As in Johnson/Road/HeadLink.lean: what the smallness test, the batching of the
claims, four sumchecks, the lookup and the point P_V are meant to give are hypotheses, and so is
what the layers must give. So are seven numbers of the shape, the length of the point P_V, that the
walk begins in a state with one coefficient for each slot, and hT: the routine of the smallness test
keeps the state (hT is not used for these claims). The program does not import this file.
-/
import Johnson.Road.HeadLink
import Johnson.Road.HeadWalk
import Johnson.Road.HeadFit
import Johnson.Road.HeadFound
import Johnson.Road.HeadCallsLaid

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Inst.Model Inst.Model.Head
open OnBytes.Model (Reading World Aff Fork SubM Row5)

/-- Public facts on the calls of a layout: each has 2^lJ columns, and each of its segments is the
one that its name finds and bears one of the nine names. -/
def CallsLaid (R : Model.Head.Run) : Prop :=
  ∀ q, q < R.L.calls.size →
    (R.L.calls.getD q default).J = 2 ^ (R.L.calls.getD q default).lJ ∧
    ∀ g ∈ (R.L.calls.getD q default).segs, Found R q g ∧ ∃ s, g.name = nameOf s

/-- These facts hold of a layout that the verifier's function returns. -/
theorem callsLaid_of_layout {R : Model.Head.Run} {tauFC : Array F}
    (hy : Model.Head.layout R.h tauFC = .ok R.L) : CallsLaid R := by
  intro q hq
  refine ⟨cols_of_layout hy hq, fun g hg => ⟨found_of_layout hy hq hg, ?_⟩⟩
  obtain ⟨x, hx, e⟩ := names_of_layout hy hq hg
  unfold Model.Head.segments at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.NF, e⟩
  · exact ⟨.NFH, e⟩
  · exact ⟨.HD0, e⟩
  · exact ⟨.HD1, e⟩
  · exact ⟨.ROW, e⟩
  · exact ⟨.HD2, e⟩
  · exact ⟨.CNF, e⟩
  · exact ⟨.HE0, e⟩
  · exact ⟨.HE1, e⟩

/-- What Johnson/Road/HeadLink.lean asks of the calls and their key points, at the points that were
heard. -/
theorem callsAt_of_run {K : Type} [Field K] (ρ : Reading K) {R : Model.Head.Run} {tauFC : Array F}
    (hy : Model.Head.layout R.h tauFC = .ok R.L) (Xh : HeardFits R.h R.L R.cov R.x)
    (A : CallsLaid R) :
    CallsAt ρ R (fun j => pt ρ R.x.Zl (R.h.ls + j)) (fun q => pt ρ (R.x.g1.zk.getD q #[])) := by
  intro q hq
  obtain ⟨a1, a2⟩ := A q hq
  obtain ⟨b1, b2, b3⟩ := point_of_run hy Xh ρ (R := R) rfl rfl rfl hq
  exact ⟨a1, b1, b2, b3, a2⟩

/-- Claims of the walk hold in W. F: the state in which the walk begins. The claims are named
through the routines: the 17 forms of the ledger on any row that is read in the table "hr@P_V"; the
lookup's form of any forms that keyForm returns from a state in which every array has as many
columns as in F; the lookup's claims that read mask entries alone; and any three forms on the planes
that planeClaims returns from such a state. -/
def ClaimsHold (W : World Cb.Gl.E) (R : Model.Head.Run) (F : Fork) : Prop :=
  (∀ q5, RowOf R (colsOf F R.iU3) "P_V" q5 → ∀ k, k < 17 →
    ((ledCarries R q5 ++ ledTail R q5).getD k {}).value Reading.gl W = 0) ∧
  (∀ F4 c4 KF, Walk.Kept F F4 → FormsOf R F4 c4 KF →
    (joinForm R.x.g1 KF).value Reading.gl W = 0) ∧
  (∀ f ∈ R.x.g1.rows, f.value Reading.gl W = 0) ∧
  ∀ F6 c6 A, Walk.Kept F F6 → PlanesOf R F6 c6 A → ∀ f ∈ A, f.value Reading.gl W = 0

/-- The lookup's step for the forms on the planes that planeClaims returns from a state of the
walk. -/
def StepLookupAt (W : World Cb.Gl.E) (R : Model.Head.Run) (F : Fork) (fn : ℕ → ℕ → ℕ → Cb.Gl.E)
    (p : ℕ → ℕ → Cb.Gl.E) : Prop :=
  ∀ F6 c6 A, Walk.Kept F F6 → PlanesOf R F6 c6 A → StepLookup W R A fn p

/-- The named claims hold from a later state of the same shape, if they hold from an earlier one. -/
theorem ClaimsHold.kept {W : World Cb.Gl.E} {R : Model.Head.Run} {F Fw : Fork}
    (k : Walk.Kept F Fw) (h : ClaimsHold W R F) : ClaimsHold W R Fw :=
  ⟨fun q5 hq j hj => h.1 q5 (by rw [← k.2 R.iU3]; exact hq) j hj,
    fun F4 c4 KF k4 hKF => h.2.1 F4 c4 KF (k.trans k4) hKF, h.2.2.1,
    fun F6 c6 A k6 hA => h.2.2.2 F6 c6 A (k.trans k6) hA⟩

/-- The same for the lookup's step. -/
theorem StepLookupAt.kept {W : World Cb.Gl.E} {R : Model.Head.Run} {F Fw : Fork}
    {fn : ℕ → ℕ → ℕ → Cb.Gl.E} {p : ℕ → ℕ → Cb.Gl.E} (k : Walk.Kept F Fw)
    (h : StepLookupAt W R F fn p) : StepLookupAt W R Fw fn p :=
  fun F6 c6 A k6 hA => h F6 c6 A (k.trans k6) hA

/-- The walk runs claimPlanes from a state in which every array has as many columns as at its
beginning. -/
theorem walk_planes {R : Model.Head.Run} {tl tl' : Model.HTailF2} {wo : Model.WsForkOut}
    {Lc Lc' : Model.LinkCtx} {F G : Fork} {C D : Ctx} (hXL : R.h.XL = 5)
    (hs : F.LS.size = F.ns) (h : Walk.OkL (Model.Head.walk R tl wo) Lc F C tl' Lc' G D) :
    ∃ F6 c6 F7 d6, Walk.Kept F F6 ∧ Ok (Model.Head.claimPlanes R) F6 c6 () F7 d6 := by
  obtain ⟨_, F1, F2, F3, F4, F5, F6, F7, F8, F9, c1, c2, c3, c4, c5, c6, c7, c8, c9,
    d0, d1, d2, d3, d4, d5, d6, d7, d8, d9,
    a0, _, a1, _, a2, _, a3, _, a4, _, a5, _, a6, _, _, _, _, _, _, _⟩ := Walk.walk_parts h
  have k1 : Walk.Kept F F1 := Walk.keeps_objects _ F C _ F1 d0 hs a0
  have k2 : Walk.Kept F F2 := k1.trans ((Walk.adds_claimSquares R).keeps F1 c1 _ F2 d1 k1.1 a1)
  have k3 : Walk.Kept F F3 := k2.trans (Walk.keeps_claimLedger hXL F2 c2 _ F3 d2 k2.1 a2)
  have k4 : Walk.Kept F F4 := k3.trans ((Walk.adds_claimStream hXL).keeps F3 c3 _ F4 d3 k3.1 a3)
  have k5 : Walk.Kept F F5 := k4.trans (Walk.keeps_claimJoin R F4 c4 _ F5 d4 k4.1 a4)
  have k6 : Walk.Kept F F6 := k5.trans ((Walk.adds_claimPolicy R).keeps F5 c5 _ F6 d5 k5.1 a5)
  exact ⟨F6, c6, F7, d6, k6, a6⟩

/-- The same as head_link_of_walk below, as far as the field relation of the library's plain head
over the challenge field. -/
theorem head_link_rf_of_walk {R : Model.Head.Run} {tl tl' : Model.HTailF2} {wo : Model.WsForkOut}
    {Lc Lc' : Model.LinkCtx} {F G : Fork} {C D : Ctx} {W : World Cb.Gl.E}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (h1 : R.h.lt = 10) (h2 : R.h.d = 5120)
    (h3 : R.h.V = 202048) (hsh : R.h.digSh = 8) (hXL : R.h.XL = 5) (hF : R.h.famF = 24)
    (hTs : R.h.tabS = 4)
    (Xh : HeardFits R.h R.L R.cov R.x) (hPs : R.x.PV.size = R.h.lt)
    (hs : F.LS.size = F.ns) (hT : Walk.Keeps (tl.objectsF R.t.funs))
    (hwalk : Walk.OkL (Model.Head.walk R tl wo) Lc F C tl' Lc' G D)
    (i : Index ppref) (x : Instance ppref) (hr : x.r = 1023)
    (Y : ReqFits R HeadSizes.ref (Cm.reqOf x)) {Mz : Mats ℤ}
    (T : TrueH Reading.gl W R (colsOf F R.iU3)
      (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)))
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
      (Cm.reqOf x) (cellsH R.h R.L R.b Mz) := by
  choose w hw using marks_of_layout (R := R) hy
  have Hs : HasAll R := hasAll_of_layout hy h1 h2 h3 hXL
  have A := callsLaid_of_layout hy
  obtain ⟨F1, F2, F3, F4, F5, F6, F8, F9, c1, c2, c3, c4, c5, c8, _, ⟨k2, a2, _⟩, _,
    ⟨k4, a4, _⟩, _, _⟩ := Walk.walk_states hXL hs hT hwalk
  obtain ⟨_, _, q5, _, hq5, _⟩ := ok_claimLedger hXL k2.1 a2
  rw [k2.2 R.iU3] at hq5
  obtain ⟨_, KF, hKF, _⟩ := claimJoin_form
    (fun q laid y G' D' hk => Walk.leaves_keyForm R q laid F4 c4 y G' D' hk) a4
  have X := linesFit_of_run hy Xh Reading.gl (R := R) rfl rfl rfl h1 h2 h3 hsh hXL Y
    (reqOf_ok x) T
  have hPV := shortAt_of_sum hPs T.hrPV
  obtain ⟨F6, c6, F7, d6, k6, a6⟩ := walk_planes hXL hs hwalk
  obtain ⟨A', hA'⟩ := planesOf_of_claim a6
  rw [← k4.2 R.iU3] at X hPV hq5
  exact head_link_rf hy hF hTs Hs i x hr X hPV small (callsAt_of_run Reading.gl hy Xh A) hw
    (fun q => Kf q (w q) (hw q)) hKF hq5 (claims.2.1 F4 c4 KF k4 hKF)
    (fun k hk => claims.1 q5 (by rw [← k4.2 R.iU3]; exact hq5) k hk) S hW hP stepP
    ⟨claims.2.2.1, claims.2.2.2 F6 c6 A' k6 hA'⟩ (stepL F6 c6 A' k6 hA')

/-- **The head's link, from the verifier's own routines.** See the heads of this file and of
Johnson/Road/HeadLink.lean for what is a hypothesis. -/
theorem head_link_of_walk {R : Model.Head.Run} {tl tl' : Model.HTailF2} {wo : Model.WsForkOut}
    {Lc Lc' : Model.LinkCtx} {F G : Fork} {C D : Ctx} {W : World Cb.Gl.E}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (h1 : R.h.lt = 10) (h2 : R.h.d = 5120)
    (h3 : R.h.V = 202048) (hsh : R.h.digSh = 8) (hXL : R.h.XL = 5) (hF : R.h.famF = 24)
    (hTs : R.h.tabS = 4)
    (Xh : HeardFits R.h R.L R.cov R.x) (hPs : R.x.PV.size = R.h.lt)
    (hs : F.LS.size = F.ns) (hT : Walk.Keeps (tl.objectsF R.t.funs))
    (hwalk : Walk.OkL (Model.Head.walk R tl wo) Lc F C tl' Lc' G D)
    {κ : ℕ → LayerScale} {tbs : ℕ → Tables} (hn : (npOf R.h).OK)
    (i : Index ppref) (x : Instance ppref) (hr : x.r = 1023) (he : x.e = 1024)
    (Y : ReqFits R HeadSizes.ref (Cm.reqOf x)) {Mz : Mats ℤ}
    (T : TrueH Reading.gl W R (colsOf F R.iU3)
      (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)))
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
    (head_link_rf_of_walk hy h1 h2 h3 hsh hXL hF hTs Xh hPs hs hT hwalk i x hr Y T small Kf claims
      S hW hP stepP stepL) hl pol

#print axioms callsLaid_of_layout
#print axioms callsAt_of_run
#print axioms walk_planes
#print axioms head_link_rf_of_walk
#print axioms head_link_of_walk

end OnBytes.Road.Hd
