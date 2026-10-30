-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadLinkL.lean: the output head's link for every request with its policy, in one
theorem: from claims of the verifier that hold, and from what each random step is meant to give, to
the library's relation of the request under the policy.

Johnson/Road/HeadLink.lean has the link for a request for the next token, on the library's plain
head (seven families, no cost). This file has its twin on the head with the cost ledger
(Policy/Rel/LedgerHead.lean): nine families, and four clauses on the positions' costs. It uses what
that file uses, and besides
  the four claims of the routine claimPolicy, each form by name
    (Johnson/Road/HeadPolicyForms.lean, over HeadPolicy.lean),
  the way from the calls' key vectors to the relation with the ledger (Johnson/Road/HeadSumL.lean).

What is a hypothesis. All that is one in Johnson/Road/HeadLink.lean (see its head), the lookup's
other claims among them, at the request Req.of pol x. Besides: (1) public: the policy is the
shape's, and the number of counted positions is the run's; (2) two more tables of the reads are
true of the cells; (3) the four claims that claimPolicy adds hold in the world (ClaimsPolicy: it
names the forms by the verifier's own expressions); (4) one more step from a point to all positions,
StepCost: two extensions that are 0 at the point u are extensions of functions that are 0. None of
(2) to (4) is derived from a verifier's acceptance here; (4) is false for some worlds
and points. No probability is stated here.

Main definitions: StepCost.
Main theorems: tabs_of_layout (the table of each family's call is the family's); head_linkL_rf (as
far as the field relation over the challenge field); head_linkL.

The program does not import this file.
-/
import Johnson.Road.HeadLink
import Johnson.Road.HeadSumL
import Johnson.Road.HeadPolicyForms

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Inst.Model Inst.Model.Head
open OnBytes.Model (Reading World Aff Fork SubM Row5)

/-! ## Public facts -/

/-- If every entry of the matrices is below 2^18 in absolute value, so is every cell. -/
theorem smallL_cellsH (h : Model.Head.Shape) (L : Model.Head.HL) (b : Model.Head.Border)
    {Mz : Mats ℤ} (hM : ∀ a r c, |Mz a r c| < 2 ^ 18) : Head.Small (cellsH h L b Mz) :=
  fun _ _ => ⟨fun _ _ => hM _ _ _, fun _ _ => hM _ _ _, fun _ _ => hM _ _ _, fun _ _ => hM _ _ _⟩

/-- The two lists of the nine names agree, and a name belongs to one family. -/
theorem name_inj {s' s : Head.Fam} (e : nameH s' = nameOf s) : s' = s := by
  cases s' <;> cases s <;> first | rfl | (simp [nameH, nameOf] at e)

/-- The library's table for the kind of a family's call is the table in which the verifier looks the
family's keys up. -/
theorem lutOf_kindL (s : Head.Fam) : lutOfKind (famKind s) = lutOfL s := by
  cases s <;> simp [famKind, lutOfKind, lutOfL, Policy.LedgerHead.tableOf]

/-- Each family's name stands in the verifier's list of segments. -/
theorem name_listed (h : Model.Head.Shape) (L : Model.Head.HL) (s : Head.Fam) :
    ∃ x ∈ Model.Head.segments h L, x.1 = nameOf s := by
  cases s
  case NF => exact ⟨("NF", "R16", h.d), by simp [Model.Head.segments], rfl⟩
  case NFH => exact ⟨("NFH", "R16", h.d), by simp [Model.Head.segments], rfl⟩
  case HD0 => exact ⟨("HD0", "R16", L.JV), by simp [Model.Head.segments], rfl⟩
  case HD1 => exact ⟨("HD1", "R16", L.JV), by simp [Model.Head.segments], rfl⟩
  case ROW => exact ⟨("ROW", "R8", Model.ledNRH h.XL), by simp [Model.Head.segments], rfl⟩
  case HD2 => exact ⟨("HD2", "R8", L.JV), by simp [Model.Head.segments], rfl⟩
  case HE0 => exact ⟨("HE0", "FE", L.JVa), by simp [Model.Head.segments], rfl⟩
  case HE1 => exact ⟨("HE1", "FE", L.JV - L.JVa), by simp [Model.Head.segments], rfl⟩
  case CNF => exact ⟨("CNF", "FC", h.d), by simp [Model.Head.segments], rfl⟩

/-- **The table of each family's call is the family's**, in a layout that the verifier's function
returns: the library's table for the kind of the call that a family's name finds is the table in
which the verifier looks the family's keys up. -/
theorem tabs_of_layout {R : Model.Head.Run} {tauFC : Array F}
    (hy : Model.Head.layout R.h tauFC = .ok R.L) (Sf : SegsFit R) (s : Head.Fam) (q : ℕ)
    (hq : Model.Head.callNo R.L (nameOf s) = some q) : tabL R q = lutOfL s := by
  obtain ⟨x, hx, hn⟩ := name_listed R.h R.L s
  obtain ⟨q', g, hq', hg, hgn, _⟩ := mem_of_segHas (segHas_of_layout hy (R := R) rfl rfl x hx)
  rw [hn, hq] at hq'
  obtain rfl := Option.some.inj hq'
  obtain ⟨s', e1, _, e3⟩ := Sf q g hg
  obtain rfl := name_inj (e1.symm.trans (hgn.trans hn))
  unfold tabL
  rw [e3]
  exact lutOf_kindL s'

/-- 2 is not 0 in the challenge field. -/
theorem two_ne_zero_gl : (2 : Cb.Gl.E) ≠ 0 := by
  obtain ⟨c, hc⟩ := Down.exists_inv23 (K := Cb.Gl.E) (p := Cb.Gl.p)
    (algebraMap Cb.Gl.F Cb.Gl.E) (by have h := Down.gl_big; omega)
  intro h0
  rw [h0, zero_pow (by decide), mul_zero] at hc
  exact zero_ne_one hc

/-! ## The step on the costs -/

/-- The step from one point to all positions, as a hypothesis, for the two clauses on a position's
cost: if the extensions of both are 0 at the point u, both are 0 at every position. It reads no
world: cells, request and point alone. It is false for some cells and points. What could make that
rare is an order which no statement here has: the cells are fixed before the point is drawn. -/
def StepCost (t : Head.Cells Cb.Gl.E) (y : Req) (lt : ℕ) (u : ℕ → Cb.Gl.E) : Prop :=
  Blocks.ext lt (fun a => dB4 t y a) u = 0 → Blocks.ext lt (fun a => dZ t y a) u = 0 →
    ∀ a < nT, dB4 t y a = 0 ∧ dZ t y a = 0

/-! ## The link -/

/-- The head's link for a request with its policy, as far as the field relation of the library's
head with the cost ledger over the challenge field: head_linkL below without what the layers must
give. Fp: the state from which the routine claimPolicy runs; every array has as many columns in it
as in the state F. -/
theorem head_linkL_rf {R : Model.Head.Run} {F : Fork} {C : Ctx} {W : World Cb.Gl.E}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (h1 : R.h.lt = 10) (hF : R.h.famF = 24)
    (hT : R.h.tabS = 4) (Sf : SegsFit R) (pol : AcceptancePolicy) (i : Index ppref) (x : Instance ppref)
    {Mz : Mats ℤ}
    {low u v : ℕ → Cb.Gl.E} {p : ℕ → ℕ → Cb.Gl.E}
    (X : LinesFit Reading.gl W R HeadSizes.ref (colsOf F R.iU3)
      (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)) (Req.of pol x) low u)
    (hPV : ShortAt W R (colsOf F R.iU3) "hr@P_V" R.h.lt v
      (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)).hr)
    (small : ∀ a r c, |Mz a r c| < 2 ^ 18)
    (A : CallsAt Reading.gl R u p) {w : ℕ → Array ℕ} {fn : ℕ → ℕ → ℕ → Cb.Gl.E}
    (hw : ∀ q, (R.L.calls.getD q default).segs.foldlM
      (fun w g => Model.Head.markColumns R w g)
      (Array.replicate (R.L.calls.getD q default).J 0) = some (w q))
    (Kf : ∀ q, KeyFn (R.L.calls.getD q default).segs (w q) (R.L.calls.getD q default).J
      (kvOf (Reading.gl.val (invE (Model.Head.pw (R.h.digSh + 15)))) HeadSizes.ref (npOf R.h)
        (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
        (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Req.of pol x))
      (Reading.gl.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0))) (fn q))
    {KF : Array Aff} (hKF : FormsOf R F C KF) {q5 : Row5 Aff}
    (hq5 : RowOf R (colsOf F R.iU3) "P_V" q5)
    (claimJ : (joinForm R.x.g1 KF).value Reading.gl W = 0)
    (claimL : ∀ k, k < 17 → ((ledCarries R q5 ++ ledTail R q5).getD k {}).value Reading.gl W = 0)
    (S : SlotsHold Reading.gl W R (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
      (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Req.of pol x) u)
    (hW : ∀ s, s < 9 → W.slot (R.x.sW + s) = Blocks.ext R.h.lt (fun a => Ledger.Wsum nD
      (fun l j => bl (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)) l j a) s) v)
    (hP : ∀ j, j < 7 → W.slot (R.x.sPv + j) = Blocks.ext R.h.lt (fun a => Ledger.prods
      (fun n => Dv (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)) n a) j) v)
    (stepP : StepPoint (npOf R.h) (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
      R.h.lt v)
    {A' : Array Aff} (claimK : LookupMeans W R A') (stepL : StepLookup W R A' fn p)
    {Fp Gp : Fork} {Cp Dp : Ctx} {w0 : Unit} (kp : Walk.Kept F Fp)
    (hNB : (Req.of pol x).NB = R.cov.hRC) (hpC : pol.C = R.h.clipC)
    (hpT : pol.theta = R.h.theta) (hpK : pol.cap = R.h.cap)
    (hRho : SumAt W R (colsOf F R.iU3) "hr@rhoC" nT (fun φ a =>
      (((Req.of pol x).rhoC a : ℤ) : Cb.Gl.E) *
        (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)).hr φ a))
    (hZ : FlatAt W R (colsOf F R.iU3) "hf@phiZ" R.h.ls R.h.lt u (fun φ a =>
      (((Req.of pol x).rhoC a : ℤ) : Cb.Gl.E) *
        (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)).hf φ a))
    (hPol : Ok (Model.Head.claimPolicy R) Fp Cp w0 Gp Dp)
    (claimP : ClaimsPolicy Reading.gl W R F)
    (stepC : StepCost (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
      (Req.of pol x) R.h.lt u) :
    Policy.LedgerHead.RF (F := Cb.Gl.E) (npOf R.h) (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E))
      (Req.of pol x) (cellsH R.h R.L R.b Mz) := by
  have idns := stepP fun k hk => by
    rw [← ledger_idn_plain gl_numerals hq5 hPV hk hW hP]
    exact claimL k hk
  have keys := stepL claimK (by
    rw [← joinForm_worth gl_numerals _ X A S hw Kf hKF]
    exact claimJ)
  obtain ⟨z1, z2, z3, z4⟩ := policy_of_claims_ref gl_numerals X.laid X.req X.XL hF X.qH X.uHD0
    hNB hpC hpT hpK hRho X.phiC hZ kp hPol claimP
  have jc := stepC z3 z4
  have hc := iw_23 gl_numerals gl_inverse two_ne_zero_gl X.sh
  exact ledgerRF_of_calls hc (tz := cellsH R.h R.L R.b Mz)
    (callsFitL_of_layout hy h1 X.laid.d X.laid.V X.XL rfl rfl (tabs_of_layout hy Sf) _
      (npOf R.h) _ _ _) hw Kf (smallL_cellsH R.h R.L R.b small)
    (fun q j hj a ha => by
      obtain ⟨u', hu, e⟩ := keys q j hj a ha
      rw [e]
      exact rows_of_port gl_numerals hy hF X.sh hT hj hu)
    idns jc ⟨z1, z2⟩

/-- **The head's link for every request with its policy.** See the head of this file for what is a
hypothesis. The letters are those of head_link in Johnson/Road/HeadLink.lean. If, BESIDES the public
facts, the true tables, the small entries, what the slots hold, the three steps and what the layers
must give, the 17 claims of the ledger, the claim on the calls' key vectors, the lookup's other
claims and the four claims on the costs hold in W, then the library's relation of the request x
holds under the policy pol. That the 48 layers run, and that the head's cells of the stream are the
program's, is a hypothesis (hl). Nothing here ties the index i to a commitment. -/
theorem head_linkL {R : Model.Head.Run} {F : Fork} {C : Ctx} {W : World Cb.Gl.E}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (h1 : R.h.lt = 10) (hF : R.h.famF = 24)
    (hT : R.h.tabS = 4) (Sf : SegsFit R) {κ : ℕ → LayerScale} {tbs : ℕ → Tables}
    (hn : (npOf R.h).OK) {pol : AcceptancePolicy} (hpol : pol.OK) (i : Index ppref) (x : Instance ppref)
    (h3 : Head3 x) {Mz : Mats ℤ}
    {low u v : ℕ → Cb.Gl.E} {p : ℕ → ℕ → Cb.Gl.E}
    (X : LinesFit Reading.gl W R HeadSizes.ref (colsOf F R.iU3)
      (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)) (Req.of pol x) low u)
    (hPV : ShortAt W R (colsOf F R.iU3) "hr@P_V" R.h.lt v
      (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)).hr)
    (small : ∀ a r c, |Mz a r c| < 2 ^ 18)
    (A : CallsAt Reading.gl R u p) {w : ℕ → Array ℕ} {fn : ℕ → ℕ → ℕ → Cb.Gl.E}
    (hw : ∀ q, (R.L.calls.getD q default).segs.foldlM
      (fun w g => Model.Head.markColumns R w g)
      (Array.replicate (R.L.calls.getD q default).J 0) = some (w q))
    (Kf : ∀ q, KeyFn (R.L.calls.getD q default).segs (w q) (R.L.calls.getD q default).J
      (kvOf (Reading.gl.val (invE (Model.Head.pw (R.h.digSh + 15)))) HeadSizes.ref (npOf R.h)
        (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
        (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Req.of pol x))
      (Reading.gl.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0))) (fn q))
    {KF : Array Aff} (hKF : FormsOf R F C KF) {q5 : Row5 Aff}
    (hq5 : RowOf R (colsOf F R.iU3) "P_V" q5)
    (claimJ : (joinForm R.x.g1 KF).value Reading.gl W = 0)
    (claimL : ∀ k, k < 17 → ((ledCarries R q5 ++ ledTail R q5).getD k {}).value Reading.gl W = 0)
    (S : SlotsHold Reading.gl W R (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
      (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Req.of pol x) u)
    (hW : ∀ s, s < 9 → W.slot (R.x.sW + s) = Blocks.ext R.h.lt (fun a => Ledger.Wsum nD
      (fun l j => bl (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)) l j a) s) v)
    (hP : ∀ j, j < 7 → W.slot (R.x.sPv + j) = Blocks.ext R.h.lt (fun a => Ledger.prods
      (fun n => Dv (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)) n a) j) v)
    (stepP : StepPoint (npOf R.h) (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
      R.h.lt v)
    {A' : Array Aff} (claimK : LookupMeans W R A') (stepL : StepLookup W R A' fn p)
    {Fp Gp : Fork} {Cp Dp : Ctx} {w0 : Unit} (kp : Walk.Kept F Fp)
    (hNB : (Req.of pol x).NB = R.cov.hRC) (hpC : pol.C = R.h.clipC)
    (hpT : pol.theta = R.h.theta) (hpK : pol.cap = R.h.cap)
    (hRho : SumAt W R (colsOf F R.iU3) "hr@rhoC" nT (fun φ a =>
      (((Req.of pol x).rhoC a : ℤ) : Cb.Gl.E) *
        (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)).hr φ a))
    (hZ : FlatAt W R (colsOf F R.iU3) "hf@phiZ" R.h.ls R.h.lt u (fun φ a =>
      (((Req.of pol x).rhoC a : ℤ) : Cb.Gl.E) *
        (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)).hf φ a))
    (hPol : Ok (Model.Head.claimPolicy R) Fp Cp w0 Gp Dp)
    (claimP : ClaimsPolicy Reading.gl W R F)
    (stepC : StepCost (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
      (Req.of pol x) R.h.lt u)
    (hl : Top.LayersGive κ tbs i.val x.prompt (cellsH R.h R.L R.b Mz)) :
    RinfR ppref κ (npOf R.h) tbs pol i x :=
  haveI : Cm.TI.Big Cb.Gl.p := Down.big_gl
  Top.rinfR_of_ledger (p := Cb.Gl.p) hn hpol i x h3 hl
    (Down.ledgerRF_gl.1 (head_linkL_rf hy h1 hF hT Sf pol i x X hPV small A hw Kf hKF hq5 claimJ
      claimL S hW hP stepP claimK stepL kp hNB hpC hpT hpK hRho hZ hPol claimP stepC))

#print axioms tabs_of_layout
#print axioms head_linkL_rf
#print axioms head_linkL

end OnBytes.Road.Hd
