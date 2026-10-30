-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/VecTieLay.lean: VecTie (AtFullSide/K1/VecTie.lean) AT THE TWELVE LAYERS' READS. The thread's half: from
Thr's Made to the hearing's return on the rounds of what was heard, and to the pure half funs_honest
(AtFullSide/K1/VecTieLayers.lean). wit is free: valsAt at a layers' segment does not read the cover.

  layers_written     under the head: the families and the matrices are the written ones
  partsLaid, partsW, partsW_yes, partsW_can_fail   a closed test: partsFit at the written laying
  funsOf_parts       what funsOf returns has the laying's numbers
  partsFit_lay       partsFit at a layers' segment, where each table has as many weights as its length
  layers_vec_returns where funsOf and partsFit return the maker's vector returns
  callsShape_eq      the site's shape is the layout's
  start_le           the rounds of K4's row reach its last sumcheck's start
  vecTie_layers      THE CLAIM
  nReads_lay, vecTie_layers_head   the same at nReads, the plan drawn under the head

NO PROPERTY IS CLAIMED.
-/
import AtFullSide.K1.VecTie
import AtFullSide.K1.ReadsCount
import AtFullSide.K1.VecTieLayers
import Johnson.AtFull.Shape.PhiLayAtReads
import Johnson.Desc.ProofFile.Honest.K1.Law.AttFunsAtHead
import Johnson.Desc.ProofFile.Honest.K1.Law.TieReadsLayers
import Johnson.HonestTrace.U3Fit.ReturnsAtHead
import Johnson.HonestTrace.U3Fit.ValsSorts
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LayersTieHead
import Johnson.Desc.ProofFile.Honest.K4.Law.RowKit
import Johnson.Desc.K8.Honest.ReadsSeat
import Johnson.Desc.ProofFile.Honest.K4.Law.StartsAre

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Model (HTailF2 HFun TMat)
open OnBytes.Model.Layer (HPlan2 TableAsk TableAt layTables tableAsks funsOf phiOf)
open OnBytes.HonestTrace (pairOf heardOf parOfMats)
open OnBytes.HonestTrace.U3 (u3Seats placeIn sizesOf partsFit SegVals valsAt layersVals covOf errOf have_)
open OnBytes.HonestTrace.U3.Fit (sizesAt asksW)
open OnBytes.Road (flatLaid)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In ptsOf namedPts)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K3 (lookHeardAt OpenSame matsOwn)
open ProofFile.Honest.K4 (k4LookOf k4StartAt DrawnIs paired_drawn)
open ProofFile.Honest.K8 (cellsAtOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

private theorem okBind {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem someHave {α : Type} {n : String} {o : Option α} {a : α}
    (h : have_ n o = .ok a) : o = some a := by
  cases o with
  | none => cases h
  | some x => exact congrArg some (Except.ok.inj h)

/-! ## 1 The laying, at written values -/

/-- The parts of a laying, each with as many weights as its length. -/
def partsLaid (laid : List (TableAsk × List (ℕ × ℕ))) : List (ℕ × ℕ × ℕ × ℕ) :=
  (flatLaid laid).map fun t => (t.2.1, t.1.L, t.1.L, t.2.2)

/-- **A TEST AT WRITTEN VALUES**: at each group the laying passes partsFit at a number of reads off by d. -/
def partsW (d : ℕ) : Bool :=
  (List.range 12).all fun g =>
    match layTables (sizesAt (2 * g)) (asksW false false false g) 0 with
    | some x => (errOf (partsFit (sizesAt (2 * g)) (partsLaid x.2.1) (x.2.2 + d))).isNone
    | none => false

set_option maxRecDepth 1000000 in
/-- The kernel's yes. -/
theorem partsW_yes : partsW 0 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: at one read more the test says no. -/
theorem partsW_can_fail : partsW 1 = false := by decide +kernel

/-- What funsOf's list holds, as partsFit reads it: at tables with as many weights as their length. -/
theorem funsOf_parts {y : OnBytes.Model.Layer.Lay} {fo : OnBytes.Model.Forest.Heard}
    {pt : List (String × Array OnBytes.E)} {laid : List (TableAsk × List (ℕ × ℕ))} {funs : Array HFun}
    (h : funsOf y fo pt laid = some funs) (hphi : ∀ f ∈ funs.toList, f.phi.size = f.len) :
    OnBytes.HonestTrace.U3.partsOf funs = partsLaid laid := by
  unfold funsOf at h
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨l, hl, rfl⟩ := h
  have key : ∀ (laid : List (TableAsk × List (ℕ × ℕ))) (l : List (List HFun)),
      (laid.mapM fun x => (phiOf y fo pt x.1).bind fun phi =>
        some (x.2.map fun m => ({ mat := m.1, len := x.1.L, phi, tree := 2, start := m.2 } : HFun))) = some l →
      l.flatten.map (fun f => (f.mat, f.len, f.start)) = (flatLaid laid).map fun t => (t.2.1, t.1.L, t.2.2) := by
    intro laid
    induction laid with
    | nil =>
      intro l e
      have : l = [] := by simpa using e.symm
      subst this
      rfl
    | cons a rest ih =>
      intro l e
      rw [List.mapM_cons] at e
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at e
      obtain ⟨b, ⟨phi, hphi, rfl⟩, t, ht, rfl⟩ := e
      have := ih t ht
      simp only [List.flatten_cons, List.map_append, List.map_map]
      rw [this]
      unfold flatLaid
      simp [Function.comp_def]
  have e := key laid l (by simpa using hl)
  have e2 : OnBytes.HonestTrace.U3.partsOf l.flatten.toArray =
      (l.flatten.map fun f => (f.mat, f.len, f.start)).map fun t => (t.1, t.2.1, t.2.1, t.2.2) := by
    unfold OnBytes.HonestTrace.U3.partsOf
    rw [List.map_map]
    simp only [List.toList_toArray] at hphi ⊢
    refine List.map_congr_left fun f hf => ?_
    show (f.mat, f.len, f.phi.size, f.start) = (f.mat, f.len, f.len, f.start)
    rw [hphi f hf]
  rw [e2, e]
  unfold partsLaid
  rw [List.map_map]
  rfl

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

open OnBytes.HonestTrace.U3.Fit in
/-- **Under the head the families and the matrices of a group are the written ones.** -/
theorem layers_written (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {g : ℕ} (hg : g < 12)
    {hp : HPlan2} (e : G.W.G[g]? = some hp) :
    tableAsks G.W.layers.y G.W.layers.rd g = asksW false false false g ∧
      sizesOf hp.tl.mats = sizesAt (2 * g) := by
  have hX := IM.ground_publicK h.laid.pub hG
  have M := marks_at_head h hG
  obtain ⟨p0, p1, pla, pT, pmb, p4, -⟩ := layersNums_at_head h hG
  obtain ⟨rq, ro, rQ, l1, l2, l3, l4, l5, l6, l7⟩ := lists_at_head h hG
  obtain ⟨ls, -, eW, -, eF⟩ := IM.blank_ground hG
  obtain ⟨hp', a, Xl, -, e', ea, e3, t1, -⟩ :=
    (IM.ground_tails h.scope h.reads h.laid.pub hG).1 g hg
  obtain rfl : hp = hp' := Option.some.inj (e.symm.trans e')
  obtain ⟨Xl', -, f2, kd, kg, -⟩ := (IM.ground_named h.scope h.reads h.laid.pub hG).1 g hg
  obtain rfl : Xl = Xl' := Option.some.inj (e3.symm.trans f2)
  have etl := tlOf_even M hg e
  have hk : 2 * g < 25 := by omega
  have eA : tableAsks G.W.layers.y G.W.layers.rd g = asksW rq ro rQ g := by
    rw [tableAsks_by]
    show asksBy (G.W.y.parts.getD 0 0) (G.W.y.parts.getD 1 0) (2 ^ G.W.y.h.la) G.W.y.T
      (2 ^ G.W.y.h.lmb) G.W.y.h.p4 _ _ _ _ _ _ _ g = _
    rw [p0, p1, pla, pT, pmb, p4, l1, l2, l3, l4, l5, l6, l7]
    rfl
  have eT : (ProofFile.k8Par Zp G Xl (2 * g)).asks = triplesW rq ro rQ g := by
    show ProofFile.k8Asks G Xl = _
    unfold ProofFile.k8Asks
    rw [kd, kg]
    show VerifiableInference.Desc.First.K8.Asks.layers G.W.y G.W.layers.rd g = _
    rw [layers_by, p0, p1, pla, pT, pmb, p4, l1, l2, l3, l4, l5, l6, l7]
    rfl
  have eks : (ProofFile.k8Par Zp G Xl (2 * g)).ks = ksW (2 * g) := by
    show Xl.tl.mats.toList.map (·.k) = _
    rw [t1, ← etl]
    exact ks_at_head h hG hk
  have ems : (ProofFile.k8Par Zp G Xl (2 * g)).ms = msW (2 * g) := by
    show Xl.tl.mats.toList.map (·.m) = _
    rw [t1, ← etl]
    exact ms_at_head h hG hk
  have eL : Zp.first.layout = Johnson.G.layoutFull := by
    rw [← eF]
    exact (first_at_head h hG).2.2
  obtain ⟨A, a1, -, a3⟩ :=
    OnBytes.Road.K4.Plan.u3_cols_lay h.scope h.reads h.laid.pub hG hg e3
  rw [OnBytes.Road.K4.Plan.end_sum0, eT, famSum_by, eks, ems] at a3
  have eC : A.sizeC = colsW (2 * g) := by
    unfold colsW
    rw [← eL, a1]
    rfl
  have w := List.all_eq_true.1 laidW_yes g (List.mem_range.2 hg)
  rw [Bool.and_eq_true] at w
  obtain ⟨w1, -⟩ := w
  have mem : ∀ b : Bool, b ∈ [false, true] := fun b => by cases b <;> decide
  have w3 := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 w1 rq (mem rq)) ro (mem ro))
    rQ (mem rQ)
  rw [eC] at a3
  rw [decide_eq_true a3] at w3
  have w4 : (!rq && !ro && !rQ) = true := w3
  obtain ⟨rfl, rfl, rfl⟩ : rq = false ∧ ro = false ∧ rQ = false := by
    cases rq <;> cases ro <;> cases rQ <;> first | exact ⟨rfl, rfl, rfl⟩ | cases w4
  refine ⟨eA, ?_⟩
  rw [← etl]
  exact sizes_at_head h hG hk

/-- **partsFit at a layers' segment, where each table has as many weights as its length.** -/
theorem partsFit_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {g : ℕ} (hg : g < 12)
    {hp : HPlan2} (e : G.W.G[g]? = some hp)
    {y : OnBytes.Model.Layer.Lay} {fo : OnBytes.Model.Forest.Heard}
    {pt : List (String × Array OnBytes.E)} {xl : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
    {funs : Array HFun}
    (hx : layTables (sizesOf hp.tl.mats) (tableAsks G.W.layers.y G.W.layers.rd g) 0 = some xl)
    (hf : funsOf y fo pt xl.2.1 = some funs) (hphi : ∀ f ∈ funs.toList, f.phi.size = f.len) :
    partsFit (sizesOf hp.tl.mats) (OnBytes.HonestTrace.U3.partsOf funs) xl.2.2 = .ok () := by
  obtain ⟨eA, eS⟩ := layers_written h hG hg e
  rw [eS, eA] at hx
  rw [eS, funsOf_parts hf hphi]
  have w := List.all_eq_true.1 partsW_yes g (List.mem_range.2 hg)
  simp only [hx, Nat.add_zero] at w
  cases hp' : partsFit (sizesAt (2 * g)) (partsLaid xl.2.1) xl.2.2 with
  | error m =>
    rw [hp'] at w
    cases w
  | ok u => rfl

end

/-! ## 2 The maker -/

/-- **Where funsOf and partsFit return, the layers' vector returns.** -/
theorem layers_vec_returns {Z : ProofFile.Pub} {G : ProofFile.Ground} {sps : List Spot} {seg g : ℕ} {V : SegVals}
    (hV : layersVals Z G sps seg g = .ok V) {hp : HPlan2} {k4 k3 : Spot × ℕ}
    {xl : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {funs : Array HFun}
    (hA : G.W.G[g]? = some hp) (h4 : placeIn Z sps seg .K4 = .ok k4) (h3 : placeIn Z sps seg .K3 = .ok k3)
    (hx : layTables (OnBytes.Desc.First.K4.Honest.matsOf
        { P := G.W.layers, hp := hp, g := g, link := seg, piece := k4.1.place.piece, r0 := k4.2, seg := seg })
        (tableAsks G.W.layers.y G.W.layers.rd g) 0 = some xl)
    {hd : List Fmt.Drawn}
    (hf : funsOf G.W.layers.y
        (ptsOf { P := G.W.layers, hp := hp, g := g, link := seg, piece := k4.1.place.piece, r0 := k4.2, seg := seg }
          { cell := fun _ _ _ => 0, w := fun _ _ => 0, tokv := #[], look := k4LookOf G.W.layers.y.fo k3.2 } hd).fo
        (namedPts { P := G.W.layers, hp := hp, g := g, link := seg, piece := k4.1.place.piece, r0 := k4.2, seg := seg }
          (ptsOf { P := G.W.layers, hp := hp, g := g, link := seg, piece := k4.1.place.piece, r0 := k4.2, seg := seg }
            { cell := fun _ _ _ => 0, w := fun _ _ => 0, tokv := #[], look := k4LookOf G.W.layers.y.fo k3.2 } hd))
        xl.2.1 = some funs)
    (hpf : partsFit (sizesOf hp.tl.mats) (OnBytes.HonestTrace.U3.partsOf funs) xl.2.2 = .ok ()) :
    V.vec hd = .ok fun C => First.K8.Honest.readAt (parOfMats hp.tl.mats) funs.toList
      (cellsAtOf C (matsOwn G.W seg)) := by
  unfold layersVals at hV
  obtain ⟨hp₁, hA₁, hV⟩ := okBind hV
  obtain rfl : hp = hp₁ := Option.some.inj (hA.symm.trans (someHave hA₁))
  obtain ⟨k4₁, e4, hV⟩ := okBind hV
  obtain rfl : k4 = k4₁ := Except.ok.inj (h4.symm.trans e4)
  obtain ⟨k3₁, e3, hV⟩ := okBind hV
  obtain rfl : k3 = k3₁ := Except.ok.inj (h3.symm.trans e3)
  dsimp only at hV
  obtain ⟨_, -, hV⟩ := okBind hV
  obtain ⟨_, -, hV⟩ := okBind hV
  obtain ⟨_, -, hV⟩ := okBind hV
  obtain ⟨_, -, hV⟩ := okBind hV
  obtain ⟨x₁, hx₁, hV⟩ := okBind hV
  obtain rfl : xl = x₁ := Option.some.inj (hx.symm.trans (someHave hx₁))
  obtain ⟨_, -, hV⟩ := okBind hV
  obtain ⟨_, -, hV⟩ := okBind hV
  obtain rfl := Except.ok.inj hV
  dsimp only
  unfold OnBytes.HonestTrace.U3.layersAt
  rw [hf]
  dsimp only
  rw [hpf]
  rfl

/-! ## 3 Numbers and shapes -/

/-- On the written seats of "U3": at an even segment below 24 the seat stands behind the rows up to the reads' own row. -/
def laySeatsB (c : ℕ) : Bool :=
  (OnBytes.HonestTrace.U3.Fit.seatsW "U3").all fun s =>
    s.seg % 2 != 0 || decide (24 ≤ s.seg) ||
      decide (OnBytes.HonestTrace.U3.Fit.rowsBeforeW (14 * s.seg + c) ≤ s.heard)

set_option maxRecDepth 1000000 in
/-- The kernel's yes. -/
theorem laySeatsB_yes : laySeatsB 5 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: the test says no a row further on. -/
theorem laySeatsB_can_fail : laySeatsB 6 = false := by decide +kernel

/-- Where a row bears a name it stands in the row's list. -/
theorem start_lt (Q : K4Pub) : k4StartAt Q 6 < (OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g).length := by
  have hm : k4StartAt Q 6 ∈ OnBytes.Desc.First.K4.Honest.starts Q := by
    rw [ProofFile.Honest.K4.starts_eq]
    exact List.mem_map.2 ⟨6, by simp, rfl⟩
  unfold OnBytes.Desc.First.K4.Honest.starts OnBytes.Desc.First.K4.Honest.rowsNamed at hm
  obtain ⟨⟨a, i⟩, hx, e⟩ := List.mem_map.1 hm
  have h1 := (List.mem_filter.1 hx).1
  have h2 := (List.mem_zipIdx h1).2.1
  simp only at e
  omega

/-- nReads at an even segment below 24 is the plan's number of reads. -/
theorem nReads_lay {X : OnBytes.Model.Verify.Public} {g : ℕ} (hg : g < 12) {hp : HPlan2}
    (hG : X.G[g]? = some hp) : nReads X (2 * g) = hp.nU.getD 2 0 := by
  unfold nReads
  rw [if_neg (by omega), if_pos (by omega), show 2 * g / 2 = g by omega, hG]
  rfl

/-- What phiB reads of a heard record. -/
theorem phiB_same' {g g' : OnBytes.Model.Forest.Heard} (es : g.shape = g'.shape) (e0 : g.zb0 = g'.zb0)
    (e1 : g.zb1 = g'.zb1) (lm e : ℕ) :
    OnBytes.Model.Forest.phiB g lm e = OnBytes.Model.Forest.phiB g' lm e := by
  unfold OnBytes.Model.Forest.phiB OnBytes.Model.Forest.Heard.zb
  simp only [es, e0, e1]

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The seat of an even segment's "U3" stands behind the segment's K4 rounds. -/
theorem heard_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {g : ℕ} (hg : g < 12) {Ad : MsgAddr} {am : ℕ}
    (hPair : pairOf (u3Seats Zp G) Ad = some (2 * g, am)) :
    OnBytes.HonestTrace.U3.Fit.rowsBeforeW (14 * (2 * g) + 5) ≤ heardOf (u3Seats Zp G) Ad := by
  unfold pairOf at hPair
  obtain ⟨st, hst, e⟩ := Option.map_eq_some_iff.1 hPair
  have eS : st.seg = 2 * g := congrArg Prod.fst e
  have hm : st ∈ OnBytes.HonestTrace.U3.Fit.seatsW "U3" := by
    have q : st ∈ u3Seats Zp G := List.mem_of_find?_eq_some hst
    unfold u3Seats at q
    rwa [OnBytes.HonestTrace.U3.Fit.seats_at_head h hG] at q
  have w := List.all_eq_true.1
    (show (OnBytes.HonestTrace.U3.Fit.seatsW "U3").all _ = true from laySeatsB_yes) st hm
  rw [eS] at w
  unfold heardOf
  rw [hst]
  have h1 : ((2 * g) % 2 != 0) = false := by
    have : (2 * g) % 2 = 0 := by omega
    rw [this]
    rfl
  have h2 : decide (24 ≤ 2 * g) = false := decide_eq_false (by omega)
  rw [h1, h2] at w
  simpa using w

/-- **The site's shape is the layout's.** -/
theorem callsShape_eq (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {g : ℕ} (hg : g < 12) :
    ProofFile.Honest.K3.Law.AtThr.callsShape Zp g = G.W.layers.y.fo := by
  obtain ⟨s, hs, e1, e2, eS⟩ := ProofFile.Honest.K3.Law.AtThr.calls_site_found h g hg
  rw [eS]
  have hs' := hs
  unfold ProofFile.Honest.K3.lookSites at hs'
  obtain ⟨a, _, hsa⟩ := List.mem_filterMap.1 hs'
  obtain ⟨f1, hsh, f3, f4, _, _, _, _⟩ := ProofFile.Honest.K3.Law.site_facts _ _ a s hsa
  rw [← f3, ← f4, e1, e2] at f1
  have eW : G.W = P5J.At.X Zp := (IM.blank_ground hG).choose_spec.2.1
  have f1' : VerifiableInference.Desc.First.Look.placeAt G.W (2 * g) false = some s.p := by
    rw [eW]
    exact f1
  have q := OnBytes.HonestTrace.U3.Fit.shape_layers h hG hg s.p f1'
  exact Option.some.inj (hsh.symm.trans q)

end

/-! ## 4 The claim -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)

/-- **VecTie at a layers' reads, under the head.** wit is free: valsAt at a layers' segment does not read the cover. -/
theorem vecTie_layers {g : ℕ} (hg : g < 12) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {Ad : MsgAddr} {am : ℕ}
    (hPair : pairOf (u3Seats Zp G) Ad = some (2 * g, am)) {hp₀ : HPlan2} (hp : G.W.G[g]? = some hp₀)
    (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst) :
    VecTie (𝕋) Said (K1.noL (2 * g) false) wit Zp G (2 * g) (hp₀.nU.getD 2 0) Ad := by
  intro blk hb k s μ E ds y cols s' hT hd hS tl htl
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  have hl2 : 2 * g < 25 := by omega
  have i1 : K1.noL (2 * g) false = 14 * (2 * g) + 4 + 1 := by
    have : IM.k1Ix (2 * g) false = 3 := by
      show (if false = true then 5 else 3) + (if 2 * g = 24 then 1 else 0) = 3
      rw [if_neg (fun e => nomatch e), if_neg (by omega)]
    show 14 * (2 * g) + IM.k1Ix (2 * g) false + 2 = _
    omega
  obtain ⟨e, Xl, reads, he, hX, hu⟩ := K1.k01_flat_reads h.scope h.reads O (2 * g) hl2
  obtain ⟨m0, m1, fm, km, gm, -⟩ := (IM.ground_named h.scope h.reads O.pub O.blank).1 g hg
  obtain rfl : m0 = Xl := Option.some.inj (fm.symm.trans hX)
  have hU := IM.alone_underR hu
  obtain rfl : e = blk := Option.some.inj (he.symm.trans hb)
  have hq := VerifiableInference.Desc.First.K8.Honest.k1Quiet_layers hX km (by rw [gm]; exact hp)
  obtain ⟨own, hown, hmats, -, -, -, hfe⟩ := layers_record (L := 𝕋) hq hU hS htl
  -- what the reads leave
  have hDec : VerifiableInference.Desc.Keeps.Decides VerifiableInference.Desc.LinkJoin.SameOwn
      (IM.k1Reads Zp Bs.G₀ (2 * g) m0 (IM.k1Ix (2 * g) false + 1) reads) := by
    unfold IM.k1Reads
    simp only [hq]
    exact VerifiableInference.Desc.LinkJoin.andThen_sameOwn _ _ _
      (VerifiableInference.Desc.LinkJoin.k1Later_sameOwn _ _ _ _ _ _)
      (VerifiableInference.Desc.LinkJoin.quietLayers_sameOwn _)
  have hS' := hS
  unfold Thread.Stepped at hS'
  obtain ⟨-, -, hdec, -⟩ := Block.step_ok.1 (step_under hU hS'.2)
  have hsame : s'.own? = s.own? := hDec _ _ _ _ hdec
  -- K4's member, from the thread's fold
  obtain ⟨Lk, b, x₄, e1, e2, -, e4, xl, xg, xP, xG, -, -⟩ := IM.k4_of h.scope h.reads O g hg
  obtain rfl : hp₀ = x₄.2.hp := Option.some.inj (hp.symm.trans xG)
  have hf4 : cF.blocksInOrder[14 * (2 * g) + 4]? = some b := by
    have q' := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope h.scope h.reads O (by omega : 2 * g ≤ 24) 2] at q'
    exact q'
  have hM := hT.1.2.2.2.2.1
  rw [i1] at hM
  unfold Thread.Made at hM
  obtain ⟨hseen, -, -, -, s₀, cols₀, -, -, hf⟩ := hM
  have hf' : foldBlocks 0 (cF.blocksInOrder.take (14 * (2 * g) + 4 + 1)) s₀ μ.seen cols₀ = .ok (s, [], []) := by
    have e0 : μ.seen.drop (𝕋).thread.front = μ.seen := List.drop_zero
    rw [e0] at hf
    exact hf
  obtain ⟨t₄, rs', c', n, hfront, hst⟩ := IM.fold_last hf4 hf'
  have hst' : b.step 0 t₄ (rs'.take b.rounds.length) c' = .ok (s, n) := hst
  have hd4 := ((VerifiableInference.Desc.Sound.step_ok_iff 0 b t₄ s _ c' n).1 hst').2.2.2
  obtain ⟨a, fo, o, G₄, ha, hfo, hh, ho, -, -, -, -⟩ :=
    OnBytes.Desc.First.K4.heard_reads ((IM.k4_yes e4 _ _ _ _).1 hd4).1
  obtain rfl : own = o := Option.some.inj (hown.symm.trans (hsame.trans ho))
  have hh' : OnBytes.Desc.First.K4.hear OnBytes.Desc.First.K4.engFl
      { x₄.2.P with tokv := t₄.tokv } x₄.2.hp x₄.2.g fo a.F _ = some (own, G₄, []) := hh
  rw [xP, xg] at hh'
  obtain ⟨-, -, iU3, tab, laid, nU3, TS', claimsP, pts, hd2', -, -, hlay, -, -, -, -, ehd2, hpts, hfuns⟩ :=
    OnBytes.Desc.First.K4.hear_public hh'
  have hz := VerifiableInference.OnPublicFiles.sized_upTo h.scope h.reads O h.laid.planOk (2 * g) (by omega) 1
    (by omega) (show foldBlocks 0 (cF.blocksInOrder.take (14 * (2 * g) + 1 + 2 + 1)) s₀ μ.seen cols₀ =
      .ok (t₄, rs', c') from hfront)
  obtain ⟨G₇, hG₇, hz₇⟩ := hz
  obtain rfl : a.F = G₇ := by
    have : t₄.fork? = some a.F := by
      unfold First.S.fork?
      rw [ha]
    exact Option.some.inj (this.symm.trans hG₇)
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, Ld⟩ :=
    OnBytes.Road.K4.own_ledG hz₇ hh'
  obtain rfl : hd2' = hd2 := Option.some.inj (ehd2.symm.trans Ld.eHd2)
  -- the numbers
  obtain ⟨k4, k3, hp', q4, q3, w4, w3, eG, -, -⟩ :=
    OnBytes.HonestTrace.U3.Fit.layersDeclared_at_head h hG hg
  obtain rfl : x₄.2.hp = hp' := Option.some.inj (hp.symm.trans eG)
  have er5 : roundsTo cF.blocksInOrder (14 * (2 * g) + 4) = k4.2 := by
    rw [OnBytes.HonestTrace.U3.Fit.roundsTo_at_head h, w4]
  have er3 : roundsTo cF.blocksInOrder (14 * (2 * g) + 3) = k3.2 := by
    rw [OnBytes.HonestTrace.U3.Fit.roundsTo_at_head h, w3]
  have er6 : roundsTo cF.blocksInOrder (14 * (2 * g) + 4 + 1) = k4.2 + b.rounds.length := by
    rw [← er5]
    unfold roundsTo
    rw [declsTo_succ hf4, List.length_append]
  have hlenH : μ.st.heard.length = k4.2 + b.rounds.length := by
    have q' := (𝕋).thread.heard_length hT.1.2.1
    rw [i1] at q'
    rw [q']
    show 0 + roundsTo cF.blocksInOrder _ = _
    rw [Nat.zero_add]
    exact er6
  have hHn : μ.st.heard.length ≤ heardOf (u3Seats Zp Bs.G₀) Ad := by
    have q' := heard_lay h hG hg hPair
    have e6 : OnBytes.HonestTrace.U3.Fit.rowsBeforeW (14 * (2 * g) + 5) = k4.2 + b.rounds.length := by
      rw [← er6]
      exact (OnBytes.HonestTrace.U3.Fit.roundsTo_at_head h _).symm
    omega
  have hcut : μ.st.heard.take (heardOf (u3Seats Zp Bs.G₀) Ad) = μ.st.heard := List.take_of_length_le hHn
  obtain ⟨err, hle⟩ := ProofFile.Honest.K3.Law.AtThr.fold_rest 0 _ _ _ _ _ _ _ hfront
  have eL4 : ((cF.blocksInOrder.take (14 * (2 * g) + 4)).flatMap (·.rounds)).length = k4.2 := er5
  rw [eL4] at err hle
  have hlenS : μ.seen.length = μ.st.heard.length := by
    rw [← hseen, List.length_map]
  have eRr : (rs'.take b.rounds.length).map (·.drawn) = μ.st.heard.drop k4.2 := by
    rw [err, List.map_take, List.map_drop, hseen, List.take_of_length_le]
    rw [List.length_drop]
    omega
  -- the tape
  have hD : DrawnIs (OnBytes.K.Kc.paired ((rs'.take b.rounds.length).map noDigest)
      (OnBytes.Desc.First.K4.entries Bs.G₀.W.layers x₄.2.hp g)) (μ.st.heard.drop k4.2) := by
    intro n' d hn
    rw [paired_drawn]
    have q' : ((rs'.take b.rounds.length).map (·.drawn))[n']? = some d := by
      rw [eRr]
      exact hn
    rw [List.getElem?_map] at q'
    obtain ⟨rr, hr, rfl⟩ := Option.map_eq_some_iff.1 q'
    rw [List.getElem?_map, hr]
    rfl
  -- the honest side
  let QQ : K4Pub :=
    { P := Bs.G₀.W.layers, hp := x₄.2.hp, g := g, link := 2 * g, piece := k4.1.place.piece, r0 := k4.2, seg := 2 * g }
  let ww : K4In :=
    { cell := fun _ _ _ => 0, w := fun _ _ => 0, tokv := #[], look := k4LookOf Bs.G₀.W.layers.y.fo k3.2 }
  have hfront' : foldBlocks 0 (cF.blocksInOrder.take (28 * g + 4)) s₀ μ.seen cols₀ = .ok (t₄, rs', c') := by
    rw [show 28 * g + 4 = 14 * (2 * g) + 4 by omega]
    exact hfront
  have Op := ProofFile.Honest.K3.Law.AtThr.layers_tie_head h g hg s₀ μ.st.input.x μ.seen cols₀ t₄ rs' c' a fo
    hfront' ha hfo
  have eL4' : ((cF.blocksInOrder.take (28 * g + 4)).flatMap (·.rounds)).length = k4.2 := by
    rw [show 28 * g + 4 = 14 * (2 * g) + 4 by omega]
    exact er5
  have eL3 : ((cF.blocksInOrder.take (28 * g + 3)).flatMap (·.rounds)).length = k3.2 := by
    rw [show 28 * g + 3 = 14 * (2 * g) + 3 by omega]
    exact er3
  have Op' : OpenSame fo (lookHeardAt Bs.G₀.W.layers.y.fo k3.2 (μ.st.heard.take k4.2)) := by
    rw [eL4', List.map_take, hseen] at Op
    unfold ProofFile.Honest.K3.Law.AtThr.lookOfK3 at Op
    rw [callsShape_eq h hG hg, eL3] at Op
    exact Op
  have hlook : ww.look (μ.st.heard.take k4.2) = k4LookOf Bs.G₀.W.layers.y.fo k3.2 (μ.st.heard.take k4.2) := rfl
  have hpub : OnBytes.Model.Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Bs.G₀.W := by
    rw [ProofFile.Law.blankBy_W O.blank]
    exact VerifiableInference.Desc.LinkJoin.public_of_pub O.pub
  obtain ⟨-, -, -, -, -, -, -, -, p9, p10⟩ := P1K8.layPremises Z _ (some Z.lay) Bs.G₀.W g x₄.2.hp
    h.scope h.reads hpub hg hp
  obtain ⟨-, -, pla, pT, -, -, -⟩ := OnBytes.HonestTrace.U3.Fit.layersNums_at_head h hG
  have hla : QQ.P.y.h.la ≠ 0 := by
    intro e0
    have : 2 ^ Bs.G₀.W.y.h.la = 65536 := pla
    have e1 : Bs.G₀.W.y.h.la = 0 := e0
    rw [e1] at this
    norm_num at this
  have hlt : QQ.P.y.h.lt ≠ 0 := by
    intro e0
    have q' : QQ.P.y.T = 2 ^ QQ.P.y.h.lt := p9
    have q2 : QQ.P.y.T = 1024 := pT
    rw [e0] at q'
    rw [q2] at q'
    norm_num at q'
  have hE : (QQ.g == 0) = true → own.H.ZE.size = QQ.P.y.h.la := by
    intro hg0
    obtain ⟨u1, hN, hTm⟩ := Ld.nt
    obtain ⟨a1, a2, -, -⟩ := OnBytes.Desc.First.K4.hearNorms_emb_tape hN hg0
    obtain ⟨-, -, k3e, -, -⟩ := OnBytes.Desc.First.K4.hearTerms_keeps hTm
    rw [k3e, a1, List.size_toArray, a2]
    exact p10.symm
  have hB : ∀ lm e', OnBytes.Model.Forest.phiB (ww.look (μ.st.heard.take k4.2)) lm e' =
      OnBytes.Model.Forest.phiB fo lm e' := fun lm e' =>
    phiB_same' Op'.shape.symm Op'.zb0.symm Op'.zb1.symm lm e'
  have hl6 : k4StartAt QQ 6 ≤ (μ.st.heard.drop k4.2).length := by
    have q' := start_lt QQ
    have el : b.rounds.length = (OnBytes.Desc.First.K4.rounds QQ.P QQ.hp QQ.g).length := by
      obtain ⟨b', hp'', hb', ehp, er, -, -⟩ := OnBytes.HonestTrace.U3.Fit.k4_block_at_head h hG hg
      obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hf4)
      obtain rfl : hp'' = x₄.2.hp := Option.some.inj (ehp.symm.trans hp)
      rw [er, List.length_map]
      exact List.length_map _
    rw [List.length_drop, hlenH]
    omega
  have hhl : (μ.st.heard.take k4.2).length = QQ.r0 := by
    rw [List.length_take]
    show min k4.2 _ = k4.2
    omega
  have hfun := ProofFile.Honest.K4.VT.funs_honest (Q := QQ) (w := ww) (h := μ.st.heard.take k4.2)
    (ds := μ.st.heard.drop k4.2) Ld hD hl6 hhl Op'.zx.symm hla hlt hE hB hpts hfuns
  rw [List.take_append_drop] at hfun
  -- the maker
  obtain ⟨V, hV, hVn, -⟩ := OnBytes.HonestTrace.U3.Fit.layersVals_at_head h hG hg
    (OnBytes.HonestTrace.U3.Fit.lookFits_layers h hG hg)
  obtain ⟨y₂, hl₂, hn₂, hc₂, -⟩ := OnBytes.HonestTrace.U3.Fit.layersLaid_at_head h hG hg hp
  have hM' : OnBytes.Desc.First.K4.Honest.matsOf QQ = sizesOf x₄.2.hp.tl.mats := by
    have hX' := IM.ground_publicK h.laid.pub hG
    exact (Meaning.P34.mats_of_public hX' g).trans (Meaning.P34.tails_of_public hX' hp).1.symm
  have hlay' : layTables (OnBytes.Desc.First.K4.Honest.matsOf QQ)
      (tableAsks Bs.G₀.W.layers.y Bs.G₀.W.layers.rd g) 0 = some (tab, laid, nU3) := hlay
  have hlay2 : layTables (sizesOf x₄.2.hp.tl.mats)
      (tableAsks Bs.G₀.W.layers.y Bs.G₀.W.layers.rd g) 0 = some (tab, laid, nU3) := by
    rw [← hM']
    exact hlay'
  have hn3 : nU3 = x₄.2.hp.nU.getD 2 0 := by
    have q' := Option.some.inj (hlay2.symm.trans hl₂)
    rw [← hn₂, ← q']
  -- as many weights as rows
  have hrch := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    (show 14 * (2 * g) + 4 + 1 ≤ cF.blocksInOrder.length from by
      have q' := (List.getElem?_eq_some_iff.1 hb).1
      rw [i1] at q'
      have q2 : 14 * (2 * g) + 4 + 1 < cF.blocksInOrder.length := q'
      omega)
    (by rw [← i1]; exact hT.1)
  have hr' : Johnson.Desc.First.Walk.Tied.Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g) + 6)
      (μ.st.input.x.pub, s') := by
    obtain ⟨hfit, -⟩ := Block.step_ok.1 hS.2
    have hb' : cF.blocksInOrder[14 * (2 * g) + 4 + 1]? = some e := by
      rw [← i1]
      exact hb
    exact Johnson.Desc.First.Walk.Tied.Reach.succ hrch hb'
      ⟨roundsOf y.1, cols, VerifiableInference.Desc.Sound.roundsFit_len _ _ hfit, hS.2⟩
  have hphi₀ := Johnson.AtFull.Shape.Phi.phi_sizes_lay h hg hr' htl
  rw [hfe] at hphi₀
  have hpf := partsFit_lay h hG hg hp (xl := (tab, laid, nU3)) hlay2 hfun hphi₀
  have hvec := layers_vec_returns (hd := μ.st.heard) hV hp q4 q3 hlay' hfun hpf
  refine ⟨V, fun C => First.K8.Honest.readAt (parOfMats x₄.2.hp.tl.mats) own.funs.toList
    (cellsAtOf C (matsOwn Bs.G₀.W (2 * g))), ?_, ?_, ?_, fun C j _ => ?_⟩
  · rw [OnBytes.HonestTrace.U3.Fit.valsAt_layers_at_head h hG hg]
    exact hV
  · rw [hcut]
    exact hvec
  · rw [hVn, ← hc₂, hn₂]
  · show First.K8.Honest.readAt (parOfMats x₄.2.hp.tl.mats) own.funs.toList _ j = _
    rw [hmats, hfe]

/-- **The same at nReads**, the plan drawn under the head. -/
theorem vecTie_layers_head {g : ℕ} (hg : g < 12) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {Ad : MsgAddr} {am : ℕ}
    (hPair : pairOf (u3Seats Zp G) Ad = some (2 * g, am))
    (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst) :
    VecTie (𝕋) Said (K1.noL (2 * g) false) wit Zp G (2 * g) (nReads (P5J.At.X Zp) (2 * g)) Ad := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  obtain ⟨-, -, x₄, -, -, -, -, -, -, -, xG, -, -⟩ := IM.k4_of h.scope h.reads O g hg
  have hW : Bs.G₀.W = P5J.At.X Zp := O.W
  have hGX : (P5J.At.X Zp).G[g]? = some x₄.2.hp := hW ▸ xG
  rw [nReads_lay hg hGX]
  exact vecTie_layers h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hg hG hPair xG wit

end

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.partsW_yes
#print axioms ProofFile.Honest.K1.partsW_can_fail
#print axioms ProofFile.Honest.K1.funsOf_parts
#print axioms ProofFile.Honest.K1.layers_written
#print axioms ProofFile.Honest.K1.partsFit_lay
#print axioms ProofFile.Honest.K1.layers_vec_returns
#print axioms ProofFile.Honest.K1.laySeatsB_yes
#print axioms ProofFile.Honest.K1.laySeatsB_can_fail
#print axioms ProofFile.Honest.K1.start_lt
#print axioms ProofFile.Honest.K1.heard_lay
#print axioms ProofFile.Honest.K1.callsShape_eq
#print axioms ProofFile.Honest.K1.nReads_lay
#print axioms ProofFile.Honest.K1.vecTie_layers
#print axioms ProofFile.Honest.K1.vecTie_layers_head
