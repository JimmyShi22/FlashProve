-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/VecAtLater.lean: AT A LAYERS' SEGMENT THE MAKER'S VECTOR RETURNS, FROM MADE AT ANY LATER BORDER. What
vecTie_layers says behind the reads' own member, said from the fold that the field Made holds: nothing else of Thr is spent.
What was heard is cut at the seat's own number, which is the segment's rows' end.

  fold_cut          a fold that returns returns over a shorter front
  layHeard, layHeard_yes, layHeard_can_fail   a test on the written seats: an even segment's seat stands just behind its rows
  lay_of_fold       the vector returns, from a fold over the segment's own rounds
  vec_lay_later     the same from Made at any later border, at a seat: the letters of vec_att_later

NO PROPERTY IS CLAIMED.
-/
import AtFullSide.K1.VecTieLay
import Johnson.Desc.ProofFile.Honest.K1.Law.AttVecAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block foldBlocks OpenedColumn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att (funBack tabsBack)
open VerifiableInference.Desc.First.Att.P (Pts Geo LookIn TablesP)
open VerifiableInference.Desc.Sound (MsgT roundsFit_len)
open VerifiableInference.Desc.K1 (joined_yes rounds_k1Reads)
open OnBytes.Model (HTailF2 HFun)
open OnBytes.Model.Layer (HPlan2 TableAsk TableAt layTables tableAsks funsOf phiOf)
open OnBytes.Model.Stages (LinkH)
open OnBytes.HonestTrace (pairOf heardOf)
open OnBytes.HonestTrace.U3 (u3Seats placeIn sizesOf SegVals valsAt layersVals covOf)
open OnBytes.HonestTrace.U3.Fit (rowsBeforeW)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In ptsOf namedPts)
open H2K5.Honest (PtsTo Pub5)
open OnBytes.HonestTrace.U3 (attVals)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K3 (lookHeardAt OpenSame)
open ProofFile.Honest.K4 (k4LookOf k4StartAt DrawnIs paired_drawn)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-- A test at written values: at an even segment below 24 the seat stands just behind the rows up to the reads' member, shifted by d. -/
def layHeard (d : ℕ) : Bool :=
  (OnBytes.HonestTrace.U3.Fit.seatsW "U3").all fun s =>
    s.seg % 2 != 0 || decide (24 ≤ s.seg) || (rowsBeforeW (14 * s.seg + 5 + d) == s.heard)

set_option maxRecDepth 1000000 in
/-- The kernel's yes. -/
theorem layHeard_yes : layHeard 0 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: a row further on the test says no. -/
theorem layHeard_can_fail : layHeard 1 = false := by decide +kernel

/-- A fold that returns returns over a shorter front. -/
theorem fold_cut {St Cl : Type} {ft : ℕ} {bs : List (Block St Cl)} {B b : ℕ} (hB : B ≤ b) {s₀ : St}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {out : St × List Fmt.RoundView × List OpenedColumn}
    (h : foldBlocks ft (bs.take b) s₀ rs cols = .ok out) :
    ∃ t r c, foldBlocks ft (bs.take B) s₀ rs cols = .ok (t, r, c) := by
  have e : bs.take b = bs.take B ++ (bs.take b).drop B := by
    conv_lhs => rw [← List.take_append_drop B (bs.take b)]
    rw [List.take_take, Nat.min_eq_left hB]
  rw [e] at h
  obtain ⟨t, r, c, h1, -⟩ := (VerifiableInference.Desc.foldBlocks_append_ok _ _ _ _ _ _).1 h
  exact ⟨t, r, c, h1⟩

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Layers: the maker's vector returns, from a fold over the segment's own rounds**, at what was heard up to these rounds' end. -/
theorem lay_of_fold (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (ξ : ProofFile.Inst) {s₀ t : TS} {seen rest : List Fmt.RoundView}
    {cols c : List OpenedColumn}
    (hf : foldBlocks 0 (cF.blocksInOrder.take (14 * (2 * g) + 4 + 1)) s₀ seen cols = .ok (t, rest, c))
    {cov : OnBytes.Model.Head.Covered} {V : SegVals} (hV : valsAt Zp G cov (2 * g) = .ok V) :
    ∃ v, V.vec ((seen.map (·.drawn)).take (rowsBeforeW (14 * (2 * g) + 5))) = .ok v := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  obtain ⟨Lk, b, x₄, e1, e2, -, e4, xl, xg, xP, xG, -, -⟩ := IM.k4_of h.scope h.reads O g hg
  have hp := xG
  have hf4 : cF.blocksInOrder[14 * (2 * g) + 4]? = some b := by
    have q' := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope h.scope h.reads O (by omega : 2 * g ≤ 24) 2] at q'
    exact q'
  obtain ⟨t₄, rs', c', n, hfront, hst⟩ := IM.fold_last hf4 hf
  have hst' : b.step 0 t₄ (rs'.take b.rounds.length) c' = .ok (t, n) := hst
  have hd4 := ((VerifiableInference.Desc.Sound.step_ok_iff 0 b t₄ t _ c' n).1 hst').2.2.2
  obtain ⟨a, fo, own, G₄, ha, hfo, hh, -, -, -, -, -⟩ :=
    OnBytes.Desc.First.K4.heard_reads ((IM.k4_yes e4 _ _ _ _).1 hd4).1
  have hh' : OnBytes.Desc.First.K4.hear OnBytes.Desc.First.K4.engFl
      { x₄.2.P with tokv := t₄.tokv } x₄.2.hp x₄.2.g fo a.F _ = some (own, G₄, []) := hh
  rw [xP, xg] at hh'
  obtain ⟨-, -, iU3, tab, laid, nU3, TS', claimsP, pts, hd2', -, -, hlay, -, -, -, -, ehd2, hpts, hfuns⟩ :=
    OnBytes.Desc.First.K4.hear_public hh'
  have hz := VerifiableInference.OnPublicFiles.sized_upTo h.scope h.reads O h.laid.planOk (2 * g) (by omega) 1
    (by omega) (show foldBlocks 0 (cF.blocksInOrder.take (14 * (2 * g) + 1 + 2 + 1)) s₀ seen cols =
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
  have hrow : rowsBeforeW (14 * (2 * g) + 5) = k4.2 + b.rounds.length := by
    rw [← er6]
    exact (OnBytes.HonestTrace.U3.Fit.roundsTo_at_head h _).symm
  obtain ⟨err, -⟩ := ProofFile.Honest.K3.Law.AtThr.fold_rest 0 _ _ _ _ _ _ _ hfront
  obtain ⟨-, hleA⟩ := ProofFile.Honest.K3.Law.AtThr.fold_rest 0 _ _ _ _ _ _ _ hf
  have eL4 : ((cF.blocksInOrder.take (14 * (2 * g) + 4)).flatMap (·.rounds)).length = k4.2 := er5
  have eL5 : ((cF.blocksInOrder.take (14 * (2 * g) + 4 + 1)).flatMap (·.rounds)).length = k4.2 + b.rounds.length := er6
  rw [eL4] at err
  rw [eL5] at hleA
  rw [hrow]
  -- what was heard, cut
  have hlenD : (seen.map (·.drawn)).length = seen.length := List.length_map _
  have eRr : (rs'.take b.rounds.length).map (·.drawn) =
      ((seen.map (·.drawn)).take (k4.2 + b.rounds.length)).drop k4.2 := by
    rw [err, List.map_take, List.map_drop, List.drop_take]
    congr 1
    omega
  have hD : DrawnIs (OnBytes.K.Kc.paired ((rs'.take b.rounds.length).map noDigest)
      (OnBytes.Desc.First.K4.entries Bs.G₀.W.layers x₄.2.hp g))
      (((seen.map (·.drawn)).take (k4.2 + b.rounds.length)).drop k4.2) := by
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
  have hfront' : foldBlocks 0 (cF.blocksInOrder.take (28 * g + 4)) s₀ seen cols = .ok (t₄, rs', c') := by
    rw [show 28 * g + 4 = 14 * (2 * g) + 4 by omega]
    exact hfront
  have Op := ProofFile.Honest.K3.Law.AtThr.layers_tie_head h g hg s₀ ξ seen cols t₄ rs' c' a fo hfront' ha hfo
  have eL4' : ((cF.blocksInOrder.take (28 * g + 4)).flatMap (·.rounds)).length = k4.2 := by
    rw [show 28 * g + 4 = 14 * (2 * g) + 4 by omega]
    exact er5
  have eL3 : ((cF.blocksInOrder.take (28 * g + 3)).flatMap (·.rounds)).length = k3.2 := by
    rw [show 28 * g + 3 = 14 * (2 * g) + 3 by omega]
    exact er3
  have eH₀ : ((seen.map (·.drawn)).take (k4.2 + b.rounds.length)).take k4.2 = (seen.take k4.2).map (·.drawn) := by
    rw [List.take_take, Nat.min_eq_left (by omega), List.map_take]
  have Op' : OpenSame fo (lookHeardAt Bs.G₀.W.layers.y.fo k3.2
      (((seen.map (·.drawn)).take (k4.2 + b.rounds.length)).take k4.2)) := by
    rw [eL4'] at Op
    unfold ProofFile.Honest.K3.Law.AtThr.lookOfK3 at Op
    rw [callsShape_eq h hG hg, eL3] at Op
    rw [eH₀]
    exact Op
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
  have hB : ∀ lm e', OnBytes.Model.Forest.phiB (ww.look (((seen.map (·.drawn)).take (k4.2 + b.rounds.length)).take k4.2)) lm e' =
      OnBytes.Model.Forest.phiB fo lm e' := fun lm e' =>
    phiB_same' Op'.shape.symm Op'.zb0.symm Op'.zb1.symm lm e'
  have hTake : ((seen.map (·.drawn)).take (k4.2 + b.rounds.length)).length = k4.2 + b.rounds.length := by
    rw [List.length_take, hlenD]
    omega
  have hl6 : k4StartAt QQ 6 ≤ (((seen.map (·.drawn)).take (k4.2 + b.rounds.length)).drop k4.2).length := by
    have q' := start_lt QQ
    have el : b.rounds.length = (OnBytes.Desc.First.K4.rounds QQ.P QQ.hp QQ.g).length := by
      obtain ⟨b', hp'', hb', ehp, er, -, -⟩ := OnBytes.HonestTrace.U3.Fit.k4_block_at_head h hG hg
      obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hf4)
      obtain rfl : hp'' = x₄.2.hp := Option.some.inj (ehp.symm.trans hp)
      rw [er, List.length_map]
      exact List.length_map _
    rw [List.length_drop, hTake]
    omega
  have hhl : (((seen.map (·.drawn)).take (k4.2 + b.rounds.length)).take k4.2).length = QQ.r0 := by
    rw [List.length_take, hTake]
    show min k4.2 _ = k4.2
    omega
  have hfun := ProofFile.Honest.K4.VT.funs_honest (Q := QQ) (w := ww)
    (h := ((seen.map (·.drawn)).take (k4.2 + b.rounds.length)).take k4.2)
    (ds := ((seen.map (·.drawn)).take (k4.2 + b.rounds.length)).drop k4.2) Ld hD hl6 hhl Op'.zx.symm hla hlt hE hB
    hpts hfuns
  rw [List.take_append_drop] at hfun
  -- the maker
  have hVl : layersVals Zp Bs.G₀ Johnson.AtFull.Desc.spotsWritten (2 * g) g = .ok V := by
    rw [← OnBytes.HonestTrace.U3.Fit.valsAt_layers_at_head h hG hg cov]
    exact hV
  have hM' : OnBytes.Desc.First.K4.Honest.matsOf QQ = sizesOf x₄.2.hp.tl.mats := by
    have hX' := IM.ground_publicK h.laid.pub hG
    exact (Meaning.P34.mats_of_public hX' g).trans (Meaning.P34.tails_of_public hX' hp).1.symm
  have hlay' : layTables (OnBytes.Desc.First.K4.Honest.matsOf QQ)
      (tableAsks Bs.G₀.W.layers.y Bs.G₀.W.layers.rd g) 0 = some (tab, laid, nU3) := hlay
  have hlay2 : layTables (sizesOf x₄.2.hp.tl.mats)
      (tableAsks Bs.G₀.W.layers.y Bs.G₀.W.layers.rd g) 0 = some (tab, laid, nU3) := by
    rw [← hM']
    exact hlay'
  -- as many weights as rows
  have z0 : (fo.zb 0).size = 5 + (fo.shape.kT + fo.shape.cK) := by
    show fo.zb0.size = _
    rw [Op'.zb0, Op'.shape]
    exact (zb_sizes _ _ _).1
  have z1 : (fo.zb 1).size = 5 + (fo.shape.kT + fo.shape.cK) := by
    show fo.zb1.size = _
    rw [Op'.zb1, Op'.shape]
    exact (zb_sizes _ _ _).2
  have hphi₀ := Johnson.AtFull.Shape.Phi.funsOf_sizes p9 p10.symm z0 z1 hlay' hfuns
  have hpf := partsFit_lay h hG hg hp (xl := (tab, laid, nU3)) hlay2 hfun hphi₀
  exact ⟨_, layers_vec_returns hVl hp q4 q3 hlay' hfun hpf⟩

end

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

set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)

/-- **Layers, from Made at any later border**, at a seat of the segment: the letters of vec_att_later. -/
theorem vec_lay_later {g : ℕ} (hg : g < 12) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {Ad : MsgAddr} {st : OnBytes.HonestTrace.Seat}
    (hst : OnBytes.HonestTrace.seatAt (u3Seats Zp G) Ad = some st) (hseg : st.seg = 2 * g) {B : ℕ}
    (hB : 14 * (2 * g) + 4 < B) {k : Coins Bk} {sB : TS} {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hM : (𝕋).thread.Made B k sB μ E) (cov : OnBytes.Model.Head.Covered) :
    ∀ V', valsAt Zp G cov st.seg = .ok V' → ∃ v, V'.vec (μ.st.heard.take st.heard) = .ok v := by
  intro V' hV
  rw [hseg] at hV
  unfold Thread.Made at hM
  obtain ⟨hseen, -, -, -, s₀, cols, -, -, hf⟩ := hM
  have e0 : μ.seen.drop (𝕋).thread.front = μ.seen := List.drop_zero
  rw [e0] at hf
  have hf₀ : foldBlocks 0 (cF.blocksInOrder.take B) s₀ μ.seen cols = _ := hf
  obtain ⟨t, rest, c, hf'⟩ := fold_cut (B := 14 * (2 * g) + 4 + 1) hB hf₀
  have hm : st ∈ OnBytes.HonestTrace.U3.Fit.seatsW "U3" := by
    have q : st ∈ u3Seats Zp G := List.mem_of_find?_eq_some hst
    unfold u3Seats at q
    rwa [OnBytes.HonestTrace.U3.Fit.seats_at_head h hG] at q
  have w' := List.all_eq_true.1
    (show (OnBytes.HonestTrace.U3.Fit.seatsW "U3").all _ = true from layHeard_yes) st hm
  rw [hseg] at w'
  have h1 : ((2 * g) % 2 != 0) = false := by
    have : (2 * g) % 2 = 0 := by omega
    rw [this]
    rfl
  have h2 : decide (24 ≤ 2 * g) = false := decide_eq_false (by omega)
  rw [h1, h2] at w'
  have e1 : rowsBeforeW (14 * (2 * g) + 5) = st.heard := by simpa using w'
  rw [← e1, ← hseen]
  exact lay_of_fold h hg hG μ.st.input.x hf' hV

end

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.fold_cut
#print axioms ProofFile.Honest.K1.lay_of_fold
#print axioms ProofFile.Honest.K1.layHeard_yes
#print axioms ProofFile.Honest.K1.layHeard_can_fail
#print axioms ProofFile.Honest.K1.vec_lay_later
