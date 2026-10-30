-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/PhiHead.lean: BEHIND THE READS' MEMBER OF THE HEAD's LINK, AT EVERY STATE REACHED FROM THE CHAIN's OWN START, EVERY
TABLE OF THE SMALLNESS TEST'S LIST HAS AS MANY WEIGHTS AS ITS RUN HAS ROWS. Under the head. Raw Reach: no run on shapes, no family J.

How. headList_at_343: the list is the tables that the text makes of what the state holds as heard. The reads keep what was heard
(kept_by_reads). The head's own yes hands the sizes of the heard points (heard_sizes) and the lookup's key points (given_ok); the
lookup's yes the two points on the planes (calls_heard_site, hearVia_heard). lens_of_tables.

Limits. Lengths alone. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.PhiLayAtReads
import Johnson.P1K8R.ReadsLiveAlongFold
import Johnson.P1K8R.ZlSizeAtStep
import Johnson.P4R.FreeAt341N
import Johnson.Desc.Reads.HeardSizes
import Johnson.Desc.Reads.LensAt
import Johnson.Desc.Reads.RunIsAtBorder
import Johnson.Desc.Reads.RunIsAt
import Johnson.Road.K4.K4DeclsJoin
import Johnson.Goal.Meaning.HeadNumsScope
import Johnson.Goal.Meaning.HeadColsScope
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CallsHeardLink
import Johnson.P4R.Back341N
import Johnson.Desc.Kinds.Law.K6WayUpAtSeat
import Johnson.Desc.Kinds.Law.HeadLedgerMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Phi
open OnBytes OnBytes.Model
open OnBytes.Model.Head (HL)
open VerifiableInference.Desc (Block Chain OpenedColumn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Reads (last_size size_of_tail)
open VerifiableInference.Reads.AtSeat (Kept decideBy_more heard_sizes laid_by_hearing zt_at lens_of_tables)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open ProofFile.Honest.K3.Law.AtThr (site_calls_head calls_heard_site)
open VerifiableInference.Desc.Sound.MgAt (borderOf)

/-- **What the head's own yes says of what is held as heard.** -/
theorem sizes_of_decide {sh : OnBytes.Model.Head.Shape} {iU3 work : Nat} {rounds : Given → List Round}
    {weights : Given → Behind → SumOnMatrix} {L : HL} {s0 s2 : S} {rs : List Fmt.RoundView}
    (h4 : decideBy rounds (fun _ => Head.hear) weights (parOf sh work) (seatAt sh iU3) s0 rs = .ok s2)
    (hWL : WellLaid ((seatAt sh iU3).ledger s0))
    (hJ : ∀ q, q < 6 → (L.calls.getD q default).lJ =
      (letI := Head.sizesOf sh; lJ (OnBytes.Model.Head.keyFloor sh) (callKeys q)))
    (hls : ∀ q, q < 6 → sh.ls ≤ (L.calls.getD q default).lJ) :
    ∃ o x g, s2.here = .head o ∧ o.x = some x ∧ x.g1 = g ∧ s0.lookHeard? = some g ∧
      x.Zl.size = sh.ls + sh.lt ∧ x.qH = 0 ∧ x.PV.size = sh.lt ∧ x.tV.r.size = sh.lt ∧
      x.tH.r.size = sh.lt ∧ ∀ q, q < 6 → (OnBytes.Model.Head.ztOf sh L g q).size = sh.lt := by
  obtain ⟨g0, H, F, left, s1, s2', hg, hh, e1, e2, hs2⟩ := decideBy_more h4
  have hs2' : s2 = s2' := hs2
  subst hs2'
  obtain ⟨z, y, hz1, -, hP, hgE⟩ := Came.given_ok _ _ _ _ hg
  subst hgE
  obtain ⟨g, hg0, rfl⟩ : ∃ g, s0.lookHeard? = some g ∧ z = (g.zx, fun c => g.zk.getD c #[]) := by
    have e : (s0.lookHeard?.map fun G => (G.zx, fun c => G.zk.getD c #[])) = some z := hz1
    obtain ⟨g, a, b⟩ := Option.map_eq_some_iff.1 e
    exact ⟨g, a, b.symm⟩
  have hz : sh.ls + sh.lt ≤ g.zx.size := by
    obtain ⟨p1, p2⟩ := hP 0 _ (Came.call_get (by decide))
    exact size_of_tail _ _ (J := (L.calls.getD 0 default).lJ) (by rw [hJ 0 (by decide)]; exact p1)
      p2 (hls 0 (by decide))
  have hzt : (@fromLookup (Head.sizesOf sh) (OnBytes.Model.Head.keyFloor sh) g.zx
      fun c => g.zk.getD c #[]).norm.zt.size = sh.lt :=
    last_size g.zx (n := sh.lt) (Nat.le_trans (Nat.le_add_left _ _) hz)
  obtain ⟨a1, -, a3, a4⟩ := @heard_sizes (Head.sizesOf sh) (parOf sh work).policy (requestOf s0)
    ⟨y⟩ (@fromLookup (Head.sizesOf sh) (OnBytes.Model.Head.keyFloor sh) g.zx
      fun c => g.zk.getD c #[]).norm _ _ _ _ _ hWL hh hzt
  obtain ⟨o2, x2, q2, hx2, hG2, hZl, hqH, -, p1, -, p3, p4⟩ := laid_by_hearing sh iU3 e2
  have hl1 : s1.lookHeard? = some g := by
    have e1' : s1 = s0.putFork F := putFork?_ok e1
    rw [e1', VerifiableInference.Desc.First.S.look_putFork]
    exact hg0
  obtain ⟨o1, G, ho1, hG, e⟩ := setHeard_form sh iU3 e2
  have hGg : G = g := by
    unfold VerifiableInference.Desc.First.S.lookHeard? at hl1
    rw [ho1] at hl1
    by_cases hop : o1.opened = true
    · have k : o1.lookHeard = some g := by
        have k0 : (if o1.opened = true then o1.lookHeard else none) = some g := hl1
        rw [if_pos hop] at k0
        exact k0
      exact Option.some.inj (hG.symm.trans k)
    · have k0 : (if o1.opened = true then o1.lookHeard else none) = some g := hl1
      rw [if_neg hop] at k0
      cases k0
  have hxg : x2.g1 = g := by
    subst hGg
    rw [e] at q2
    have q3 := VerifiableInference.Desc.First.Here.head.inj q2
    subst q3
    have q4 := Option.some.inj hx2
    rw [← q4]
    rfl
  refine ⟨o2, x2, g, q2, hx2, hxg, hg0, ?_, hqH, by rw [p1]; exact a1, by rw [p3]; exact a3,
    by rw [p4]; exact a4, fun q hq => ?_⟩
  · rw [hZl, hxg]
    exact last_size _ hz
  · rw [zt_at sh L g _ hP hq (hJ q hq) (hls q hq) hz]
    exact hzt

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **At a state reached in front of the lookup on the calls at the head's link the ledger has its sizes.** -/
theorem sized_340 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 340 (z, s)) :
    ∃ F, s.fork? = some F ∧ OnBytes.PscRun.Sized F := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hS := h.scope
  have hR := h.reads
  obtain ⟨s339, b2, h339, e2, y2⟩ := P4.reach_last hr
  obtain ⟨s338, b1, h338, e1, y1⟩ := P4.reach_last h339
  obtain ⟨L1, c1, l1, l2, -, -, hyes, -⟩ := P4.k7_left_seat hS hR O
  have f1 : cF.blocksInOrder[338]? = some c1 := by
    have q := IM.hear_at_flat l1 l2
    rwa [IM.flatIx_scope hS hR O (by decide) 0] at q
  obtain rfl : b1 = c1 := Option.some.inj (e1.symm.trans f1)
  obtain ⟨r1, g1, d1⟩ := P4.step_yes y1
  obtain ⟨r1', g1', a1⟩ := hyes _ _ _ _ d1
  obtain ⟨ha, hhead⟩ := P4.head_behind_338 Bs.G₀.W a1
  obtain ⟨L2, c2, xx, m1, m2, -, hla2, hK⟩ := IM.k2_head_of hS hR O
  have f2 : cF.blocksInOrder[339]? = some c2 := by
    have q := IM.hear_at_flat m1 m2
    rwa [IM.flatIx_scope hS hR O (by decide) 1] at q
  obtain rfl : b2 = c2 := Option.some.inj (e2.symm.trans f2)
  obtain ⟨r2, g2, d2⟩ := P4.step_yes y2
  have a2 : xx.decide s339 r2 g2 = .ok s :=
    ((IM.yes_alone hla2 (by decide) s339 s r2 g2).1 d2).1
  rcases hK with ⟨-, hm⟩ | ⟨Pp, n, -, -, hd⟩
  · obtain ⟨e, he⟩ := hm s339 r2 g2
    rw [he] at a2
    cases a2
  · rcases hd with ⟨hn, -⟩ | ⟨l, HP, -, -, hx⟩ | ⟨l, -, hx⟩
    · cases hn
    · rw [hx] at a2
      obtain ⟨G, hG, hs, -, -⟩ := placeH2_free a2
      exact ⟨G, hG, hs⟩
    · rw [hx] at a2
      have hb := VerifiableInference.Desc.First.K2.between_of_link (snd := _root_.Tw.K2.sendByL8) a2 rfl
      rw [hhead] at hb
      cases hb

/-- **BEHIND THE READS OF THE HEAD's LINK THE TABLES' WEIGHTS HAVE THEIR LENGTHS.** -/
theorem phi_sizes_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {z : ProofFile.InstPub} {s' : S} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 343 (z, s'))
    {tl : HTailF2} (htl : s'.tl? = some tl) : ∀ Fn ∈ tl.funs.toList, Fn.phi.size = Fn.len := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hS := h.scope
  have hR := h.reads
  have hOk := h.laid.planOk
  obtain ⟨xh, t, ⟨a, ha, hx⟩, ⟨cov, ht⟩, tl', etl, -, efuns, -, -⟩ :=
    P1K8.headList_at_343 _ _ _ _ _ _ _ _ _ _ hS hR O _ _ _ _ hr
  obtain rfl : tl = tl' := Option.some.inj (htl.symm.trans etl)
  rw [efuns]
  -- three members back
  obtain ⟨s₂, b₂, hr₂, hb₂, y₂⟩ := back (k := 342) hr
  obtain ⟨s₁, b₁, hr₁, hb₁, y₁⟩ := back (k := 341) hr₂
  obtain ⟨s₀, b₀, hr₀, hb₀, y₀⟩ := back (k := 340) hr₁
  -- public numbers
  have hpub : Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Bs.G₀.W := by
    rw [ProofFile.Law.blankBy_W O.blank]
    exact VerifiableInference.Desc.LinkJoin.public_of_pub O.pub
  obtain ⟨six, floor, -⟩ := InScope.nums_in_scope hS hR hpub
  have hJ := InScope.cols_in_scope hS hR hpub
  have hls := VerifiableInference.Reads.AtSeat.hlsJ_of_floor hJ floor
  -- the reads keep what was heard
  obtain ⟨bk, hbk, Dk⟩ := P1K8.member_342_of _ _ _ _ _ _ _ _ _ _ hS hR O Kept
    (fun Xl pr reads eX h2 s rs gs t hd => P1K8.kept_by_reads Zp Bs.G₀ 24 Xl pr reads eX h2 s rs gs t hd)
  obtain rfl : b₂ = bk := Option.some.inj (hb₂.symm.trans hbk)
  obtain ⟨rs2, gs2, hd2⟩ := stepYes_decide y₂
  have kp := Dk s₂ rs2 gs2 s' hd2
  -- the head's own rounds
  have eW : Bs.G₀.W = Zp.p.X := O.W
  obtain ⟨blk, hbl, M⟩ := P4.k6_member_at_mg h.toAtMg
  obtain rfl : b₁ = blk := Option.some.inj (hb₁.symm.trans hbl)
  obtain ⟨rs1, gs1, hd1⟩ := stepYes_decide y₁
  have hW := P4.wellLaid_341 hS hR O (P4.plan_at O hOk 340) hr₁ (P5J.At.X Zp).hS (Head.Law.readsOf (P5J.At.X Zp))
  have hJ' : ∀ q, q < 6 → ((P5J.At.X Zp).HLy.calls.getD q default).lJ =
      (letI := Head.sizesOf (P5J.At.X Zp).hS; lJ (OnBytes.Model.Head.keyFloor (P5J.At.X Zp).hS) (callKeys q)) := by
    have e : P5J.At.X Zp = Bs.G₀.W := eW.symm
    rw [e]
    exact hJ
  have hls' : ∀ q, q < 6 → (P5J.At.X Zp).hS.ls ≤ ((P5J.At.X Zp).HLy.calls.getD q default).lJ := by
    have e : P5J.At.X Zp = Bs.G₀.W := eW.symm
    rw [e]
    exact hls
  obtain ⟨o, x₂, g, ho, hx₂, hg1, hlook, hZl, hqH, hPV, hTV, hTH, hzt⟩ :=
    sizes_of_decide (L := (P5J.At.X Zp).HLy) (weights := fun _ _ => forTheMerge) (M.decide_down hd1).1 hW hJ' hls'
  obtain ⟨o', ho', ex', -⟩ := kp o ho
  obtain rfl : a = o' := VerifiableInference.Desc.First.Here.head.inj (ha.symm.trans ho')
  obtain rfl : xh = x₂ := Option.some.inj (hx.symm.trans (ex'.trans hx₂))
  -- the lookup's two points
  obtain ⟨st, hst, l1, l2, -, -⟩ := site_calls_head h 24 (by omega)
  have hb' : cF.blocksInOrder[borderOf st.link false]? = some b₀ := by
    rw [l1]
    exact hb₀
  obtain ⟨R₀, c₀, -, e₀⟩ := y₀
  obtain ⟨F, g', G, hF, hv, hg', -⟩ := calls_heard_site h st hst (by omega) l2 b₀ hb' 0 s₀ s₁ _ R₀ c₀ e₀
  obtain ⟨Fz, hFz, hz⟩ := sized_340 h hr₀
  obtain rfl : F = Fz := Option.some.inj (hF.symm.trans hFz)
  obtain ⟨z0, z1⟩ := zb_of_hearVia hz hv
  obtain rfl : g' = g := Option.some.inj (hg'.symm.trans hlook)
  -- the test on lengths
  have ht' : VerifiableInference.Desc.K8.ReadsQuiet.tables (P5J.At.X Zp).hS (P5J.At.X Zp).HLy
      (P5J.At.X Zp).H cov xh = .ok t := by
    have e : P5J.At.X Zp = Bs.G₀.W := eW.symm
    rw [e]
    exact ht
  have six' : (P5J.At.X Zp).HLy.calls.size ≤ 6 := by
    have e : P5J.At.X Zp = Bs.G₀.W := eW.symm
    rw [e]
    exact six
  have hc6 := VerifiableInference.Reads.AtSeat.hc6_of_size six'
  have y0 : xh.g1.zb0.size = xh.g1.shape.kT + xh.g1.shape.cK + 5 := by
    rw [hg1]
    have e : (g'.zb 0).size = g'.zb0.size := rfl
    rw [← e, z0]
    omega
  have y1 : xh.g1.zb1.size = xh.g1.shape.kT + xh.g1.shape.cK + 5 := by
    rw [hg1]
    have e : (g'.zb 1).size = g'.zb1.size := rfl
    rw [← e, z1]
    omega
  obtain ⟨lb, ub⟩ := lens_of_tables ht' hZl
    (fun q hq => by rw [hg1]; exact hzt q (hc6 _ _ hq))
    (fun q hq => by rw [hg1]; exact hzt q (hc6 _ _ hq))
    (by rw [hqH, hg1]; exact hzt 0 (by decide)) hPV hTV
    (VerifiableInference.Reads.AtSeat.tN_size ht') hTH y0 y1
  refine OnBytes.Road.K4.hsz_of_lens (fun Fn hF => ?_) lb
  unfold VerifiableInference.Reads.allU3B at ub
  exact beq_iff_eq.1 (List.all_eq_true.1 ub Fn hF)

/-- The same in the number of K1's member. -/
theorem phi_sizes_at_reads_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {z : ProofFile.InstPub} {s' : S}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (VerifiableInference.Desc.K1.noL 24 false + 1) (z, s'))
    {tl : HTailF2} (htl : s'.tl? = some tl) : ∀ Fn ∈ tl.funs.toList, Fn.phi.size = Fn.len := by
  have e : VerifiableInference.Desc.K1.noL 24 false + 1 = 343 := by decide
  rw [e] at hr
  exact phi_sizes_head h hr htl

end Johnson.AtFull.Shape.Phi

#print axioms Johnson.AtFull.Shape.Phi.phi_sizes_at_reads_head
#print axioms Johnson.AtFull.Shape.Phi.sizes_of_decide
#print axioms Johnson.AtFull.Shape.Phi.sized_340
#print axioms Johnson.AtFull.Shape.Phi.phi_sizes_head
