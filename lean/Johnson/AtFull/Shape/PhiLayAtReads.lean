-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/PhiLayAtReads.lean: BEHIND THE READS' MEMBER OF A LAYERS' LINK, AT EVERY STATE REACHED FROM THE CHAIN's OWN START,
EVERY TABLE OF THE SMALLNESS TEST'S LIST HAS AS MANY WEIGHTS AS ITS RUN HAS ROWS. Under the head. Raw Reach: no run on shapes and no
family J enters.

How. reads_lay_list: the list is the funs of the own rounds' return that the state holds. Three members back: the own rounds' yes
hands that return (heard_reads, hear_public: funsOf at the laid families); the lookup's yes hands what it heard (calls_here,
hearVia_heard: the lengths of zb0, zb1). layPremises: T = 2 ^ lt, la = ls + lt. funsOf_sizes (PhiLay.lean).

Limits. Lengths alone. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.PhiLay
import Johnson.Desc.K1.Law.LaterOne
import Johnson.P1K8R.OwnBetween
import Johnson.P1K8R.ListAtLayers
import Johnson.P1K8R.LayPremises
import Johnson.Desc.First.Link.Law.FitsMsBuilt
import Johnson.Desc.ProofFile.Honest.K3.Shape.HeardTop
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LaysAttHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteThereHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LayersTieHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Phi
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Decides)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open VerifiableInference.Desc.LinkJoin (SameOwn)
open ProofFile.Honest.K3.Law.AtThr (site_calls_head site_hub calls_here CallsHere)
open VerifiableInference.Desc.Sound.MgAt (borderOf)

theorem back {σ Cl P : Type} {ft : Nat} {bs : List (Block σ Cl)} {st : P → σ} {k : Nat}
    {z : P} {s' : σ} (h : Reach ft bs st (k + 1) (z, s')) :
    ∃ s b, Reach ft bs st k (z, s) ∧ bs[k]? = some b ∧ StepYes ft b s s' := by
  cases h with
  | succ h1 h2 h3 => exact ⟨_, _, h1, h2, h3⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- What the lookup heard has the two points' lengths. -/
theorem zb_of_hearVia {p : VerifiableInference.Desc.First.Look.P} {F G : Fork} {rs : List Fmt.RoundView}
    {H : Forest.Heard} (hS : OnBytes.PscRun.Sized F)
    (hv : VerifiableInference.Desc.K3.Law.hearVia p F rs = some (H, G)) :
    (H.zb 0).size = 5 + (H.shape.kT + H.shape.cK) ∧ (H.zb 1).size = 5 + (H.shape.kT + H.shape.cK) := by
  cases hs : p.shape with
  | none =>
    unfold VerifiableInference.Desc.K3.Law.hearVia at hv
    rw [hs] at hv
    cases hv
  | some h =>
    have e := ProofFile.Honest.K3.Shape.hearVia_heard hS hs hv
    have e0 : H.shape = h := congrArg VerifiableInference.Desc.First.Shape.HeardAll.shape e
    have z0 : H.zb0.size = _ := congrArg VerifiableInference.Desc.First.Shape.HeardAll.zb0 e
    have z1 : H.zb1.size = _ := congrArg VerifiableInference.Desc.First.Shape.HeardAll.zb1 e
    rw [e0]
    exact ⟨z0, z1⟩

/-- **BEHIND THE READS OF A LAYERS' LINK THE TABLES' WEIGHTS HAVE THEIR LENGTHS.** -/
theorem phi_sizes_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : Nat} (hg : g < 12)
    {z : ProofFile.InstPub} {s' : S} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g) + 6) (z, s'))
    {tl : HTailF2} (htl : s'.tl? = some tl) : ∀ Fn ∈ tl.funs.toList, Fn.phi.size = Fn.len := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hS := h.scope
  have hR := h.reads
  have hOk := h.laid.planOk
  obtain ⟨hp, tl', o, hG, etl, eo, c1, -, -⟩ := P1K8.reads_lay_list hS hR O hg hr
  obtain rfl : tl = tl' := Option.some.inj (htl.symm.trans etl)
  rw [c1]
  -- three members back
  obtain ⟨s₅, b₅, hr₅, hb₅, y₅⟩ := back (k := 14 * (2 * g) + 5) hr
  obtain ⟨s₄, b₄, hr₄, hb₄, y₄⟩ := back (k := 14 * (2 * g) + 4) hr₅
  obtain ⟨s₃, b₃, hr₃, hb₃, y₃⟩ := back (k := 14 * (2 * g) + 3) hr₄
  -- the reads leave what the own rounds returned
  have hown : SameOwn s₅ s' := by
    obtain ⟨b, eb, dec⟩ := P1K8.four_decide VerifiableInference.Desc.LinkJoin.sameOwn_stretch
      VerifiableInference.Desc.LinkJoin.quietLayers_sameOwn hS hR O hg 0 (by omega)
    obtain rfl : b₅ = b := Option.some.inj (hb₅.symm.trans eb)
    obtain ⟨rs, gs, hd⟩ := stepYes_decide y₅
    exact dec _ _ _ _ hd
  -- the own rounds
  obtain ⟨Lk, b, xx, e1, e2, -, e4, xl, xg, xP, xG, -, -⟩ := IM.k4_of hS hR O g hg
  have hf4 : cF.blocksInOrder[14 * (2 * g) + 4]? = some b := by
    have k := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope hS hR O (by omega : 2 * g ≤ 24) 2] at k
    exact k
  obtain rfl : b₄ = b := Option.some.inj (hb₄.symm.trans hf4)
  obtain ⟨rs4, gs4, hd4⟩ := stepYes_decide y₄
  obtain ⟨a, fo, o₄, G, ha, hfo, hh, ho, -, -, -, -⟩ :=
    OnBytes.Desc.First.K4.heard_reads ((IM.k4_yes e4 s₄ s₅ rs4 gs4).1 hd4).1
  obtain rfl : o₄ = o := by
    have e : s₅.own? = some o := by rw [← hown]; exact eo
    exact Option.some.inj (ho.symm.trans e)
  have hh' : OnBytes.Desc.First.K4.hear OnBytes.Desc.First.K4.engFl
      { xx.2.P with tokv := s₄.tokv } xx.2.hp xx.2.g fo a.F _ = some (o₄, G, []) := hh
  obtain ⟨-, -, iU3, tab, laid, nU3, TS, claimsP, pts, hd2, -, -, hlay, -, -, -, -, -, hpts, hfuns⟩ :=
    OnBytes.Desc.First.K4.hear_public hh'
  -- the lookup
  obtain ⟨st, hst, l1, l2, -, -⟩ := site_calls_head h (2 * g) (by omega)
  obtain ⟨Fd, Bs', base', A', B', lot, O', hlot, hbs, hm⟩ := site_hub h st hst (by rw [l1]; omega)
  have hb' : cF.blocksInOrder[borderOf st.link st.digits]? = some b₃ := by
    rw [l1, l2, ProofFile.Honest.K3.Law.AtThr.border_even g hg, show 28 * g + 3 = 14 * (2 * g) + 3 by omega]
    exact hb₃
  obtain ⟨m1, m2, m3⟩ := hm b₃ hb'
  obtain ⟨R₃, c₃, -, e₃⟩ := y₃
  obtain ⟨F, H, G₁, hF, -, hv, hC, -⟩ := calls_here _ _ _ _ Fd Zp Bs' base' _ A' B' O' st hst l2 lot b₃
    hlot hbs m1 m2 m3 0 s₃ s₄ _ R₃ c₃ e₃
  obtain ⟨-, Rr, Cc, hf0⟩ := hr₃.fold
  obtain ⟨G', hG', hz⟩ := VerifiableInference.OnPublicFiles.sized_upTo hS hR O hOk (2 * g) (by omega) 0
    (by omega) (show foldBlocks 0 (cF.blocksInOrder.take (14 * (2 * g) + 0 + 2 + 1)) (ProofFile.startS Zp z) Rr Cc =
      .ok (s₃, [], []) from hf0)
  obtain rfl : F = G' := Option.some.inj (hF.symm.trans hG')
  obtain ⟨z0, z1⟩ := zb_of_hearVia hz hv
  -- what the lookup heard is what the own rounds took
  have eH : fo = H := by
    rcases hC with ⟨q, hq, e⟩ | ⟨q, hq, e⟩ | ⟨q, hq, _, e⟩
    · rw [e] at ha
      cases ha
      exact (Option.some.inj (show some H = some fo from hfo)).symm
    · rw [e] at ha
      cases ha
    · rw [e] at ha
      cases ha
  subst eH
  -- public numbers
  have hpub : Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Bs.G₀.W := by
    rw [ProofFile.Law.blankBy_W O.blank]
    exact VerifiableInference.Desc.LinkJoin.public_of_pub O.pub
  obtain ⟨-, -, -, -, -, -, -, -, p9, p10⟩ := P1K8.layPremises Z _ (some Z.lay) Bs.G₀.W g xx.2.hp hS hR hpub hg xG
  have hfuns' : Layer.funsOf Bs.G₀.W.layers.y fo pts laid = some o₄.funs := by
    rw [← xP]
    exact hfuns
  have hlay' : Layer.layTables ((xx.2.P.tails.getD xx.2.g {}).mats.map fun M => (M.m, M.k))
      (Layer.tableAsks Bs.G₀.W.layers.y xx.2.P.rd xx.2.g) 0 = some (tab, laid, nU3) := by
    rw [← xP]
    exact hlay
  exact funsOf_sizes p9 p10.symm z0 z1 hlay' hfuns'

/-- The same in the number of K1's member: at an even link below the head. -/
theorem phi_sizes_at_reads_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 24)
    (he : l % 2 = 0) {z : ProofFile.InstPub} {s' : S}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (VerifiableInference.Desc.K1.noL l false + 1) (z, s'))
    {tl : HTailF2} (htl : s'.tl? = some tl) : ∀ Fn ∈ tl.funs.toList, Fn.phi.size = Fn.len := by
  obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by omega⟩
  have e : VerifiableInference.Desc.K1.noL (2 * g) false + 1 = 14 * (2 * g) + 6 := by
    have n : ¬ 2 * g = 24 := by omega
    simp [VerifiableInference.Desc.K1.noL, IM.k1Ix, n]
  rw [e] at hr
  exact phi_sizes_lay h (by omega) hr htl

end Johnson.AtFull.Shape.Phi

#print axioms Johnson.AtFull.Shape.Phi.phi_sizes_at_reads_lay
#print axioms Johnson.AtFull.Shape.Phi.back
#print axioms Johnson.AtFull.Shape.Phi.zb_of_hearVia
#print axioms Johnson.AtFull.Shape.Phi.phi_sizes_lay
