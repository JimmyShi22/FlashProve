-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/TieStateAtHead.lean: TieStateP (TiePlanShare.lean) AT THE HEAD, AT THE READS OF EACH SORT OF SEGMENT, at the count nReads: hSt of
exchangeAtS_tie_base (AtFullSide/K1/TieAtBase.lean). Under the head and hSaid.

  ownHeardS_head          OwnHeardS at a layers' segment: k4_own_at_reads at the border in front; the reads keep own?
  tieStateP_layers_head   at segment 2 g
  attTlS_head             AttTlS at an attention's segment: tlIsPlan_at_reads at the promise's stand
  tieStateP_att_head · tieStateP_out_head · tieStateP_all_head   attention · the output head · all 25

k4_own_at_reads binds its tape and its ledger under "there are": OwnHeardS asks no more: its caller spends what holds of every return
of hearFl (tablesLie_hear).

NO PROPERTY IS CLAIMED.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TieStatePlan
import Johnson.Desc.ProofFile.Honest.K1.Law.TieStateAttPlan
import Johnson.Desc.ProofFile.Honest.K1.Law.TieStateHeadPlan
import Johnson.Desc.ProofFile.Honest.K1.Law.ShapesAtHead
import Johnson.Desc.ProofFile.Honest.K1.Law.K4HeardAtReads
import Johnson.Desc.ProofFile.Honest.K1.Law.FrontAtReads
import Johnson.Desc.K8.Honest.ReadsSeat
import Johnson.HonestTrace.U3Fit.LayersLaid
import Johnson.HonestTrace.U3Fit.Slice
import Johnson.Meaning.ReadsPublic
import Johnson.Meaning.ReadsPlan
import Johnson.Desc.AtSeats.TlAtRch
import Johnson.Desc.ProofFile.Honest.K5.Law.AttValsAtHead
import Johnson.Desc.ProofFile.Honest.K1.Twin.FirstSeatedAtLinkNoB
import Johnson.IMR.K5Seat
import Johnson.Goal.Meaning.HidPlanNM
import Johnson.Road.FormsKeysPlan
import AtFullSide.K1.ReadsCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT mgAll mgBase)
open OnBytes.HonestTrace (Sz ShapesFit SameSizes)
open OnBytes.Model.Layer (HPlan2)
open ProofFile.Honest.FirstThread
open OnBytes.Maker (WholeD)
open OnBytes.Slice (frS)
open P5J (AtMgA CellsM TS F0T)
open Johnson.Desc.First.Walk.Tied (rchAt_raw)
open VerifiableInference.Desc.LinkJoin (SameOwn andThen_sameOwn k1Later_sameOwn quietLayers_sameOwn)
open VerifiableInference.Desc.First.K8.Honest (k1Quiet_layers)

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
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
include hSaid

/-- **OwnHeardS at a layers' segment.** -/
theorem ownHeardS_head {Bs : ProofFile.PureBase} {base₀ : List (Block TS ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
    {g : ℕ} (hg : g < 12) {hp : HPlan2} (hG : Bs.G₀.W.G[g]? = some hp)
    {Xl : OnBytes.Model.Stages.LinkH} {pr : ℕ} {reads : Option (List ℕ)} (hX : Bs.G₀.built[2 * g]? = some Xl)
    (hk : Xl.kind = 0) (hgg : Xl.g = g)
    {blk₁ : Block TS ProofFile.Cl}
    (hU : blk₁.UnderR ((IM.k1Reads Zp Bs.G₀ (2 * g) Xl pr reads).retype : Block TS ProofFile.Cl))
    (hblk : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).bs[K1.noL (2 * g) false]? = some blk₁) :
    OwnHeardS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said (K1.noL (2 * g) false) g hp := by
  intro blk hb k s μ E ds y cols s' hT hd hS o ho
  obtain rfl : blk₁ = blk := Option.some.inj (hblk.symm.trans hb)
  have hT' : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      (K1.noL (2 * g) false) k s μ E := ⟨hT.1, hSaid _ _ _ hT.2⟩
  have hbl : K1.noL (2 * g) false ≤ cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hb).1.le
  have hn24 : ¬ 2 * g = 24 := by omega
  have i1 : K1.noL (2 * g) false = 28 * g + 5 := by
    have : IM.k1Ix (2 * g) false = 3 := by
      show (if false = true then 5 else 3) + (if 2 * g = 24 then 1 else 0) = 3
      rw [if_neg (fun e => nomatch e), if_neg hn24]
    show 14 * (2 * g) + IM.k1Ix (2 * g) false + 2 = _
    omega
  have hr := rchAt_raw (thrS_rchAt h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (0 : ℕ) hbl hT')
  rw [i1] at hr
  obtain ⟨x₄, tokv, fo, F₄, o', G, t, u, -, xg, xP, xG, hh, ho'⟩ :=
    VerifiableInference.Desc.LinkJoin.k4_own_at_reads h.scope h.reads O hg hr
  have hDec : VerifiableInference.Desc.Keeps.Decides SameOwn (IM.k1Reads Zp Bs.G₀ (2 * g) Xl pr reads) := by
    have hq : IM.k1Quiet Bs.G₀ (2 * g) Xl = K8.ReadsQuiet.layers ⟨⟨1, some (2 * g), 4, .K1⟩, hp.tl⟩ :=
      k1Quiet_layers hX hk (by rw [hgg]; exact hG)
    unfold IM.k1Reads
    simp only [hq]
    exact andThen_sameOwn _ _ _ (k1Later_sameOwn _ _ _ _ _ _) (quietLayers_sameOwn _)
  have hS' := hS
  unfold Thread.Stepped at hS'
  obtain ⟨-, -, hdec, -⟩ := Block.step_ok.1 (step_under hU hS'.2)
  have hsame : s'.own? = s.own? := hDec _ _ _ _ hdec
  have eo : o' = o := Option.some.inj (ho'.symm.trans (hsame.symm.trans ho))
  subst eo
  obtain rfl : hp = x₄.2.hp := Option.some.inj (hG.symm.trans xG)
  refine ⟨{ x₄.2.P with tokv := tokv }, fo, F₄, t, G, u, ?_, ?_⟩
  · rw [xg] at hh
    exact hh
  · obtain ⟨Lk, b, y₄, e1, e2, -, hla, -, eg, eP, ehp, et, epl⟩ := IM.k4_of h.scope h.reads O g hg
    obtain ⟨⟨O₁, hO₁⟩, -⟩ := _root_.Meaning.Reads.plan_of_plansG epl xG
    obtain ⟨s1, -⟩ := OnBytes.Road.planG_sizes hO₁
    intro a
    have e := _root_.Meaning.Reads.sizes_of_map s1 a
    show ((x₄.2.P.tails.getD g {}).mats.getD a {}).m = _ ∧ ((x₄.2.P.tails.getD g {}).mats.getD a {}).k = _
    rw [xP, ← eP]
    exact ⟨e.1.symm, e.2.symm⟩

/-- **TieStateP at a layers' segment.** -/
theorem tieStateP_layers_head {g : ℕ} (hg : g < 12) :
    TieStateP (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said Sz.ref
      (K1.noL (2 * g) false) (2 * g) (nReads (P5J.At.X Zp) (2 * g)) := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  have hl2 : 2 * g < 25 := by omega
  obtain ⟨e, Xl, reads, he, hX, hu⟩ := K1.k01_flat_reads h.scope h.reads O (2 * g) hl2
  obtain ⟨m0, m1, fm, km, gm, -⟩ := (IM.ground_named h.scope h.reads O.pub O.blank).1 g hg
  obtain rfl : m0 = Xl := Option.some.inj (fm.symm.trans hX)
  obtain ⟨Lk, b, y₄, e1, e2, -, hla, -, eg, eP, ehp, et, epl⟩ := IM.k4_of h.scope h.reads O g hg
  have hU := IM.alone_underR hu
  have hq := k1Quiet_layers hX km (by rw [gm]; exact ehp)
  obtain ⟨⟨O₁, hO₁⟩, -⟩ := _root_.Meaning.Reads.plan_of_plansG epl ehp
  obtain ⟨-, hsz⟩ := OnBytes.Road.planG_sizes hO₁
  have eT := OnBytes.HonestTrace.U3.Fit.tlOf_even (OnBytes.HonestTrace.U3.Fit.marks_at_head h O.blank) hg ehp
  have hShape : ShapesFit y₄.2.hp.tl Sz.ref (2 * g) := by
    have q := shapesFit_at_head h O.blank hl2 (by rw [eT, hsz])
    rwa [eT] at q
  have eN : nReads (P5J.At.X Zp) (2 * g) = y₄.2.hp.nU.getD 2 0 := by
    unfold nReads
    rw [if_neg (by omega), if_pos (by omega), show 2 * g / 2 = g by omega]
    show ((Zp.p.X.G[g]?).map fun hp => hp.nU.getD 2 0).getD 0 = _
    rw [← O.W, ehp]
    rfl
  rw [eN]
  exact tieStateP_layers he hU hq hShape (ownHeardS_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    Said hSaid O hg ehp hX km gm hU he)

/-- **AttTlS at an attention's segment.** -/
theorem attTlS_head {Bs : ProofFile.PureBase} {base₀ : List (Block TS ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
    {g : ℕ} (hg : g < 12) {A : OnBytes.Attention.Plan} (hA : Bs.G₀.W.A[g]? = some A) :
    AttTlS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said (K1.noL (2 * g + 1) false) A := by
  intro blk hb k s μ E ds y cols s' hT hd hS
  have hl2 : 2 * g + 1 < 25 := by omega
  have hT' : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      (K1.noL (2 * g + 1) false) k s μ E := ⟨hT.1, hSaid _ _ _ hT.2⟩
  have hbl : K1.noL (2 * g + 1) false ≤ cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hb).1.le
  have hIn := inAt_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hT
  have σ : (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a))
      (D.at frS.P.T.a).key₁ 0).E.Str := (fun _ => default, fun _ => default)
  have hr := thrS_rchAt h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w σ hbl hT'
  have hon := (hIn (Sound.strsOf _ σ)).1
  have hm : s.failed = none := (hIn (Sound.strsOf _ σ)).2
  have hst := K1.stand_of_promise (2 * g + 1) hl2 _ _ (hIn (Sound.strsOf _ σ))
  have hsub : (Sound.linksFull[2 * g + 1]?).getD .layers = First.ModelPart.attention := by
    have : ∀ g, g < 12 → (Sound.linksFull[2 * g + 1]?).getD .layers = First.ModelPart.attention := by decide
    exact this g hg
  rw [hsub] at hst
  have hP := K1.tlIsPlan_at_reads h.scope h.reads O (XV := Bs.G₀.W) rfl h.𝔇.N
    (honest (mgAll h.𝔇 mgBase) _ _) (2 * g + 1) hl2 ((μ.st.input.x.pub, s), σ) hr hon hm
  have hno : Sound.linkNo s = 2 * g + 1 := K1.linkNo_at_reads_b h (2 * g + 1) hl2
    ((μ.st.input.x.pub, s), σ) hon hm
  unfold First.standOf at hst
  cases hh : s.here with
  | att a =>
    refine ⟨a, rfl, hP a A hh ?_⟩
    show Bs.G₀.W.A[Sound.linkNo s / 2]? = some A
    rw [hno, show (2 * g + 1) / 2 = g by omega]
    exact hA
  | between => rw [hh] at hst; cases hst
  | lay a => rw [hh] at hst; cases hst
  | head a =>
    rw [hh] at hst
    have hst' : (if s.inLink = true then First.Stand.link .head else First.Stand.headFront) =
        First.Stand.link .attention := hst
    by_cases hc : s.inLink = true
    · rw [if_pos hc] at hst'
      cases hst'
    · rw [if_neg hc] at hst'
      cases hst'
  | fin a => rw [hh] at hst; cases hst
  | mem a => rw [hh] at hst; cases hst

/-- **TieStateP at an attention's segment.** -/
theorem tieStateP_att_head {g : ℕ} (hg : g < 12) :
    TieStateP (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said Sz.ref
      (K1.noL (2 * g + 1) false) (2 * g + 1) (nReads (P5J.At.X Zp) (2 * g + 1)) := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  have hl2 : 2 * g + 1 < 25 := by omega
  obtain ⟨e, Xl, reads, he, hX, hu⟩ := K1.k01_flat_reads h.scope h.reads O (2 * g + 1) hl2
  obtain ⟨m0, m1, -, -, -, -, f2, k2, g2, -⟩ := (IM.ground_named h.scope h.reads O.pub O.blank).1 g hg
  obtain rfl : m1 = Xl := Option.some.inj (f2.symm.trans hX)
  obtain ⟨-, -, -, A, -, -, -, -, hA, -⟩ := IM.k5_of h.scope h.reads O g hg
  have hU := IM.alone_underR hu
  have eT := OnBytes.HonestTrace.U3.Att.tlOf_odd (OnBytes.HonestTrace.U3.Fit.marks_at_head h O.blank) hA
  have hpub : OnBytes.Model.Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := h.pubOne
  have C := OnBytes.Road.Hd.core_of_scope h.scope h.reads hpub
  have hW : Bs.G₀.W = Zp.p.X := O.W
  have hA' : Zp.p.X.A[g]? = some A := hW ▸ hA
  have etl : _root_.Meaning.tlAt Zp.p.X (2 * g + 1) = A.seam.tl := by
    unfold _root_.Meaning.tlAt
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      show (2 * g + 1) / 2 = g by omega, hA']
    rfl
  have hNM : A.seam.tl.NM = A.seam.tl.mats.size := by
    have q := _root_.Meaning.nm_of_core hpub C hl2
    rwa [etl] at q
  have hShape : ShapesFit A.seam.tl Sz.ref (2 * g + 1) := by
    have q := shapesFit_at_head h O.blank hl2 (by rw [eT, hNM])
    rwa [eT] at q
  have hAg : Bs.G₀.W.A[m1.g]? = some A := by rw [g2]; exact hA
  have eN : nReads (P5J.At.X Zp) (2 * g + 1) = A.nW := by
    unfold nReads
    rw [if_neg (by omega), if_neg (by omega), show (2 * g + 1) / 2 = g by omega]
    show ((Zp.p.X.A[g]?).map fun a => a.nW).getD 0 = _
    rw [hA']
    rfl
  rw [eN]
  exact tieStateP_att he hU hX k2 hAg hShape (OnBytes.HonestTrace.SameSizes.refl _)
    (attTlS_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hSaid O hg hA)

/-- **TieStateP at the output head.** -/
theorem tieStateP_out_head :
    TieStateP (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said Sz.ref
      (K1.noL 24 false) 24 (nReads (P5J.At.X Zp) 24) := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨e, Xl, reads, he, hX, hu⟩ := K1.k01_flat_reads h.scope h.reads O 24 (by omega)
  obtain ⟨m2, f2, k2, -⟩ := (IM.ground_named h.scope h.reads O.pub O.blank).2
  obtain rfl : m2 = Xl := Option.some.inj (f2.symm.trans hX)
  have hU := IM.alone_underR hu
  have hq := VerifiableInference.Desc.First.K8.Honest.k1Quiet_head hX k2
  have M := OnBytes.HonestTrace.U3.Fit.marks_at_head h O.blank
  have eT : ProofFile.Honest.K3.tlOf Bs.G₀.W 24 = Bs.G₀.W.H.tl := by
    unfold ProofFile.Honest.K3.tlOf ProofFile.Honest.K3.linkH ProofFile.Honest.K3.stepOf
    rw [M.p4, M.groups]
    rfl
  have hpub : OnBytes.Model.Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := h.pubOne
  have C := OnBytes.Road.Hd.core_of_scope h.scope h.reads hpub
  have hW : Bs.G₀.W = Zp.p.X := O.W
  have hNM : Bs.G₀.W.H.tl.NM = Bs.G₀.W.H.tl.mats.size := by
    have q := _root_.Meaning.nm_of_core hpub C (k := 24) (by omega)
    rw [hW]
    exact q
  have hShape : ShapesFit Bs.G₀.W.H.tl Sz.ref 24 := by
    have q := shapesFit_at_head h O.blank (l := 24) (by omega) (by rw [eT, hNM])
    rwa [eT] at q
  have eN : nReads (P5J.At.X Zp) 24 = Bs.G₀.W.H.nU.getD 2 0 := by
    unfold nReads
    rw [if_pos rfl, hW]
    rfl
  rw [eN]
  exact tieStateP_head he hU hq hShape

/-- **hSt at each of the 25 segments.** -/
theorem tieStateP_all_head {l : ℕ} (hl : l < 25) :
    TieStateP (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said Sz.ref
      (K1.noL l false) l (nReads (P5J.At.X Zp) l) := by
  by_cases h24 : l = 24
  · subst h24
    exact tieStateP_out_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hSaid
  · by_cases he : l % 2 = 0
    · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by omega⟩
      exact tieStateP_layers_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hSaid (by omega)
    · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
      exact tieStateP_att_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hSaid (by omega)

end

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.ownHeardS_head
#print axioms ProofFile.Honest.K1.tieStateP_layers_head
#print axioms ProofFile.Honest.K1.attTlS_head
#print axioms ProofFile.Honest.K1.tieStateP_att_head
#print axioms ProofFile.Honest.K1.tieStateP_out_head
#print axioms ProofFile.Honest.K1.tieStateP_all_head
