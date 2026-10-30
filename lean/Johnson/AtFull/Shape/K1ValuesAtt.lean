-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/K1ValuesAtt.lean: K1's TEST ON VALUES AT THE TWELVE ATTENTION READS (members
14 (2 k + 1) + 5 of the first chain), IN THE RULE's FORM ValuesJ, AT THE TABLE's OWN LETTERS. The
cell's test is midV … (valsTS A): the commitment's decision returns m and valsTS A m passes.

  reach_back                   one member back along Reach
  planR_at_head_olderK                the plan's facts (H2K5.Honest.PlanR) under the head
  lookR_reached                at every state reached in front of the reads the field g meets lookR
  commit_here_g                the commitment leaves the attention link's field g
  k1_valuesJ_att               the theorem

Limits. Premises beside the head: the thread's list and ft, that it begins at a start of the
chain, FitsAt at this member, the run on shapes. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.TableBatch
import Johnson.Prover.Send.Form
import Johnson.Desc.ProofFile.Honest.Thread.ShapeJV
import Johnson.Desc.K5.Honest.Law.PublicAtHead
import Johnson.Desc.K5.Honest.Law.RunsPreR
import Johnson.P1K8R.DepthAtAtt
import Johnson.Desc.ProofFile.Honest.K5.Law.LookRHeard
import Johnson.Desc.ProofFile.Honest.K5.Law.ShapeFrame
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LaysAttHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Place noDigest roundsFit step_iff K1.commitAtS)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open ProofFile.Honest (Shape Thread Thr ThrS ValuesJ FitsAt shapeJ run_front Coins ProverCoinCounts Mid Env roundsOf)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)
open H2K5.Honest (lookR PlanR valsTS tabsGC parts_of_GC)

/-- One member back. -/
theorem reach_back {σ Cl P : Type} {ft : Nat} {bs : List (Block σ Cl)} {st : P → σ} {k : Nat}
    {z : P} {s' : σ} (h : Reach ft bs st (k + 1) (z, s')) :
    ∃ s b, Reach ft bs st k (z, s) ∧ bs[k]? = some b ∧ StepYes ft b s s' := by
  cases h with
  | succ h1 h2 h3 => exact ⟨_, _, h1, h2, h3⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- **The plan's facts under the head.** -/
theorem planR_at_head_olderK (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : Nat} (hg : g < 12)
    {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) :
    ∃ r1 r2 u1 u2 wl ix wh, PlanR a r1 r2 u1 u2 wl ix wh := by
  obtain ⟨hid, PL⟩ := H2K5.Honest.law_at_head h hg ea
  have PA := H2K5.Honest.public_at_head h hg ea
  obtain ⟨r1, r2, u1, u2, wl, ix, wh, U, -⟩ := PA.units
  have N := OnBytes.Road.Rows.norm_of_hid hid
  have Zs := OnBytes.Road.Rows.sizes_of_hid hid
  have hl : 1 ≤ a.S.lnT := Nat.le_of_succ_le Zs.lnT
  have fD : a.S.nD ≤ a.fs.dT := by
    have e : (OnBytes.Road.L5.dimOf a.S).lD = a.S.nD := N.nD.symm
    have := PL.fit.2.2.2.2.2.2.1.2.1
    rw [e] at this
    exact this
  have fW : (OnBytes.Road.L5.dimOf a.S).lW ≤ a.fs.dT := PL.fit.2.2.2.2.2.2.1.2.2.1
  refine ⟨r1, r2, u1, u2, wl, ix, wh, U, N, hl, ?_, PA.fit, le_trans Zs.lmS fD, ?_⟩
  · intro f hf
    have hD : a.S.cf.lmS ≤ (OnBytes.Road.L5.dimOf a.S).lD := by
      rw [show (OnBytes.Road.L5.dimOf a.S).lD = a.S.nD from N.nD.symm]
      exact Zs.lmS
    have hM : (OnBytes.Road.L5.dimOf a.S).lD ≤ (OnBytes.Road.L5.dimOf a.S).lM := by
      show _ + _ + _ + _ ≤ _ + _ + _ + _ + _
      omega
    cases f with
    | m1 => exact le_trans hD hM
    | d1 => exact hD
    | m2 => exact le_trans hD hM
    | d2 => exact hD
    | _ => exact hf.elim
  · have hlt := N.lt
    refine le_trans ?_ fW
    show _ ≤ 1 + a.S.cf.lgk + (a.S.lnT - 1 + 1 + a.S.cf.lB) + a.S.cf.ldh
    omega

/-- **At every state reached in front of the reads of group g, the field g meets lookR.** -/
theorem lookR_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : Nat} (hg : g < 12)
    {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g + 1) + 5) (z, s)) :
    ∃ w, s.here = .att w ∧ lookR a w.g := by
  obtain ⟨s₁, b₄, hr₁, hb₄, y₄⟩ := reach_back (k := 14 * (2 * g + 1) + 4) hr
  obtain ⟨s₀, b₃, hr₀, hb₃, y₃⟩ := reach_back (k := 14 * (2 * g + 1) + 3) hr₁
  obtain ⟨p, hp, hB⟩ := ProofFile.Honest.K3.Law.AtThr.calls_att_head h g hg a b₃ ea hb₃
  obtain ⟨R₃, c₃, -, e₃⟩ := y₃
  obtain ⟨F, H, G₁, w, hv, hw, hwg⟩ := hB z 0 s₀ s₁ R₃ c₃ _ hr₀ e₃
  have hR : lookR a (some H) := ProofFile.Honest.K5.lookR_of_hearVia h hg ea p hp F R₃ H G₁ hv
  obtain ⟨blk, a', hfl, Pl, Dc⟩ := ProofFile.Honest.K5.k5_member h hg
  obtain rfl : a' = a := Option.some.inj (Pl.plan.symm.trans ea)
  have eb : ProofFile.Honest.K5.borderOf g = 14 * (2 * g + 1) + 4 := by
    unfold ProofFile.Honest.K5.borderOf
    omega
  rw [eb] at hfl
  obtain rfl : blk = b₄ := Option.some.inj (hfl.symm.trans hb₄)
  obtain ⟨R₄, c₄, -, e₄⟩ := y₄
  obtain ⟨_, hd, _⟩ := (step_iff 0 blk s₁ s R₄ c₄ _).1 e₄
  obtain ⟨w', hd', G, hh, _, rfl⟩ := H2K5.Honest.k5_yes_is _ ((Dc.decides _ _ _ _).1 hd).1
  rw [hw] at hh
  obtain rfl : w = w' := by cases hh; rfl
  exact ⟨_, rfl, by rw [show _ = w.g from rfl, hwg]; exact hR⟩

theorem putLink_att {s : S} {w : VerifiableInference.Desc.First.AttOwn}
    (h : s.here = .att w) (L : LinkCtx) :
    (s.putLink L).here = .att { w with L := L } := by
  unfold VerifiableInference.Desc.First.S.putLink
  rw [h]

theorem putFork_att {s : S} {w : VerifiableInference.Desc.First.AttOwn}
    (h : s.here = .att w) (F : Fork) : (s.putFork F).here = .att { w with F := F } := by
  unfold VerifiableInference.Desc.First.S.putFork
  rw [h]

/-- The commitment leaves the attention link's field g. -/
theorem commit_here_g {P : VerifiableInference.Desc.K1.Par} {link moment : Nat}
    {arrays : Option (List Nat)} {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K1.commitAtS (Cl := Unit) P link moment arrays).decide s rs gs = .ok t)
    {w : VerifiableInference.Desc.First.AttOwn}
    (hw : s.here = .att w) : ∃ w', t.here = .att w' ∧ w'.g = w.g := by
  simp only [K1.commitAtS] at h
  split at h
  · rename_i L F tl _ _ _
    cases hb : (VerifiableInference.Desc.K1.commitOwn (Cl := Unit) P link moment arrays).decide
        ⟨VerifiableInference.Desc.K1.owedOf s,
          ⟨L, F, tl, VerifiableInference.Desc.K1.stateOf s ()⟩⟩ rs gs with
    | error e => simp [hb, Except.map] at h
    | ok y =>
      simp only [hb, Except.map, Except.ok.injEq] at h
      subst h
      have e0 : (VerifiableInference.Desc.K1.laid s y.held.w).here = .att w := hw
      exact ⟨_, putFork_att (putLink_att e0 _) _, rfl⟩
  · cases h

variable {V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **K1's test on values at the attention reads, in the rule's form.** -/
theorem k1_valuesJ_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (T : Thread Bk S ProofFile.Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String) (hbs : T.bs = cF.blocksInOrder) (hft : T.ft = 0)
    (hs₀ : ∀ k w hd s₀, T.begun k w hd s₀ → ∃ p, s₀ = ProofFile.startS Zp p)
    {k : Nat} (hk : k < 12) (hfit : FitsAt T (14 * (2 * k + 1) + 5)) {a₀ : ShA}
    (hyes : (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes a₀ 358 = true) :
    ValuesJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀)
      (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) fall (14 * (2 * k + 1) + 5) := by
  obtain ⟨B', Xl, pd, reads, digits, A, -, e1, e2, e3, e4, -⟩ := reads_att_frame_free h k hk
  obtain rfl := base_one hB e1
  obtain ⟨Bs₁, Xl₁, pd₁, reads₁, digits₁, A₁, b, e1', -, -, -, q, hrd, -⟩ := reads_att_at h k hk
  obtain rfl := base_one hB e1'
  have hc : Tab.cells Zp Bs.G₀ (14 * (2 * k + 1) + 5) = Tab.reads Zp Bs.G₀ (2 * k + 1) :=
    cells_link Zp Bs.G₀ (2 * k + 1) 4 (by omega) (by omega) rfl
  unfold Tab.reads at hc
  rw [nums_of e2 e3] at hc
  simp only [show ((2 * k + 1) % 2 == 0) = false from beq_eq_false_iff_ne.2 (by omega),
    Bool.false_eq_true, if_false, show (2 * k + 1) / 2 = k from by omega, e4] at hc
  have eg := cell_g hc
  have ev := cell_v hc
  obtain ⟨B₂, base, O⟩ := h.laid.opened
  obtain rfl := base_one hB O.made
  have ea : (P5J.At.X Zp).A[k]? = some A := by
    have hW : Bs.G₀.W = P5J.At.X Zp := O.W
    rw [← hW]
    exact e4
  intro blk hblk kk s m E ds y cols hA hJ hd _ _ hMv
  have hblk' : cF.blocksInOrder[14 * (2 * k + 1) + 3 + 2]? = some blk := by rw [← hbs]; exact hblk
  obtain rfl : b = blk := Option.some.inj (q.symm.trans hblk')
  obtain ⟨t, ht⟩ := run_front (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀ 358
    (14 * (2 * k + 1) + 5 + 1) (by omega) hyes
  have hg : Tab.g Zp Bs.G₀ (14 * (2 * k + 1) + 5) (shA s) = .ok t := by
    have ht' : ((firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).run (14 * (2 * k + 1) + 5) a₀).bind
        ((firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).g (14 * (2 * k + 1) + 5)) = .ok t := ht
    have hJ' : (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).run (14 * (2 * k + 1) + 5) a₀ =
      .ok (shA s) := hJ
    rw [hJ'] at ht'
    exact ht'
  rw [eg] at hg
  have hf1 := (hfit b hblk kk m E ds y cols hd hMv).1
  rw [hrd] at hf1
  have hf2 := (VerifiableInference.Desc.roundsFit_noDigest _ _).trans hf1
  obtain ⟨r₁, r₂, e2, -, han⟩ := k1_fit hf2
  have hz := Johnson.Prover.Send.factors_of_fit _ r₁ r₂ (e2 ▸ hf2)
  have hg2 : readsA (readsAttGS (Tab.k1P Zp Bs.G₀ (2 * k + 1) 4 1) (2 * k + 1) reads A)
      (Tab.k1P Zp Bs.G₀ (2 * k + 1) 4 1) (shA s) = .ok t := hg
  unfold readsA at hg2
  split at hg2
  swap
  · cases hg2
  rename_i u hu
  have hu' : readsAttGS (Tab.k1P Zp Bs.G₀ (2 * k + 1) 4 1) (2 * k + 1) reads A (chainSh s) =
    some u := hu
  unfold readsAttGS at hu'
  split at hu'
  · cases hu'
  obtain ⟨mm, hcm, hq⟩ := Option.bind_eq_some_iff.1 hu'
  split at hq
  swap
  · cases hq
  rename_i hG
  show Tab.vals Zp Bs.G₀ (14 * (2 * k + 1) + 5) s _ _ = true
  rw [ev]
  show midV (Tab.k1P Zp Bs.G₀ (2 * k + 1) 4 1) (2 * k + 1) reads (valsTS A) s _ _ = true
  rw [e2]
  obtain ⟨mS, hd', em⟩ := commit_returns (gs := (b.shown T.ft (roundsOf y.1) cols).take
    (K1.commitAtS (Cl := Unit) (Tab.k1P Zp Bs.G₀ (2 * k + 1) 4 1) (2 * k + 1) 1 reads).openings)
    hcm hz han
  unfold midV
  rw [hd']
  show valsTS A mS = true
  -- the parts at the state behind the commitment
  rw [← em] at hG
  obtain ⟨a, h₅, gl, e5, e6, e7, hT⟩ := parts_of_GC A hG
  -- lookR at the state in front
  have hA1 := hA.1
  unfold Thr ProofFile.Honest.Thread.Made at hA1
  obtain ⟨-, -, -, -, ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩, -, -⟩ := hA1
  obtain ⟨p, rfl⟩ := hs₀ _ _ _ _ hbeg
  rw [hbs, hft] at hfold
  have hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * k + 1) + 5) (p, s) :=
    Johnson.Desc.First.Walk.Tied.reach_of_fold _ (by rw [flat_len h]; omega) s _ _ _ _ hfold
  obtain ⟨w, hw, hR⟩ := lookR_reached h hk ea hr
  obtain ⟨w', hw', eg'⟩ := commit_here_g hd' hw
  obtain rfl : w' = a := by rw [e5] at hw'; cases hw'; rfl
  have hR' : lookR A w'.g := by rw [eg']; exact hR
  obtain ⟨r1, r2, u1, u2, wl, ix, wh, Q⟩ := planR_at_head_olderK h hk ea
  have hB1 : H2K5.Honest.ptsB (VerifiableInference.Desc.First.Att.P.parCOf A).geo
      (heardAll gl).zk (heard5Sh h₅) (ledSh w'.F) = true := by
    unfold H2K5.Honest.tabsG at hT
    simp only [Bool.and_eq_true] at hT
    exact hT.1.1
  obtain ⟨p', hp'⟩ := H2K5.Honest.pts_returns hB1
  exact H2K5.Honest.valsTS_of_R A Q e5 hR' e6
    (fun gl' e => by rw [e7] at e; cases e; exact ⟨p', hp'⟩) 0

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.reach_back
#print axioms Johnson.AtFull.Shape.planR_at_head_olderK
#print axioms Johnson.AtFull.Shape.lookR_reached
#print axioms Johnson.AtFull.Shape.commit_here_g
#print axioms Johnson.AtFull.Shape.k1_valuesJ_att
