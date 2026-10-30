-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TotalHead.lean: FOR THE ITEM "totalB": AN ASSEMBLY AT THE HEAD's SEGMENT (number 24),
AT THE FRAME's OWN THREAD AT THE LIBRARY's HEAD: `GivesTotalB` (Honest/K9/TotalFront.lean) FROM EIGHT NAMED DEBTS AND
THREE CONDITIONS ON A FREE LETTER: Honest/K9/TotalAtt.lean's like, by the same join (`join_plain`). AN IMPLICATION
STILL. Statements and proofs: calls; no goal is stated.
  `seated_w_head`   under the head, at K9's seat at 24: the seat's letter w IS (.head, X.H.nLin, ⟨1, 24, 0, X.H.nMsg,
      X.H.nU⟩), X the public parameters
  **`givesTotalB_head`**   at T := the thread of `lettersHead …`, b := the number of the segment's batching in the
      head's own table: `GivesTotalB Lk p T b own rdW (rowsFit p.rows) tst Front`
FREE LETTERS: rdW · tst · Front · F₁ · sent · Hc · Hh: what Honest/K9/TotalAtt.lean's head says of its free letters
holds here (there is no Xp, mH or hmH here).
PASSES THROUGH: Sd (K9's seat at 24). PINNED: own, by hown, as in Honest/K9/TotalAtt.lean.
PAID INSIDE, BY CALLS: as in Honest/K9/TotalAtt.lean, at `seal_head`, `okFront_head_at_head`, `rwFront_head_at_head`,
`k8At_head`, `k8Behind_head` at `take_head`, `thetaAt_head`, `laterRun_head_paid`, `sized_head`, `laterDraw_at`,
`totalIn_paid`; the smallness test's hearing block is number 5 here. BUT:
  `FrontShares.counts` is paid UNDER hfold
  `ItemBack` WHOLE at seven of the order's eleven entries: the two "guests" (`itemBack_guests_head`) · "norm", "join",
      "policy", "logits", "the merge" (`itemBack_head`, Honest/K9/BackAt.lean, at `take_head`, its named premise
      `RunAnswers` paid by `runAnswers_at_head`, Honest/K9/RunAnswersAt.lean), under hforms, AT WHATEVER SECOND HOLE
      Hc · AND AT AN EIGHTH, "K8.equations", all terms but the first four (`rest_back_ahead`; `itemBack_eqs_head`;
      `noAhead_at_head`), under hformsE
WHAT STAYS: EIGHT DEBTS (on whose each is, what Honest/K9/TotalAtt.lean's head says holds here): hE · htst · hFacts ·
hFront · hVals: as Honest/K9/TotalAtt.lean's head says them; AND
  hback: `ItemBack` at the lookups' three entries: the lookups'
  hlens: `LensAt`, here "= X.H.nLin" (`seated_w_head`): OURS. Not paid. Exchanged in Honest/K9/LensRuns.lean
      (`lensAt_head_runs`: above this file; not called here) for `LensEqAsked Zp` alone, a named public premise: a test
      with code that no verifier asks; evaluated true at the stored full-size example alone, proved at no public part
      (Johnson/Desc/K9/Honest/LensEq.lean); every run's own number is paid there and in Honest/K9/LensLook.lean
  hfold: `FoldOnce` (at a stand the matrix is counted as drawn once)

THREE CONDITIONS ON Front: hforms: at the five entries it gives the sentence "forms" at the readers of Hc (the table's
own at Hc := the table's holes at the public parameters and this segment: by reading, not typed) · hformsE · hF₁: as
in Honest/K9/TotalAtt.lean, at (5, "K8.equations"); and what that head says behind its three holds here.
AND BESIDE THEM: the head h · an opening O of the head's own form · Sd · FOUR READINGS, each "… = some …": hd, hC, hD
off the public parameters; e3 off the opening's ground. hD follows from hd (`placeD_of_dig`, Honest/K9/TotalAtt.lean):
not laid in.
THE TIES, THE GROUND: as Honest/K9/TotalAtt.lean's head says them.
SINCE THIS FILE the words "called by no line" in the heads of Honest/K9/K8BehindAt.lean, RwFrontAt.lean,
OkFrontAt.lean, TotalFill.lean, TotalItems.lean, BackAt.lean and RunAnswersAt.lean are overtaken for `take_head`,
`k8Behind_head`, `rwFront_head_at_head`, `okFront_head_at_head`, `seal_head`, `itemBack_guests_head`,
`itemBack_eqs_head`, `itemBack_head`, `runAnswers_at_head`; so is "by reading, not typed" for the filling in
Honest/K9/BackAt.lean's head, at this sort.
WHAT IS NOT CLAIMED. Any of the eight at any thread. The three conditions at any Front. The four readings, O or Sd at
any public part. That a stand is there. That all these can stand together. No member: `givesTotalB_head` is called by no
line. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.TotalAtt
import Johnson.Desc.ProofFile.Honest.K9.RunAnswersAt
import Johnson.Desc.First.Att.Door.Law.K5RestOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (batchAt pi8 SegAt)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.First.K8.Honest (ThetaAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K8 (FrontAtStandN ValuesAtStand FoldOnce k8Share k8At_head counts_front_seal kindOver_lsTail
  kindOver_tests)
open _root_.Desc.K14.Law (seatZ secondAt)

/-- The seat's letter at the head's segment. -/
theorem seated_w_head {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where}
    {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp 24 kk Lk p w) :
    w = (.head, (P5J.At.X Zp).H.nLin, ⟨1, 24, 0, (P5J.At.X Zp).H.nMsg, (P5J.At.X Zp).H.nU⟩) := by
  obtain ⟨h4, hN, -⟩ := H2K5.Door.scope_all h
  have ht := Sd.tested
  have h4' : Zp.p.X.p4 = true := h4
  have hN' : Zp.p.X.NGr = 12 := hN
  unfold Desc.K9.testsWhere at ht
  simp only [h4', hN', if_true] at ht
  exact (Option.some.inj ht).symm

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The assembly at the head's segment.** -/
theorem givesTotalB_head (hE : K9Asks.RowsAsked Zp) {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where}
    {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp 24 kk Lk p ww) {Xl : LinkH}
    (e3 : Bs.G₀.built[24]? = some Xl) {xx : First.Look.Place} {tlD : HTailF2}
    (hd : First.Look.digAt (P5J.At.X Zp) 24 = some (xx, tlD)) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) 24 false = some pC) (hD : placeAt (P5J.At.X Zp) 24 true = some pD)
    (own : List (ℕ × ℕ))
    (hown : own = (P5J.At.N Zp cF).group 24)
    (rdW : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Wt → ℕ × ℕ → Sound.MsgQ)
    (tst : S → Option String)
    (Front : ℕ × String → S → (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Wt → Prop)
    (htst : ∀ e, tst e = none → freeSlotShare ww.2.2.filled e = none ∧ k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none)
    (hback : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ItemBack Lk p (phiFill tlD)
      (okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD) (tmFillHead Bs.G₀.W pC pD)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps 24) own rdW o (Front o))
    (F₁ : S → (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Wt → Prop)
    (hFacts : ∀ κ s m En ds y cols s' x' z G,
      BatStand Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps 24) κ s m En ds y cols s' x' z G →
      ∀ a v, Desc.K9.atS.get? s = some a →
        okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD (K9L.fixed9 (phiFill tlD) s) →
        F₁ s v → First.K8.Honest.FourFacts tlD pi8 (K9L.fixed9 (phiFill tlD) s) (Sound.dataQ own a (rdW v)))
    (hF₁ : ∀ s v, Front (5, "K8.equations") s v → F₁ s v) (Hc Hh : Desc.K9.LinkHoles)
    (hforms : ∀ o ∈ [(3, "norm"), (3, "policy"), (3, "logits"), (8, "the merge"), (3, "join")], ∀ s v,
      Front o s v → Sound.formsQ (Desc.K9.readersOfLink Hc Lk) own o.1 o.2 s (rdW v))
    (sent : ℕ → List (ℕ × ℕ))
    (hformsE : ∀ s v, Front (5, "K8.equations") s v →
      Sound.formsQA sent own (Desc.K9.readersOfLink (Desc.K9.withSmall Hh) Lk) 5 "K8.equations" s (rdW v))
    (hlens : LensAt Lk p (phiFill tlD) (okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD) (tmFillHead Bs.G₀.W pC pD)
      (lenFillHead Bs.G₀.W pC pD) (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps 24) ww)
    (hFront : FrontAtStandN Lk p (phiFill tlD) (okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD) (ProofFile.k8NU Bs.G₀ Xl)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links P5J.At.ps 24))
    (hVals : ValuesAtStand Lk p (phiFill tlD) (okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD) (ProofFile.k8NU Bs.G₀ Xl)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links P5J.At.ps 24))
    (hfold : FoldOnce Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps 24)) :
    GivesTotalB Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps 24) own rdW (Desc.K9.rowsFit p.rows) tst Front := by
  have hm : 24 < 25 := by omega
  have htot : TotalInBehind Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps 24) own := by
    rw [hown]
    exact totalIn_paid h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm Sd
  have hs : IM.subAt 24 = .head := by decide
  obtain ⟨hlk, seg, drawB, kp⟩ := tied_of_seated h hm Sd
  have seg' : SegAt 24 .head Lk := hs ▸ seg
  obtain ⟨X₁, a2, SL⟩ := seal_head h O hs Lk p hlk seg drawB kp pC pD hC hD xx tlD hd
  have eX₁ : X₁ = Xl := Option.some.inj (a2.symm.trans e3)
  rw [eX₁] at SL
  obtain ⟨X₂, b2, TK⟩ := take_head h O hs Lk p hlk seg drawB kp pC pD hC tlD
  have eX₂ : X₂ = Xl := Option.some.inj (b2.symm.trans e3)
  rw [eX₂] at TK
  obtain ⟨X₃, c1, hK⟩ := k8At_head h.scope h.reads O
  have eX₃ : X₃ = Xl := Option.some.inj (c1.symm.trans e3)
  rw [eX₃] at hK
  have hK' := hK Lk Sd.link seg'
  have hk3 := ProofFile.Honest.K8.thetaAt_head h Sd.link
  have hw : ww.1 = .head := by rw [seated_w_head h Sd]
  have hKw : ProofFile.Honest.K8.K8At Lk ww.1 (ProofFile.k8ParW Zp Bs.G₀ Xl 24) := by
    rw [hw]
    exact hK'
  have hsub : (ProofFile.subsOf Zp)[24]? = some ModelPart.head := hs ▸ IM.subs_scope h.scope h.reads O 24 hm
  obtain ⟨Lk', d1, X₄, d2, SO⟩ := seatOver_k8_at O 24 .head hsub 5 rfl (by omega)
  have eL : Lk' = Lk := Option.some.inj (d1.symm.trans Sd.link)
  have eX₄ : X₄ = Xl := by
    have e3' : Bs.G₀.built.toList[24]? = some Xl := by simpa using e3
    exact Option.some.inj (d2.symm.trans e3')
  rw [eL, eX₄] at SO
  have hoa : Lk.orderAfter = [(5, "K8.lsTail"), (5, "K8.tests")] := seg'.orderAfter
  obtain ⟨rLs, hLs, -⟩ := K9L.k8_lsTail_under (ProofFile.k8ParW Zp Bs.G₀ Xl 24)
  obtain ⟨rTs, hTs, -⟩ := K9L.k8_tests_under (ProofFile.k8ParW Zp Bs.G₀ Xl 24)
  have so0 : SeatOver Lk 0 rLs := SO 0 "K8.lsTail" rLs (by rw [hoa]; rfl) hLs
  have so1 : SeatOver Lk 1 rTs := SO 1 "K8.tests" rTs (by rw [hoa]; rfl) hTs
  have hlen : Lk.orderAfter.length = 2 := by rw [hoa]; rfl
  have hfour : TermsBack Lk p (phiFill tlD) (okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps 24) own rdW LinkJoin.tmFour F₁ :=
    ProofFile.Honest.K8.termsBack_four _ _ own rdW SL hK'
      (ProofFile.Honest.K8.laterRun_head_paid h Sd.link seg' TK) (laterDraw_at p)
      (fun q v hq hv => sized_head q v hq hv) F₁ hFacts
  have hrest : TermsBack Lk p (phiFill tlD) (okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps 24) own rdW (fun _ => K9L.tmRest pi8)
      (fun s v =>
        Sound.formsQA sent own (Desc.K9.readersOfLink (Desc.K9.withSmall Hh) Lk) 5 "K8.equations" s (rdW v)) :=
    fun κ s m En ds y cols s' x' z G St a v ha _ hF _ c hc =>
      rest_back_ahead Hh Lk (phiFill tlD) sent own (5, "K8.equations") rfl tlD pi8 (fun _ => rfl) s a ha (rdW v)
        (noAhead_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm Lk p sent own κ s m En ds y cols s' x' z G St)
        hF c hc
  have hord : Lk.order = [(2, "objects"), (2, "guests"), (3, "norm"), (3, "join"), (3, "policy"), (2, "planes"),
      (7, "objects"), (7, "guests"), (5, "K8.equations"), (3, "logits"), (8, "the merge")] := by
    rw [LinkJoin.split_head seg']
    rfl
  have hcall := itemBack_head (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
    (batchAt P5J.At.links P5J.At.ps 24) p own rdW Hc TK
    (runAnswers_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hlk p)
  have hback' : ∀ o ∈ Lk.order, ItemBack Lk p (phiFill tlD) (okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
      (tmFillHead Bs.G₀.W pC pD) (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps 24) own rdW o (Front o) := by
    intro o ho
    rw [hord] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hback _ (by simp)
    · exact itemBack_guests_head Bs.G₀.W 2 _
    · exact termsBack_mono _ _ p own rdW (hforms _ (by simp)) (hcall _ (by simp))
    · exact termsBack_mono _ _ p own rdW (hforms _ (by simp)) (hcall _ (by simp))
    · exact termsBack_mono _ _ p own rdW (hforms _ (by simp)) (hcall _ (by simp))
    · exact hback _ (by simp)
    · exact hback _ (by simp)
    · exact itemBack_guests_head Bs.G₀.W 7 _
    · exact termsBack_mono _ _ p own rdW (fun s v hF => ⟨hF₁ s v hF, hformsE s v hF⟩)
        (itemBack_eqs_head Bs.G₀.W 5 F₁ _ hfour hrest)
    · exact termsBack_mono _ _ p own rdW (hforms _ (by simp)) (hcall _ (by simp))
    · exact termsBack_mono _ _ p own rdW (hforms _ (by simp)) (hcall _ (by simp))
  have FS : FrontShares Lk p (phiFill tlD) (okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD) pi8
      (tmFillHead Bs.G₀.W pC pD) (lenFillHead Bs.G₀.W pC pD)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links P5J.At.ps 24) own rdW ww
      Front :=
    ⟨okFront_head_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O e3 hd hC hD Lk p, hback', hlens,
      counts_front_seal _ _ SL ww _ hKw (fun _ => hfold),
      rwFront_head_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hE Lk kp tlD, htot⟩
  have K8B := k8Behind_head (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
    (batchAt P5J.At.links P5J.At.ps 24) (p := p) seg' TK hK' hk3 hFront hVals
  exact join_plain cF Zp kk ww (Desc.K9.rowsFit p.rows) tst (k8Share (ProofFile.k8NU Bs.G₀ Xl)) rLs rTs
    (ProofFile.k8ParW Zp Bs.G₀ Xl 24) Front Sd SL (fun _ => rfl) htst FS hlen rfl hLs hTs so0
    (kindOver_lsTail _ hLs) so1 (kindOver_tests _ hTs) K8B

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.seated_w_head
#print axioms ProofFile.Honest.K9.givesTotalB_head
