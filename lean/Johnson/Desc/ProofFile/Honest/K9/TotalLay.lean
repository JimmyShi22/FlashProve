-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TotalLay.lean: FOR THE ITEM "totalB": AN ASSEMBLY AT A FEED-FORWARD SEGMENT (of even
number below 24), AT THE FRAME's OWN THREAD AT THE LIBRARY's HEAD: `GivesTotalB` (Honest/K9/TotalFront.lean) FROM EIGHT
NAMED DEBTS AND THREE CONDITIONS ON A FREE LETTER: Honest/K9/TotalAtt.lean's like, by the join for three runs behind
(`join_layers`, Honest/K9/TotalAfter.lean). AN IMPLICATION STILL. Statements and proofs: calls; no goal is stated.
  `seatOver_k4_at`   `SeatOver` for the feed-forward kind's run behind, at the first chain cF itself:
      Honest/K9/TotalOver.lean's `seatOver_k4` at the opening's own three equations
  `sub_even`   the segments of even number below 24 are feed-forward ones (the library has the like:
      `IM.subAt_layers`)
  `seated_sort_lay`   under the head, at K9's seat at such a segment: the seat's letter's sort is .layers
  **`givesTotalB_lay`**   at T := the thread of `lettersHead …`, b := the number of the segment's batching in the
      head's own table: `GivesTotalB Lk p T b own rdW (rowsFit p.rows) tst Front`
FREE LETTERS: rdW · tst · Front · F₁ · sent · Xp · mH · Hh · share4: what Honest/K9/TotalAtt.lean's head says of its
free letters, and of hmH, holds here. Where share4 always speaks, h4 costs nothing and htst makes tst always speak:
idle; where it never speaks, htst's third part costs nothing and h4 is at its dearest.
PASSES THROUGH: Sd (K9's seat at the segment). PINNED: own, by hown, as in Honest/K9/TotalAtt.lean.
run4 WITH hr4 (the feed-forward kind's own block lists run4 under "free-slot"): A PIN, so that `K4Behind` and the
seat speak of one run, AND A SIXTH READING: it is spent for the seat and, inside the join, for what
the run leaves (so the words "premises that the joins' proofs do not spend" in Honest/K9/TotalFront.lean's head do not
hold of it). No payer is called.
PAID INSIDE, BY CALLS: as in Honest/K9/TotalAtt.lean, at `seal_lay`, `okFront_lay_at_head`, `rwFront_lay_at_head`,
`k8At_layers`, `k8Behind_lay` at `take_lay`, `thetaAt_layers`, `laterRun_layers_paid`, `sized_lay`, `laterDraw_at`,
`totalIn_paid`; and the seat of the run between (`seatOver_k4_at`); the order behind has three entries. `ItemBack` WHOLE
at four of the order's seven entries: the two "guests" (`itemBack_guests_lay`) · "front", "back" (`itemBack_lay_at`,
Honest/K9/BackAt.lean, at `take_lay`), under hforms · AND AT A FIFTH, "K8.equations", all terms but the first four
(`rest_back_ahead`; `itemBack_eqs_lay`; `noAhead_at_head`), under hformsE.
WHAT STAYS: EIGHT DEBTS (on whose each is, what Honest/K9/TotalAtt.lean's head says holds here): hE · hFacts · hFront ·
hVals: as Honest/K9/TotalAtt.lean's head says them; AND
  htst: as there, with a third share, share4
  hback: `ItemBack` at the lookups' two entries: the lookups'
  hlens: `LensAt`: OURS. Not paid. Exchanged in Honest/K9/LensRuns.lean (`lensAt_lay_runs`: above this file; not called
      here) for `LensEqAsked Zp` alone, a named public premise: a test with code that no verifier asks; evaluated true
      at the stored full-size example alone, proved at no public part (Johnson/Desc/K9/Honest/LensEq.lean: ours); every
      run's own number is paid there and in Honest/K9/LensLook.lean. The seat's number is the segment's plan's nLin
      (`seated_w_lay`, Honest/K9/LensAtStand.lean)
  h4: `K4Behind`: the run between returns outside its own share: the feed-forward kind's house's
THREE CONDITIONS ON Front: hforms, at "front", "back" · hformsE · hF₁: as in Honest/K9/TotalAtt.lean; and what that
head says behind its three holds here.
AND BESIDE THEM: the head h · an opening O of the head's own form · g < 12 · Sd · FIVE READINGS, each "… = some …":
hd, hC, hD off the public parameters; e3 (the built link) and hk (that kind's numbers) off the opening's ground. hD
follows from hd (`placeD_of_dig`, Honest/K9/TotalAtt.lean): not laid in.
THE TIES, THE GROUND: as Honest/K9/TotalAtt.lean's head says them.
SINCE THIS FILE the words "called by no line" in the heads of Honest/K9/TotalAfter.lean, TotalOver.lean,
K8BehindAt.lean, RwFrontAt.lean, OkFrontAt.lean, TotalFill.lean, TotalItems.lean and BackAt.lean are overtaken for
`join_layers`, `seatOver_k4`, `take_lay`, `k8Behind_lay`, `rwFront_lay_at_head`, `okFront_lay_at_head`, `seal_lay`,
`itemBack_guests_lay`, `itemBack_eqs_lay`, `itemBack_lay_at`; so is "by reading, not typed" for the filling in
Honest/K9/BackAt.lean's head, at this sort.
WHAT IS NOT CLAIMED. Any of the eight at any thread. The three conditions at any Front. The readings, O or Sd at any
public part. That a stand is there. That all these can stand together. No member: `givesTotalB_lay` is called by no
line. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.TotalHead

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
open ProofFile.Honest.K8 (FrontAtStandN ValuesAtStand k8Share k8At_layers counts_front_seal kindOver_lsTail kindOver_tests)
open _root_.Desc.K14.Law (seatZ secondAt)

/-- `SeatOver` for the feed-forward kind's run, at an opening's own chain. -/
theorem seatOver_k4_at {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c A B) (l : ℕ) (sub : ModelPart)
    (hl : (ProofFile.subsOf Z)[l]? = some sub) (hk : (kindsBeforeBatching sub (l == 0))[2]? = some KindName.K4) :
    ∃ Lk, c.links[l]? = some Lk ∧ ∃ p4, LPFK9.k4ParAt Z Bs.G₀ l = some p4 ∧
      ∀ j name r, Lk.orderAfter[j]? = some (2, name) →
        (OnBytes.Desc.First.K4.blockAtC p4).after.lookup name = some r → SeatOver Lk j r :=
  seatOver_k4 O.made O.places O.chain l sub hl hk

theorem sub_even : ∀ g < 12, IM.subAt (2 * g) = .layers := by decide

/-- The seat's letter's sort at a feed-forward segment. -/
theorem seated_sort_lay {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) {kk : ℕ} {Lk : Link S ProofFile.Cl}
    {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp (2 * g) kk Lk p w) :
    w.1 = .layers := by
  obtain ⟨h4, hN, -⟩ := H2K5.Door.scope_all h
  have ht := Sd.tested
  have h4' : Zp.p.X.p4 = true := h4
  have hN' : Zp.p.X.NGr = 12 := hN
  unfold Desc.K9.testsWhere at ht
  simp only [h4', hN', if_true] at ht
  have e1 : (2 * g == 2 * 12) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  have e2 : ((2 * g) % 2 == 0) = true := by
    rw [beq_iff_eq]
    omega
  rw [e1, e2] at ht
  obtain ⟨hp, -, e⟩ := Option.map_eq_some_iff.1 ht
  rw [← e]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The assembly at a feed-forward segment.** -/
theorem givesTotalB_lay (hE : K9Asks.RowsAsked Zp) {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where}
    {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp (2 * g) kk Lk p ww) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g]? = some Xl) {xx : First.Look.Place} {tlD : HTailF2}
    (hd : First.Look.digAt (P5J.At.X Zp) (2 * g) = some (xx, tlD)) {p4 : OnBytes.Desc.First.K4.Par}
    (hk : LPFK9.k4ParAt Zp Bs.G₀ (2 * g) = some p4) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) (2 * g) false = some pC) (hD : placeAt (P5J.At.X Zp) (2 * g) true = some pD)
    (own : List (ℕ × ℕ))
    (hown : own = (P5J.At.N Zp cF).group (2 * g))
    (rdW : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Wt → ℕ × ℕ → Sound.MsgQ)
    (tst share4 : S → Option String)
    (Front : ℕ × String → S → (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Wt → Prop)
    (run4 : S → Except String S) (hr4 : (OnBytes.Desc.First.K4.blockAtC p4).after.lookup "free-slot" = some run4)
    (htst : ∀ e, tst e = none → freeSlotShare ww.2.2.filled e = none ∧ k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none ∧
      share4 e = none)
    (hback : ∀ o ∈ [(1, "objects"), (6, "objects")], ItemBack Lk p (phiFill tlD)
      (okFillLay p4 (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD) (tmFillLay p4 pC pD)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g)) own rdW o (Front o))
    (F₁ : S → (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Wt → Prop)
    (hFacts : ∀ κ s m En ds y cols s' x' z G,
      BatStand Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g)) κ s m En ds y cols s' x' z G →
      ∀ a v, Desc.K9.atS.get? s = some a → okFillLay p4 (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD (K9L.fixed9 (phiFill tlD) s) →
        F₁ s v → First.K8.Honest.FourFacts tlD pi8 (K9L.fixed9 (phiFill tlD) s) (Sound.dataQ own a (rdW v)))
    (hF₁ : ∀ s v, Front (4, "K8.equations") s v → F₁ s v) (Xp : Verify.Public) {mH : ℕ}
    (hmH : (2 * g == mH) = false) (Hh : Desc.K9.LinkHoles)
    (hforms : ∀ o ∈ [(2, "front"), (2, "back")], ∀ s v, Front o s v →
      Sound.formsQ (Desc.K9.readersOfLink (Desc.K9.holesAt Xp mH (2 * g) Lk) Lk) own o.1 o.2 s (rdW v))
    (sent : ℕ → List (ℕ × ℕ))
    (hformsE : ∀ s v, Front (4, "K8.equations") s v →
      Sound.formsQA sent own (Desc.K9.readersOfLink (Desc.K9.withSmall Hh) Lk) 4 "K8.equations" s (rdW v))
    (hlens : LensAt Lk p (phiFill tlD) (okFillLay p4 (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD) (tmFillLay p4 pC pD)
      (lenFillLay p4 pC pD) (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g)) ww)
    (hFront : FrontAtStandN Lk p (phiFill tlD) (okFillLay p4 (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD) (ProofFile.k8NU Bs.G₀ Xl)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links P5J.At.ps (2 * g)))
    (hVals : ValuesAtStand Lk p (phiFill tlD) (okFillLay p4 (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD) (ProofFile.k8NU Bs.G₀ Xl)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links P5J.At.ps (2 * g)))
    (h4 : K4Behind Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g)) share4 run4) :
    GivesTotalB Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g)) own rdW (Desc.K9.rowsFit p.rows) tst Front := by
  have hm : 2 * g < 25 := by omega
  have htot : TotalInBehind Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g)) own := by
    rw [hown]
    exact totalIn_paid h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm Sd
  have hs := sub_even g hg
  obtain ⟨hlk, seg, drawB, kp⟩ := tied_of_seated h hm Sd
  have seg' : SegAt (2 * g) .layers Lk := hs ▸ seg
  have e3' : Bs.G₀.built.toList[2 * g]? = some Xl := by simpa using e3
  obtain ⟨q₁, X₁, a1, a2, SL⟩ := seal_lay h O (2 * g) hm hs Lk p hlk seg drawB kp pC pD hC hD xx tlD hd
  have eq₁ : q₁ = p4 := Option.some.inj (a1.symm.trans hk)
  have eX₁ : X₁ = Xl := Option.some.inj (a2.symm.trans e3')
  rw [eq₁, eX₁] at SL
  obtain ⟨q₂, X₂, b1, b2, TK⟩ := take_lay h O (2 * g) hm hs Lk p hlk seg drawB kp pC pD tlD
  have eq₂ : q₂ = p4 := Option.some.inj (b1.symm.trans hk)
  have eX₂ : X₂ = Xl := Option.some.inj (b2.symm.trans e3')
  rw [eq₂, eX₂] at TK
  obtain ⟨X₃, c1, hK⟩ := k8At_layers h.scope h.reads O hg
  have eX₃ : X₃ = Xl := Option.some.inj (c1.symm.trans e3)
  rw [eX₃] at hK
  have hK' := hK Lk Sd.link seg'
  have hk3 := ProofFile.Honest.K8.thetaAt_layers h hg Sd.link
  have hw : ww.1 = .layers := seated_sort_lay h hg Sd
  have hKw : ProofFile.Honest.K8.K8At Lk ww.1 (ProofFile.k8ParW Zp Bs.G₀ Xl (2 * g)) := by
    rw [hw]
    exact hK'
  have hsub : (ProofFile.subsOf Zp)[2 * g]? = some ModelPart.layers := hs ▸ IM.subs_scope h.scope h.reads O (2 * g) hm
  have hk8 : (kindsBeforeBatching ModelPart.layers (2 * g == 0))[4]? = some KindName.K8 := by
    cases (2 * g == 0) <;> rfl
  have hk4 : (kindsBeforeBatching ModelPart.layers (2 * g == 0))[2]? = some KindName.K4 := by
    cases (2 * g == 0) <;> rfl
  obtain ⟨Lk', d1, X₄, d2, SO⟩ := seatOver_k8_at O (2 * g) .layers hsub 4 hk8 (by omega)
  have eL : Lk' = Lk := Option.some.inj (d1.symm.trans Sd.link)
  have eX₄ : X₄ = Xl := Option.some.inj (d2.symm.trans e3')
  rw [eL, eX₄] at SO
  obtain ⟨Lk'', f1, q₃, f2, SO4⟩ := seatOver_k4_at O (2 * g) .layers hsub hk4
  have eL' : Lk'' = Lk := Option.some.inj (f1.symm.trans Sd.link)
  have eq₃ : q₃ = p4 := Option.some.inj (f2.symm.trans hk)
  rw [eL', eq₃] at SO4
  have hoa : Lk.orderAfter = [(4, "K8.lsTail"), (2, "free-slot"), (4, "K8.tests")] := seg'.orderAfter
  obtain ⟨rLs, hLs, -⟩ := K9L.k8_lsTail_under (ProofFile.k8ParW Zp Bs.G₀ Xl (2 * g))
  obtain ⟨rTs, hTs, -⟩ := K9L.k8_tests_under (ProofFile.k8ParW Zp Bs.G₀ Xl (2 * g))
  have so0 : SeatOver Lk 0 rLs := SO 0 "K8.lsTail" rLs (by rw [hoa]; rfl) hLs
  have so1 : SeatOver Lk 1 run4 := SO4 1 "free-slot" run4 (by rw [hoa]; rfl) hr4
  have so2 : SeatOver Lk 2 rTs := SO 2 "K8.tests" rTs (by rw [hoa]; rfl) hTs
  have hlen : Lk.orderAfter.length = 3 := by rw [hoa]; rfl
  have hfour : TermsBack Lk p (phiFill tlD) (okFillLay p4 (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g)) own rdW LinkJoin.tmFour F₁ :=
    ProofFile.Honest.K8.termsBack_four _ _ own rdW SL hK'
      (ProofFile.Honest.K8.laterRun_layers_paid h hg Sd.link seg' TK) (laterDraw_at p)
      (fun q v hq hv => sized_lay q v hq hv) F₁ hFacts
  have hrest : TermsBack Lk p (phiFill tlD) (okFillLay p4 (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g)) own rdW (fun _ => K9L.tmRest pi8)
      (fun s v =>
        Sound.formsQA sent own (Desc.K9.readersOfLink (Desc.K9.withSmall Hh) Lk) 4 "K8.equations" s (rdW v)) :=
    fun κ s m En ds y cols s' x' z G St a v ha _ hF _ c hc =>
      rest_back_ahead Hh Lk (phiFill tlD) sent own (4, "K8.equations") rfl tlD pi8 (fun _ => rfl) s a ha (rdW v)
        (noAhead_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm Lk p sent own κ s m En ds y cols s' x' z G St)
        hF c hc
  have hord : Lk.order = [(1, "objects"), (1, "guests"), (2, "front"), (6, "objects"), (6, "guests"),
      (4, "K8.equations"), (2, "back")] := by
    rw [LinkJoin.split_layers seg']
    rfl
  have hcall := itemBack_lay_at (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
    (batchAt P5J.At.links P5J.At.ps (2 * g)) p own rdW Xp hmH TK
  have hback' : ∀ o ∈ Lk.order, ItemBack Lk p (phiFill tlD) (okFillLay p4 (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
      (tmFillLay p4 pC pD) (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g)) own rdW o (Front o) := by
    intro o ho
    rw [hord] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hback _ (by simp)
    · exact itemBack_guests_lay p4 1 _
    · exact termsBack_mono _ _ p own rdW (hforms _ (by simp)) (hcall _ (by simp))
    · exact hback _ (by simp)
    · exact itemBack_guests_lay p4 6 _
    · exact termsBack_mono _ _ p own rdW (fun s v hF => ⟨hF₁ s v hF, hformsE s v hF⟩)
        (itemBack_eqs_lay p4 4 F₁ _ hfour hrest)
    · exact termsBack_mono _ _ p own rdW (hforms _ (by simp)) (hcall _ (by simp))
  have FS : FrontShares Lk p (phiFill tlD) (okFillLay p4 (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD) pi8 (tmFillLay p4 pC pD)
      (lenFillLay p4 pC pD) (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g)) own rdW ww Front :=
    ⟨okFront_lay_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O hg e3 hd hk hC hD Lk p, hback', hlens,
      counts_front_seal _ _ SL ww _ hKw (fun e => absurd (hw.symm.trans e) (by decide)),
      rwFront_lay_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hE hg Lk kp tlD, htot⟩
  have K8B := k8Behind_lay (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
    (batchAt P5J.At.links P5J.At.ps (2 * g)) (p := p) seg' TK hK' hk3 hFront hVals
  exact join_layers cF Zp kk ww (Desc.K9.rowsFit p.rows) tst (k8Share (ProofFile.k8NU Bs.G₀ Xl)) share4 rLs rTs run4 p4
    (ProofFile.k8ParW Zp Bs.G₀ Xl (2 * g)) Front Sd SL (fun _ => rfl) htst FS hlen rfl hLs hTs so0
    (kindOver_lsTail _ hLs) hr4 so1 so2 (kindOver_tests _ hTs) K8B h4

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.seatOver_k4_at
#print axioms ProofFile.Honest.K9.sub_even
#print axioms ProofFile.Honest.K9.seated_sort_lay
#print axioms ProofFile.Honest.K9.givesTotalB_lay
