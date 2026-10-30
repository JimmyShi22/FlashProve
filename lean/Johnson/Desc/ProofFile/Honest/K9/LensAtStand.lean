-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/LensAtStand.lean: FOR THE ITEM "totalB": `LensAt` (Honest/K9/TotalFront.lean: at every
stand of the batching the runs' numbers of claims add up to the seat's number) AT THE FRAME's OWN THREAD AT THE
LIBRARY's HEAD, AT ALL THREE SORTS OF SEGMENT: EXCHANGED FOR ONE NAMED PUBLIC PREMISE AND EACH RUN's OWN NUMBER AT A
STAND. IMPLICATIONS. One definition, statements and proofs: calls; no goal is stated.
  `at_of_behind`   behind a yes of the batching every entry of the link's order has a run (the library's `fold_runs` at
      our `gathered_split`)
  `NumAtStand Lk p φ Ok T b f n`   A DEFINITION OF THIS FILE, a premise's form: at every stand, where the promise Ok
      holds at what is fixed in front of the draw, the number f there is n
  `seated_w_lay`   under the head, at K9's seat at a feed-forward segment: the seat's number is the segment's plan's
      nLin
  **`lensAt_att`, `lensAt_lay`, `lensAt_head`**   under the head, an opening O of the head's own form, K9's seat Sd, the
      readings (the plan at attention; the built link) and: hLE: `LensEqAsked Zp` (Johnson/Desc/K9/Honest/LensEq.lean) ·
      hlook: the lookups' entries' numbers, each a `NumAtStand` · hruns (and hjoin at the head): the sort's own runs'
      numbers ⊢ `LensAt` at the fillings of Honest/K9/TotalFill.lean, in the very form of the premise hlens of
      `givesTotalB_att`, `_lay`, `_head`
PAID INSIDE, BY CALLS: "reached" in front (the frame's `thr_reach`; the border's number: its `batch_at`) · the segment's
order (`tied_of_seated`) · every entry has a run (`at_of_behind`) · the seat's number is the plan's (`seated_w_att`,
`seated_w_lay`, `seated_w_head`) · the smallness test's share (inside the law `hlenEq_…`).
WHOSE EACH IS, by our own reading: hLE: OURS: public; a test with code · hlook: the lookups' runs' numbers: paid in
Honest/K9/LensLook.lean · hruns: at attention K5's two runs' together (attOwnB): paid in Honest/K9/LensAttPaid.lean by
that house's count; at a feed-forward segment the feed-forward kind's run's ("front": frontB); at the head the head's
kind's runs' (29, 4, 2) · hjoin: the head's join's: 1: these three are paid in Honest/K9/LensRuns.lean.
GROUND: beside the sealed library, what lies beneath Honest/K9/TotalLay.lean, and our
Johnson/Desc/K9/Honest/LensEq.lean. At the full size and the format's second hash function alone: the head's.
WHAT IS NOT CLAIMED. hLE at any public part. hlook, hruns, hjoin at any thread. That a stand is there: where there is
none all three say nothing. No member; the three are called by Honest/K9/LensLook.lean; the assemblies do not call them.
Nothing on any property.

-/
import Johnson.Desc.K9.Honest.LensEq
import Johnson.Desc.ProofFile.Honest.K9.TotalLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.StillRun (lenStill)
open VerifiableInference.Desc.First.Att (P.parCOf)
open K5Law (fsFirst fsSecond)
open VerifiableInference.Desc.Kinds.Head (parOf)
open VerifiableInference.Desc.Kinds.Head.Law (workOf fsK6 fsJoin)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.K9Asks (attOwnB frontB)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open _root_.Desc.K14.Law (seatZ secondAt)

/-- **Behind a yes of the batching every entry of the link's order has a run.** -/
theorem at_of_behind {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {s : S} {x : E}
    {z : S × Desc.K9.Part × List Claim} {G : Fork} {s' : S}
    (B : BatBehind p (claimsInBy Lk.each Lk.hear Lk.order) s x z G s') : ∀ o ∈ Lk.order, ∃ run, At Lk o run := by
  obtain ⟨t₁, -, hg, -⟩ := gathered_split p _ s x z B.gathered
  exact fold_runs Lk.each Lk.hear Lk.order ([], t₁) (z.2.2, z.1) hg

section
variable {α : Type} (Lk : Link S Claim) (p : Desc.K9.Where) (φ : S → α) (Ok : α × Option K9L.Pub9 → Prop)
  {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Claim V W X Pb) (b : ℕ)

/-- **A number at every stand**: where the promise holds at what is fixed in front of the draw, f there is n. -/
def NumAtStand (f : α × Option K9L.Pub9 → ℕ) (n : ℕ) : Prop :=
  ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
    Ok (K9L.fixed9 φ s) → f (K9L.fixed9 φ s) = n

end

/-- The seat's letter at a feed-forward segment is the plan's. -/
theorem seated_w_lay {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) {kk : ℕ} {Lk : Link S ProofFile.Cl}
    {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp (2 * g) kk Lk p w) :
    ∃ hp, (P5J.At.X Zp).G[g]? = some hp ∧ w.2.1 = hp.nLin := by
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
  have e3 : 2 * g / 2 = g := by omega
  rw [e1, e2, e3] at ht
  obtain ⟨hp, e0, e⟩ := Option.map_eq_some_iff.1 ht
  exact ⟨hp, e0, by rw [← e]⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **`LensAt` at an attention segment**, from the public test's yes and each run's own number at a stand. -/
theorem lensAt_att (hLE : LensEqAsked Zp) {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where}
    {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp (2 * g + 1) kk Lk p ww)
    {A : Attention.Plan} (hA : (P5J.At.X Zp).A[g]? = some A) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g + 1]? = some Xl) (tlD : HTailF2) (pC pD : First.Look.P)
    (hlook : ∀ on ∈ [((1, "objects"), Forest.lins A.fs), ((2, "join"), 1), ((1, "planes"), 3),
        ((6, "objects"), Forest.lins Xl.tl.f9)],
      NumAtStand Lk p (phiFill tlD) (okFillAtt A (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (batchAt P5J.At.links P5J.At.ps (2 * g + 1)) (l3All pC.lm pC.first 0 pD.first on.1) on.2)
    (hruns : NumAtStand Lk p (phiFill tlD) (okFillAtt A (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g + 1))
      (fun q => lenStill (fsFirst rdAll (P.parCOf A)) q +
        lenStill (fsSecond rdAll (P.parCOf A)) q) (attOwnB A.S)) :
    LensAt Lk p (phiFill tlD) (okFillAtt A (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD) (tmFillAtt A pC pD)
      (lenFillAtt A pC pD) (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g + 1)) ww := by
  intro κ s m En ds y cols s' x' z G St hOk
  have hm : 2 * g + 1 < 25 := by omega
  have hf : cF.blocksInOrder.length = 358 := Meaning.K2.flat_358 h.toAtMg.scope O
  have hb := batch_at.1 (2 * g + 1) (by omega)
  have hq := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by rw [hf, hb]; omega) St.thr.1
  rw [hb] at hq
  obtain ⟨-, seg, -, -⟩ := tied_of_seated h hm Sd
  have seg' : SegAt (2 * g + 1) .attention Lk := sub_odd g hg ▸ seg
  have hA' : Bs.G₀.W.A[g]? = some A := by
    rw [O.W]
    exact hA
  have hw : ww.2.1 = A.nLin := by rw [seated_w_att h hg Sd hA]
  rw [hw]
  have n1 := hlook ((1, "objects"), Forest.lins A.fs) (List.mem_cons.2 (Or.inl rfl)) κ s m En ds y cols s' x' z G St hOk
  have n2 := hlook ((2, "join"), 1) (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))) κ s m En ds y cols s' x' z
    G St hOk
  have n3 := hlook ((1, "planes"), 3)
    (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))))) κ s m En ds y cols s' x' z G St
    hOk
  have n4 := hlook ((6, "objects"), Forest.lins Xl.tl.f9)
    (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl))))))))
    κ s m En ds y cols s' x' z G St hOk
  have n5 := hruns κ s m En ds y cols s' x' z G St hOk
  have hAt := at_of_behind St.bat
  exact hlenEq_att hLE h.scope h.reads O hg hq seg' hAt rdAll (P.parCOf A) (tmFillAtt A pC pD)
    (l3All pC.lm pC.first 0 pD.first) tlD psiAll
    (fun a ha => by
      obtain rfl : a = A := Option.some.inj (ha.symm.trans hA')
      exact n1)
    (fun X₁ hX => by
      obtain rfl : X₁ = Xl := Option.some.inj (hX.symm.trans e3)
      exact n4)
    n2 n3
    (fun a ha => by
      obtain rfl : a = A := Option.some.inj (ha.symm.trans hA')
      exact n5) A hA'

/-- **`LensAt` at a feed-forward segment**, from the public test's yes and each run's own number at a stand. -/
theorem lensAt_lay (hLE : LensEqAsked Zp) {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where}
    {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp (2 * g) kk Lk p ww) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g]? = some Xl) (tlD : HTailF2) (p4 : OnBytes.Desc.First.K4.Par) (pC pD : First.Look.P)
    (hlook : ∀ on ∈ [((1, "objects"), Forest.lins Bs.G₀.W.layers.y.fo), ((6, "objects"), Forest.lins Xl.tl.f9)],
      NumAtStand Lk p (phiFill tlD) (okFillLay p4 (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (batchAt P5J.At.links P5J.At.ps (2 * g)) (l3All pC.lm pC.first 0 pD.first on.1) on.2)
    (hruns : NumAtStand Lk p (phiFill tlD) (okFillLay p4 (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g)) (K4Run.lenFront p4 (·.own)) (frontB Bs.G₀.W.layers.y g)) :
    LensAt Lk p (phiFill tlD) (okFillLay p4 (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD) (tmFillLay p4 pC pD)
      (lenFillLay p4 pC pD) (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g)) ww := by
  intro κ s m En ds y cols s' x' z G St hOk
  have hm : 2 * g < 25 := by omega
  have hf : cF.blocksInOrder.length = 358 := Meaning.K2.flat_358 h.toAtMg.scope O
  have hb := batch_at.1 (2 * g) (by omega)
  have hq := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by rw [hf, hb]; omega) St.thr.1
  rw [hb, show 14 * (2 * g) + 9 = 28 * g + 9 by omega] at hq
  obtain ⟨-, seg, -, -⟩ := tied_of_seated h hm Sd
  have seg' : SegAt (2 * g) .layers Lk := sub_even g hg ▸ seg
  obtain ⟨hp, hG, hw⟩ := seated_w_lay h hg Sd
  have hG' : Bs.G₀.W.G[g]? = some hp := by
    rw [O.W]
    exact hG
  rw [hw]
  have n1 := hlook ((1, "objects"), Forest.lins Bs.G₀.W.layers.y.fo) (List.mem_cons.2 (Or.inl rfl))
    κ s m En ds y cols s' x' z G St hOk
  have n2 := hlook ((6, "objects"), Forest.lins Xl.tl.f9) (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl))))
    κ s m En ds y cols s' x' z G St hOk
  have n3 := hruns κ s m En ds y cols s' x' z G St hOk
  have hAt := at_of_behind St.bat
  exact hlenEq_layers hLE h.scope h.reads O hg hq seg' hAt p4 (tmFillLay p4 pC pD)
    (l3All pC.lm pC.first 0 pD.first) tlD psiAll n1
    (fun X₁ hX => by
      obtain rfl : X₁ = Xl := Option.some.inj (hX.symm.trans e3)
      exact n2)
    n3 hp hG'

/-- **`LensAt` at the head's segment**, from the public test's yes and each run's own number at a stand. -/
theorem lensAt_head (hLE : LensEqAsked Zp) {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where}
    {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp 24 kk Lk p ww) {Xl : LinkH}
    (e3 : Bs.G₀.built[24]? = some Xl) (tlD : HTailF2) (pC pD : First.Look.P)
    (hlook : ∀ on ∈ [((2, "objects"), Forest.lins Bs.G₀.W.HLy.fs), ((2, "planes"), 3),
        ((7, "objects"), Forest.lins Xl.tl.f9)],
      NumAtStand Lk p (phiFill tlD) (okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (batchAt P5J.At.links P5J.At.ps 24) (l3All pC.lm pC.first 0 pD.first on.1) on.2)
    (hruns : ∀ on ∈ [("norm", 29), ("policy", 4), ("logits", 2)],
      NumAtStand Lk p (phiFill tlD) (okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (batchAt P5J.At.links P5J.At.ps 24)
        (lenStill (fsK6 Bs.G₀.W.hS (Kinds.Head.Law.readsOf Bs.G₀.W) (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) kapAll on.1))
        on.2)
    (hjoin : NumAtStand Lk p (phiFill tlD) (okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps 24)
      (lenStill (fsJoin Bs.G₀.W.hS (Kinds.Head.Law.readsOf Bs.G₀.W) (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) kapAll)) 1) :
    LensAt Lk p (phiFill tlD) (okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD) (tmFillHead Bs.G₀.W pC pD)
      (lenFillHead Bs.G₀.W pC pD) (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps 24) ww := by
  intro κ s m En ds y cols s' x' z G St hOk
  have hf : cF.blocksInOrder.length = 358 := Meaning.K2.flat_358 h.toAtMg.scope O
  have hq := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by rw [hf, batch_at.2]; omega) St.thr.1
  rw [batch_at.2] at hq
  obtain ⟨-, seg, -, -⟩ := tied_of_seated h (by omega : 24 < 25) Sd
  have hs : IM.subAt 24 = .head := by decide
  have seg' : SegAt 24 .head Lk := hs ▸ seg
  have hw : ww.2.1 = Bs.G₀.W.H.nLin := by
    rw [seated_w_head h Sd]
    exact congrArg (·.H.nLin) O.W.symm
  rw [hw]
  have n1 := hlook ((2, "objects"), Forest.lins Bs.G₀.W.HLy.fs) (List.mem_cons.2 (Or.inl rfl))
    κ s m En ds y cols s' x' z G St hOk
  have n2 := hlook ((2, "planes"), 3) (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl))))
    κ s m En ds y cols s' x' z G St hOk
  have n3 := hlook ((7, "objects"), Forest.lins Xl.tl.f9)
    (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl))))))
    κ s m En ds y cols s' x' z G St hOk
  have k1 := hruns ("norm", 29) (List.mem_cons.2 (Or.inl rfl)) κ s m En ds y cols s' x' z G St hOk
  have k2 := hruns ("policy", 4) (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl))))
    κ s m En ds y cols s' x' z G St hOk
  have k3 := hruns ("logits", 2)
    (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl))))))
    κ s m En ds y cols s' x' z G St hOk
  have k4 := hjoin κ s m En ds y cols s' x' z G St hOk
  have hAt := at_of_behind St.bat
  exact hlenEq_head hLE h.scope h.reads O hq seg' hAt Bs.G₀.W.hS (Kinds.Head.Law.readsOf Bs.G₀.W)
    (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) kapAll (tmFillHead Bs.G₀.W pC pD) (l3All pC.lm pC.first 0 pD.first) tlD psiAll
    n1
    (fun X₁ hX => by
      obtain rfl : X₁ = Xl := Option.some.inj (hX.symm.trans e3)
      exact n3)
    n2 k1 k2 k3 k4

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.at_of_behind
#print axioms ProofFile.Honest.K9.seated_w_lay
#print axioms ProofFile.Honest.K9.lensAt_att
#print axioms ProofFile.Honest.K9.lensAt_lay
#print axioms ProofFile.Honest.K9.lensAt_head
