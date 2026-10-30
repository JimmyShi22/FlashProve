-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TotalFill.lean: FOR THE ITEM "totalB": THE ONE NAMED FILLING OF THE LETTERS AT EACH
SORT OF SEGMENT OF THE WRITTEN DESCRIPTION: THE SEALED LIBRARY's OWN CONSTANTS; AND `SealLaw`
(Honest/K9/TotalFront.lean) THERE, UNDER THE LIBRARY's HEAD. Definitions, and three theorems over the library's laws;
no goal is stated. WHY. `SealLaw` at letters t3, l3, Kx that are free says too little of them: the library's law on a
run sees a run's terms through their polynomial alone, and a promise that nothing meets makes every law on a run hold
for nothing. So a sentence of Honest/K9/TotalFront.lean at free letters could be false, or be proved by two proofs
at letters that never meet. HERE THE LETTERS ARE LAID AS THE LIBRARY ITSELF LAYS THEM where it joins the batching's law
at the 25 segments (Johnson/P5J/K09LastC.lean, `layersLeftC_at`; Johnson/P5J/K09EndC.lean, `attLeftC_at`,
`headLeftC_at`): ψ := `psiAll` · u := tlD · the lookups' terms and numbers: `t3All`, `l3All` at the two places pC, pD
of the segment's lookups, with 0 for the third number · the callers' three worths: 0 at a feed-forward segment; `bvAtt
A`, `pvAtt A`, `kvAtt A` at an attention segment; `bvHead`, `pvHead` and 0 at the head's · Kx := `kxAll3`, `kxAtt`,
`kxHead` there.
  `phiFill tlD`      φ, at all three sorts · π is `pi8`
  `okFillLay`, `tmFillLay`, `lenFillLay`   Ok, tmOf, lenOf at a feed-forward segment: of p4 (that kind's numbers), nU,
      tlD, pC, pD
  `okFillAtt`, `tmFillAtt`, `lenFillAtt`   at an attention segment: of its plan A, nU, tlD, pC, pD
  `okFillHead`, `tmFillHead`, `lenFillHead`   at the head's segment: of the public parameters W, nU, tlD, pC, pD
  **`seal_lay`**, **`seal_att`**, **`seal_head`**   UNDER THE LIBRARY's HEAD `P5J.AtMgA` at the older hash, the opening
      of the description, letters L, p that sit at the segment (what the head's data list as the segment; its two
      orders; that its batching is a draw with one move behind; K9's numbers), AND THE THREE PINS: pC and pD are what
      `placeAt` answers at the segment for its two lookups, tlD what `digAt` answers there: there are the sort's own
      numbers, READ OFF THE PUBLIC PARAMETERS BY THE EQUATIONS STATED, such that `SealLaw` holds at this filling
WHAT PINS EACH LETTER. p4, A, X: the equations in the three theorems · pC, pD: `placeAt` · tlD: `digAt` · nU :=
`ProofFile.k8NU Bs.G₀ X`. THE PROOFS SPEND ONE OF THE THREE PINS AT MOST (the first place's, at two sorts): `SealLaw` holds
at other places and other tlD too; THE PINS STAND IN THE STATEMENTS SO THAT EVERY HOUSE PROVES ITS SENTENCE AT THE
SAME LETTERS: φ, Ok and u stand in every sentence of Honest/K9/TotalFront.lean, and at a wrong place or tlD the
promise may be met by nothing. The library's own payer of the promise takes all three. own and rdW are not letters of
`SealLaw`: at the library's meaning they are the segment's group of messages and the witness's tables by seat
(Johnson/Desc/Sound/MgAll.lean, `mgAll_totalB`): not laid here.
On a member: the head is met under four premises on the public files, at D := dpZ Z and r := theProofRun (asDescriptionFiles Z)
alone (the library's `P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean); no member of what stands beside it
here is shown. The definitions are spent by Honest/K9/TotalItems.lean; the three theorems are called by no line.
WHAT IS NOT CLAIMED. The four premises under which the head is met. Any sentence of Honest/K9/TotalFront.lean at this
filling. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.TotalSeal
import Johnson.LPFK9R.LayersOwesWhole
import Johnson.LPFK9R.OwesAtLetters
import Johnson.Desc.First.Link.Law.SortLetters3
import Johnson.Desc.First.Link.Law.SortLetters4

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.First.Att (P.parCOf)
open VerifiableInference.Desc.Kinds.Head (parOf)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open VerifiableInference.OnPublicFiles (bvAtt pvAtt kvAtt bvHead pvHead)

/-- φ at all three sorts. -/
noncomputable abbrev phiFill (tlD : HTailF2) : S → Phi BetaAll := phiAll tlD psiAll

/-! ## A feed-forward segment -/

/-- Ok. -/
def okFillLay (p4 : OnBytes.Desc.First.K4.Par) (nU : Array ℕ) (tlD : HTailF2) (pC pD : First.Look.P)
    (q : Phi BetaAll × Option Pub9) : Prop :=
  OkLayers p4 nU tlD q ∧ kxAll3 pC.lm pC.first 0 pD.first q

/-- tmOf. -/
noncomputable def tmFillLay (p4 : OnBytes.Desc.First.K4.Par) (pC pD : First.Look.P) :
    ℕ × String → ℕ → Phi BetaAll × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E) :=
  tmL p4 entUnit tmFour
    (t3All pC.lm pC.first 0 pD.first (fun _ _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0))

/-- lenOf. -/
noncomputable def lenFillLay (p4 : OnBytes.Desc.First.K4.Par) (pC pD : First.Look.P) :
    ℕ × String → Phi BetaAll × Option Pub9 → ℕ :=
  lenL p4 (l3All pC.lm pC.first 0 pD.first)

/-! ## An attention segment -/

/-- Ok. -/
def okFillAtt (A : Attention.Plan) (nU : Array ℕ) (tlD : HTailF2) (pC pD : First.Look.P)
    (q : Phi BetaAll × Option Pub9) : Prop :=
  OkAtt rdAll (P.parCOf A) nU tlD q ∧ kxAtt pC.lm pC.first 0 pD.first (P.parCOf A) nU q

/-- tmOf. -/
noncomputable def tmFillAtt (A : Attention.Plan) (pC pD : First.Look.P) :
    ℕ × String → ℕ → Phi BetaAll × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E) :=
  tmA rdAll (P.parCOf A) entUnit tmFour (t3All pC.lm pC.first 0 pD.first (bvAtt A) (pvAtt A) (kvAtt A))

/-- lenOf. -/
noncomputable def lenFillAtt (A : Attention.Plan) (pC pD : First.Look.P) :
    ℕ × String → Phi BetaAll × Option Pub9 → ℕ :=
  lenA rdAll (P.parCOf A) (l3All pC.lm pC.first 0 pD.first)

/-! ## The head's segment -/

/-- Ok. -/
def okFillHead (Wp : Verify.Public) (nU : Array ℕ) (tlD : HTailF2) (pC pD : First.Look.P)
    (q : Phi BetaAll × Option Pub9) : Prop :=
  OkHead Wp.hS (Kinds.Head.Law.readsOf Wp) (parOf Wp.hS (workOf Wp)) kapAll nU tlD q ∧
    kxHead pC.lm pC.first 0 pD.first (Kinds.Head.Law.readsOf Wp) nU q

/-- tmOf. -/
noncomputable def tmFillHead (Wp : Verify.Public) (pC pD : First.Look.P) :
    ℕ × String → ℕ → Phi BetaAll × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E) :=
  tmH Wp.hS (Kinds.Head.Law.readsOf Wp) (parOf Wp.hS (workOf Wp)) kapAll entUnit tmFour
    (t3All pC.lm pC.first 0 pD.first (bvHead (Kinds.Head.Law.readsOf Wp)) (pvHead (Kinds.Head.Law.readsOf Wp))
      (fun _ _ _ => 0))

/-- lenOf. -/
noncomputable def lenFillHead (Wp : Verify.Public) (pC pD : First.Look.P) :
    ℕ × String → Phi BetaAll × Option Pub9 → ℕ :=
  lenH Wp.hS (Kinds.Head.Law.readsOf Wp) (parOf Wp.hS (workOf Wp)) kapAll (l3All pC.lm pC.first 0 pD.first)

/-! ## `SealLaw` at the filling, under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)} {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- **At a feed-forward segment.** -/
theorem seal_lay (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (m : ℕ) (hm : m < 25)
    (hs : IM.subAt m = .layers) (L : Link S ProofFile.Cl) (p : Desc.K9.Where) (hlk : h.𝔇.lk m = some L)
    (seg : SegAt m (IM.subAt m) L)
    (drawB : DrawMoves Desc.K9.atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp m = some p) (pC pD : First.Look.P) (_ : placeAt (P5J.At.X Zp) m false = some pC)
    (_ : placeAt (P5J.At.X Zp) m true = some pD) (xx : First.Look.Place) (tlD : HTailF2)
    (_ : First.Look.digAt (P5J.At.X Zp) m = some (xx, tlD)) :
    ∃ p4 X, LPFK9.k4ParAt Zp Bs.G₀ m = some p4 ∧ Bs.G₀.built.toList[m]? = some X ∧
      SealLaw .layers m L p (phiFill tlD) (okFillLay p4 (ProofFile.k8NU Bs.G₀ X) tlD pC pD) (ProofFile.k8NU Bs.G₀ X) tlD pi8
        (tmFillLay p4 pC pD) (lenFillLay p4 pC pD) := by
  obtain ⟨p4, X, e1, e2, Wh⟩ := LPFK9.layersOwesC_whole h O m hm hs L p hlk seg drawB kp
  exact ⟨p4, X, e1, e2, sealLaw_layers (Wh (kxAll3 pC.lm pC.first 0 pD.first) pC.lm pC.first 0 pD.first
    (fun _ _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) tlD tlD (fun _ hq => hq.1))⟩

/-- **At an attention segment.** -/
theorem seal_att (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) {g : ℕ} (hg : g < 12)
    (hs : IM.subAt (2 * g + 1) = .attention) (L : Link S ProofFile.Cl) (p : Desc.K9.Where)
    (hlk : h.𝔇.lk (2 * g + 1) = some L) (seg : SegAt (2 * g + 1) (IM.subAt (2 * g + 1)) L)
    (drawB : DrawMoves Desc.K9.atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp (2 * g + 1) = some p) (pC pD : First.Look.P)
    (hC : placeAt (P5J.At.X Zp) (2 * g + 1) false = some pC) (_ : placeAt (P5J.At.X Zp) (2 * g + 1) true = some pD)
    (xx : First.Look.Place) (tlD : HTailF2) (_ : First.Look.digAt (P5J.At.X Zp) (2 * g + 1) = some (xx, tlD)) :
    ∃ A X, Bs.G₀.W.A[g]? = some A ∧ Bs.G₀.built[2 * g + 1]? = some X ∧
      SealLaw .attention (2 * g + 1) L p (phiFill tlD) (okFillAtt A (ProofFile.k8NU Bs.G₀ X) tlD pC pD) (ProofFile.k8NU Bs.G₀ X) tlD
        pi8 (tmFillAtt A pC pD) (lenFillAtt A pC pD) := by
  obtain ⟨A, X, hA, e3, Wh⟩ := LPFK9.attOwesC_g h O hg hs L p hlk seg drawB kp
  exact ⟨A, X, hA, e3, sealLaw_att (Wh (kxAtt pC.lm pC.first 0 pD.first (P.parCOf A) (ProofFile.k8NU Bs.G₀ X)) pC.lm
    pC.first 0 pD.first tlD tlD kxAtt_k3 kxAtt_planes
    (fun pl e => by obtain rfl := Option.some.inj (hC.symm.trans e); rfl))⟩

/-- **At the head's segment.** -/
theorem seal_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (hs : IM.subAt 24 = .head)
    (L : Link S ProofFile.Cl) (p : Desc.K9.Where) (hlk : h.𝔇.lk 24 = some L) (seg : SegAt 24 (IM.subAt 24) L)
    (drawB : DrawMoves Desc.K9.atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp 24 = some p) (pC pD : First.Look.P)
    (hC : placeAt (P5J.At.X Zp) 24 false = some pC) (_ : placeAt (P5J.At.X Zp) 24 true = some pD)
    (xx : First.Look.Place) (tlD : HTailF2) (_ : First.Look.digAt (P5J.At.X Zp) 24 = some (xx, tlD)) :
    ∃ X, Bs.G₀.built[24]? = some X ∧
      SealLaw .head 24 L p (phiFill tlD) (okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ X) tlD pC pD) (ProofFile.k8NU Bs.G₀ X) tlD pi8
        (tmFillHead Bs.G₀.W pC pD) (lenFillHead Bs.G₀.W pC pD) := by
  obtain ⟨X, e3, Wh⟩ := LPFK9.headOwesC_24 h O hs L p hlk seg drawB kp
  exact ⟨X, e3, sealLaw_head (Wh
    (kxHead pC.lm pC.first 0 pD.first (Kinds.Head.Law.readsOf Bs.G₀.W) (ProofFile.k8NU Bs.G₀ X)) pC.lm pC.first 0 pD.first
    (fun _ _ _ => 0) tlD tlD kxHead_k3 kxHead_planes
    (fun pl e => by obtain rfl := Option.some.inj (hC.symm.trans e); rfl))⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.seal_lay
#print axioms ProofFile.Honest.K9.seal_att
#print axioms ProofFile.Honest.K9.seal_head
