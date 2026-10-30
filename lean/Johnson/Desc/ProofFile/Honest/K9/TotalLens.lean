-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TotalLens.lean: FOR THE ITEM "totalB": THE THREE ASSEMBLIES `givesTotalB_att`,
`givesTotalB_head`, `givesTotalB_lay` (Honest/K9/TotalAtt.lean, TotalHead.lean, TotalLay.lean) WITH THEIR PREMISE hlens
EXCHANGED FOR hLE. IMPLICATIONS. The statements are the assemblies' own, cut by program, with that one binder exchanged;
each proof is one call of the assembly at one call of the exchange. No goal is stated.
  **`givesTotalB_att_lens`**   by `lensAt_att_runs` (Honest/K9/LensAttPaid.lean). SEVEN DEBTS: hE · htst · hback ·
      hFacts · hLE · hFront · hVals
  **`givesTotalB_head_lens`**   by `lensAt_head_runs` (Honest/K9/LensRuns.lean). EIGHT DEBTS: hE · htst · hback · hFacts
      · hLE · hFront · hVals · hfold
  **`givesTotalB_lay_lens`**   by `lensAt_lay_runs` (Honest/K9/LensRuns.lean). EIGHT DEBTS: hE · htst · hback · hFacts ·
      hLE · hFront · hVals · h4
THE NEW BINDER. hLE: `LensEqAsked Zp` (Johnson/Desc/K9/Honest/LensEq.lean): OURS: a named public premise, of the kind of
hE: a test with code that no verifier asks; evaluated true at the stored full-size example alone, proved at no public
part. Every other binder, and whose it is: the assemblies' heads.
WHAT IT ADDS: nothing but Lean's own word that the exchange fits the assemblies' binder hlens.
GROUND: beside the sealed library, what lies beneath Honest/K9/LensAttPaid.lean. At the full size and the format's
second hash function alone: the head's.
WHAT IS NOT CLAIMED. Any of the debts at any thread or public part. That a stand is there: where there is none all three
say nothing. No member; the three are called by no line. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.LensAttPaid

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
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile.Honest.K8 (FrontAtStandN ValuesAtStand k8Share FoldOnce)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The assembly at an attention segment, its premise hlens exchanged.** -/
theorem givesTotalB_att_lens (hE : K9Asks.RowsAsked Zp) {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where}
    {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp (2 * g + 1) kk Lk p ww)
    {A : Attention.Plan} (hA : (P5J.At.X Zp).A[g]? = some A) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g + 1]? = some Xl) {xx : First.Look.Place} {tlD : HTailF2}
    (hd : First.Look.digAt (P5J.At.X Zp) (2 * g + 1) = some (xx, tlD)) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) (2 * g + 1) false = some pC)
    (hD : placeAt (P5J.At.X Zp) (2 * g + 1) true = some pD) (own : List (ℕ × ℕ))
    (hown : own = (P5J.At.N Zp cF).group (2 * g + 1))
    (rdW : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Wt → ℕ × ℕ → Sound.MsgQ)
    (tst : S → Option String)
    (Front : ℕ × String → S → (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Wt → Prop)
    (htst : ∀ e, tst e = none → freeSlotShare ww.2.2.filled e = none ∧ k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none)
    (hback : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ItemBack Lk p (phiFill tlD)
      (okFillAtt A (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD) (tmFillAtt A pC pD)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g + 1)) own rdW o (Front o))
    (F₁ : S → (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Wt → Prop)
    (hFacts : ∀ κ s m En ds y cols s' x' z G,
      BatStand Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g + 1)) κ s m En ds y cols s' x' z G →
      ∀ a v, Desc.K9.atS.get? s = some a → okFillAtt A (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD (K9L.fixed9 (phiFill tlD) s) →
        F₁ s v → First.K8.Honest.FourFacts tlD pi8 (K9L.fixed9 (phiFill tlD) s) (Sound.dataQ own a (rdW v)))
    (hF₁ : ∀ s v, Front (4, "K8.equations") s v → F₁ s v) (Xp : Verify.Public) {mH : ℕ}
    (hmH : (2 * g + 1 == mH) = false) (Hh : Desc.K9.LinkHoles)
    (hforms : ∀ o ∈ [(2, "first"), (2, "keys"), (2, "second")], ∀ s v, Front o s v →
      Sound.formsQ (Desc.K9.readersOfLink (Desc.K9.holesAt Xp mH (2 * g + 1) Lk) Lk) own o.1 o.2 s (rdW v))
    (sent : ℕ → List (ℕ × ℕ))
    (hformsE : ∀ s v, Front (4, "K8.equations") s v →
      Sound.formsQA sent own (Desc.K9.readersOfLink (Desc.K9.withSmall Hh) Lk) 4 "K8.equations" s (rdW v))
    (hLE : LensEqAsked Zp)
    (hFront : FrontAtStandN Lk p (phiFill tlD) (okFillAtt A (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD) (ProofFile.k8NU Bs.G₀ Xl)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links P5J.At.ps (2 * g + 1)))
    (hVals : ValuesAtStand Lk p (phiFill tlD) (okFillAtt A (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD) (ProofFile.k8NU Bs.G₀ Xl)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links P5J.At.ps (2 * g + 1))) :
    GivesTotalB Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g + 1)) own rdW (Desc.K9.rowsFit p.rows) tst Front :=
  givesTotalB_att h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hE O hg Sd hA e3 hd hC hD own hown rdW tst Front htst
    hback F₁ hFacts hF₁ Xp hmH Hh hforms sent hformsE
    (lensAt_att_runs h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hLE O hg Sd hA e3 hd hC hD)
    hFront hVals

/-- **The assembly at the head's segment, its premise hlens exchanged.** -/
theorem givesTotalB_head_lens (hE : K9Asks.RowsAsked Zp) {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
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
    (hLE : LensEqAsked Zp)
    (hFront : FrontAtStandN Lk p (phiFill tlD) (okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD) (ProofFile.k8NU Bs.G₀ Xl)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links P5J.At.ps 24))
    (hVals : ValuesAtStand Lk p (phiFill tlD) (okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD) (ProofFile.k8NU Bs.G₀ Xl)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links P5J.At.ps 24))
    (hfold : FoldOnce Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps 24)) :
    GivesTotalB Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps 24) own rdW (Desc.K9.rowsFit p.rows) tst Front :=
  givesTotalB_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hE O Sd e3 hd hC hD own hown rdW tst Front htst hback F₁
    hFacts hF₁ Hc Hh hforms sent hformsE
    (lensAt_head_runs h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hLE O Sd e3 hd hC hD)
    hFront hVals hfold

/-- **The assembly at a feed-forward segment, its premise hlens exchanged.** -/
theorem givesTotalB_lay_lens (hE : K9Asks.RowsAsked Zp) {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
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
    (hLE : LensEqAsked Zp)
    (hFront : FrontAtStandN Lk p (phiFill tlD) (okFillLay p4 (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD) (ProofFile.k8NU Bs.G₀ Xl)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links P5J.At.ps (2 * g)))
    (hVals : ValuesAtStand Lk p (phiFill tlD) (okFillLay p4 (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD) (ProofFile.k8NU Bs.G₀ Xl)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links P5J.At.ps (2 * g)))
    (h4 : K4Behind Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g)) share4 run4) :
    GivesTotalB Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g)) own rdW (Desc.K9.rowsFit p.rows) tst Front :=
  givesTotalB_lay h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hE O hg Sd e3 hd hk hC hD own hown rdW tst share4 Front
    run4 hr4 htst hback F₁ hFacts hF₁ Xp hmH Hh hforms sent hformsE
    (lensAt_lay_runs h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hLE O hg Sd e3 hd hk hC hD)
    hFront hVals h4

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.givesTotalB_att_lens
#print axioms ProofFile.Honest.K9.givesTotalB_head_lens
#print axioms ProofFile.Honest.K9.givesTotalB_lay_lens
