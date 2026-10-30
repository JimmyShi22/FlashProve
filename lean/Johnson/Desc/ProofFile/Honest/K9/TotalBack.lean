-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TotalBack.lean: FOR THE ITEM "totalB": THE THREE ASSEMBLIES AS Honest/K9/TotalLens.lean
HAS THEM, WITH THEIR DEBT hback (`ItemBack` at the lookups' entries) EXCHANGED TOO: FOR A WIDER CONDITION ON THE FREE
LETTER Front. EXCHANGED, NOT PAID. IMPLICATIONS. The statements are TotalLens.lean's own, cut by program, with the
binder hback struck and the list of the binder hforms made longer; each proof is one call of that file's theorem. The
debts are counted below BESIDE the three conditions on Front, of which hforms grew. No goal is stated.
  **`givesTotalB_att_back`**   by `itemBack_look_att` (Honest/K9/BackLook.lean). hforms at seven entries: "first",
      "keys", "second", AND (1, "objects"), (2, "join"), (1, "planes"), (6, "objects"). SIX DEBTS: hE · htst · hFacts ·
      hLE · hFront · hVals
  **`givesTotalB_head_back`**   by `itemBack_look_head` (Honest/K9/BackLookHead.lean). hforms at eight: "norm",
      "policy", "logits", "the merge", (3, "join"), AND (2, "objects"), (2, "planes"), (7, "objects"). SEVEN DEBTS: hE ·
      htst · hFacts · hLE · hFront · hVals · hfold
  **`givesTotalB_lay_back`**   by `itemBack_look_lay` (Honest/K9/BackLook.lean). hforms at four: "front", "back", AND
      (1, "objects"), (6, "objects"). SEVEN DEBTS: hE · htst · hFacts · hLE · hFront · hVals · h4
WHAT THE EXCHANGE COSTS. hforms says of the free letter Front: at each listed entry o, Front o s v
gives the table's sentence "forms" (`formsQ`) at o, s and the witness's tables, at the same readers
as before. It was asked at our callers' entries; now it is asked at the lookups' too: at every entry
of the order but the two "guests" and "K8.equations" (hformsE's). Front bites only under
`exchange_totalB_seat`'s premise hfront (Honest/K9/TotalExchangeSeat.lean): the open items' meanings
give Front at every entry of the order. THAT hfront CAN BE MET TOGETHER WITH hforms, THE WIDER OR
THE NARROWER AT OUR OWN ENTRIES, IS NOT SHOWN HERE (`ExchangeAtS` at the item is had with neither as
a premise, at the laid Fronts `frontC` and `frontS`, over the bridge: Honest/K9/FrontLaid.lean,
TotalExchangeFree.lean). So the lookups' nine entries now stand as our callers' entries have stood
since Honest/K9/TotalAtt.lean: under hforms. By our reading of the library's `mgAll_forms`
(Johnson/Desc/Sound/MgAll.lean) its meaning of an item "forms" says `formsQ` at each entry of that
item's runs at which it does not look ahead: whether the lookups' entries stand among the runs of
the items that are open at the batching we have not held.
SINCE THIS FILE the row "hback: … the lookups'" in the heads of Honest/K9/TotalAtt.lean,
TotalHead.lean, TotalLay.lean and TotalLens.lean, and "What is left of the orders: the lookups' nine
entries" in Honest/K9/BackAt.lean's, are overtaken so far.
GROUND: beside the sealed library, what lies beneath Honest/K9/TotalLens.lean and BackLookHead.lean. At the full size
and the format's second hash function alone: the head's.
WHAT IS NOT CLAIMED. Any of the debts at any thread or public part. The conditions on Front at any
Front. That a stand is there: where there is none all three say nothing. No member; the three are
called by Honest/K9/TotalPaid.lean alone. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.TotalLens
import Johnson.Desc.ProofFile.Honest.K9.BackLookHead

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

/-- **The assembly at an attention segment, its debt hback exchanged too.** -/
theorem givesTotalB_att_back (hE : K9Asks.RowsAsked Zp) {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
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
    (F₁ : S → (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Wt → Prop)
    (hFacts : ∀ κ s m En ds y cols s' x' z G,
      BatStand Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g + 1)) κ s m En ds y cols s' x' z G →
      ∀ a v, Desc.K9.atS.get? s = some a → okFillAtt A (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD (K9L.fixed9 (phiFill tlD) s) →
        F₁ s v → First.K8.Honest.FourFacts tlD pi8 (K9L.fixed9 (phiFill tlD) s) (Sound.dataQ own a (rdW v)))
    (hF₁ : ∀ s v, Front (4, "K8.equations") s v → F₁ s v) (Xp : Verify.Public) {mH : ℕ}
    (hmH : (2 * g + 1 == mH) = false) (Hh : Desc.K9.LinkHoles)
    (hforms : ∀ o ∈ [(2, "first"), (2, "keys"), (2, "second")] ++
      [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ s v, Front o s v →
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
      (batchAt P5J.At.links P5J.At.ps (2 * g + 1)) own rdW (Desc.K9.rowsFit p.rows) tst Front := by
  have hlk := (tied_of_seated h (by omega : 2 * g + 1 < 25) Sd).1
  exact givesTotalB_att_lens h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hE O hg Sd hA e3 hd hC hD own hown rdW tst
    Front htst
    (fun o ho => termsBack_mono _ _ p own rdW (hforms o (List.mem_append_right _ ho))
      (itemBack_look_att _ _ p own rdW h O hg hlk hA _ tlD hC pD Xp hmH o ho))
    F₁ hFacts hF₁ Xp hmH Hh (fun o ho => hforms o (List.mem_append_left _ ho)) sent hformsE hLE hFront hVals

/-- **The assembly at the head's segment, its debt hback exchanged too.** -/
theorem givesTotalB_head_back (hE : K9Asks.RowsAsked Zp) {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
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
    (F₁ : S → (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Wt → Prop)
    (hFacts : ∀ κ s m En ds y cols s' x' z G,
      BatStand Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps 24) κ s m En ds y cols s' x' z G →
      ∀ a v, Desc.K9.atS.get? s = some a →
        okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD (K9L.fixed9 (phiFill tlD) s) →
        F₁ s v → First.K8.Honest.FourFacts tlD pi8 (K9L.fixed9 (phiFill tlD) s) (Sound.dataQ own a (rdW v)))
    (hF₁ : ∀ s v, Front (5, "K8.equations") s v → F₁ s v) (Hc Hh : Desc.K9.LinkHoles)
    (hforms : ∀ o ∈ [(3, "norm"), (3, "policy"), (3, "logits"), (8, "the merge"), (3, "join")] ++
      [(2, "objects"), (2, "planes"), (7, "objects")], ∀ s v,
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
      (batchAt P5J.At.links P5J.At.ps 24) own rdW (Desc.K9.rowsFit p.rows) tst Front := by
  have hlk := (tied_of_seated h (by omega : 24 < 25) Sd).1
  exact givesTotalB_head_lens h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hE O Sd e3 hd hC hD own hown rdW tst Front htst
    (fun o ho => termsBack_mono _ _ p own rdW (hforms o (List.mem_append_right _ ho))
      (itemBack_look_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O hlk p own rdW _ tlD hC pD Hc o ho))
    F₁ hFacts hF₁ Hc Hh (fun o ho => hforms o (List.mem_append_left _ ho)) sent hformsE hLE hFront hVals hfold

/-- **The assembly at a feed-forward segment, its debt hback exchanged too.** -/
theorem givesTotalB_lay_back (hE : K9Asks.RowsAsked Zp) {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
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
    (F₁ : S → (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Wt → Prop)
    (hFacts : ∀ κ s m En ds y cols s' x' z G,
      BatStand Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g)) κ s m En ds y cols s' x' z G →
      ∀ a v, Desc.K9.atS.get? s = some a → okFillLay p4 (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD (K9L.fixed9 (phiFill tlD) s) →
        F₁ s v → First.K8.Honest.FourFacts tlD pi8 (K9L.fixed9 (phiFill tlD) s) (Sound.dataQ own a (rdW v)))
    (hF₁ : ∀ s v, Front (4, "K8.equations") s v → F₁ s v) (Xp : Verify.Public) {mH : ℕ}
    (hmH : (2 * g == mH) = false) (Hh : Desc.K9.LinkHoles)
    (hforms : ∀ o ∈ [(2, "front"), (2, "back")] ++ [(1, "objects"), (6, "objects")], ∀ s v, Front o s v →
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
      (batchAt P5J.At.links P5J.At.ps (2 * g)) own rdW (Desc.K9.rowsFit p.rows) tst Front := by
  have hlk := (tied_of_seated h (by omega : 2 * g < 25) Sd).1
  exact givesTotalB_lay_lens h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hE O hg Sd e3 hd hk hC hD own hown rdW tst
    share4 Front run4 hr4 htst
    (fun o ho => termsBack_mono _ _ p own rdW (hforms o (List.mem_append_right _ ho))
      (itemBack_look_lay _ _ p own rdW h hg hlk p4 _ tlD pC pD Xp hmH o ho))
    F₁ hFacts hF₁ Xp hmH Hh (fun o ho => hforms o (List.mem_append_left _ ho)) sent hformsE hLE hFront hVals h4

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.givesTotalB_att_back
#print axioms ProofFile.Honest.K9.givesTotalB_head_back
#print axioms ProofFile.Honest.K9.givesTotalB_lay_back
