-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TotalRows.lean: FOR THE ITEM "totalB": THE THREE ASSEMBLIES AS Honest/K9/TotalPaid.lean
HAS THEM, WITH THE PUBLIC DEBT hE (`K9Asks.RowsAsked Zp`: "the rows fit", at all 25 segments) PAID TOO, FROM THE
LIBRARY's HEAD, BY THE SMALLNESS TEST's HOUSE's THEOREM. PAID: NO NEW PREMISE AND NO NEW CONDITION COMES IN FOR IT.
IMPLICATIONS STILL. The statements are TotalPaid.lean's own, cut by program, with that binder struck; each proof is one
call of that file's theorem. No goal is stated.
  **`givesTotalB_att_rows`**   at 2 g + 1, g < 12. THREE DEBTS: htst · hFacts · hLE
  **`givesTotalB_head_rows`**   at 24. THREE DEBTS: htst · hFacts · hLE
  **`givesTotalB_lay_rows`**   at 2 g, g < 12. FOUR DEBTS: htst · hFacts · hLE · h4
The debts are counted BESIDE the three conditions on the free letter Front (hforms, hformsE, hF₁),
as Honest/K9/TotalBack.lean's head tells them: that these can be met together with
`exchange_totalB_seat`'s hfront is not shown here (`ExchangeAtS` at the item is had with neither as
a premise, at the laid Fronts `frontC` and `frontS`, over the bridge: Honest/K9/FrontLaid.lean,
TotalExchangeFree.lean).
THE PAYER: `P1K8.rowsAsked_of_head` (Johnson/P1K8R/RowsAskedOfHead.lean): from the library's head in its shorter form
(`P5J.AtMg`, which ours hands as `h.toAtMg`): `K9Asks.RowsAsked Zp`, the sealed sentence itself, with no premise beside.
WHOSE THE THREE | FOUR ARE: as Honest/K9/TotalPaid.lean's head says of hLE, htst, hFacts and h4.
GROUND: beneath this file, beside the sealed library, lie 558 files, this one among them: what lies beneath
Honest/K9/TotalPaid.lean, and eighteen more: seventeen of the smallness test's house's (Johnson/P1K8R/) and one of the
hash build's (Johnson/Desc/First/Link/Law/K9RowsParts.lean), which import these and sealed modules alone: reading
copies.
SINCE THIS FILE the row "hE" in the heads of Honest/K9/TotalAtt.lean, TotalHead.lean and
TotalLay.lean, and that name in the lists of debts in TotalLens.lean's, TotalBack.lean's and
TotalPaid.lean's, are overtaken.
WHAT IS NOT CLAIMED. Any of the debts at any thread or public part. The conditions on Front at any
Front. THAT A STAND IS THERE: where there is none all three say nothing. No member; the three are
called by Honest/K9/TotalWorth.lean alone. At the full size and the format's second hash function
alone: the head's. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.TotalPaid
import Johnson.P1K8R.RowsAskedOfHead

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

/-- **The assembly at an attention segment, hE paid too.** -/
theorem givesTotalB_att_rows {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
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
    (hLE : LensEqAsked Zp) :
    GivesTotalB Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g + 1)) own rdW (Desc.K9.rowsFit p.rows) tst Front :=
  givesTotalB_att_paid h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (P1K8.rowsAsked_of_head Z D r Zp Np cF h.toAtMg) O
    hg Sd hA e3 hd hC hD own hown rdW tst Front htst F₁ hFacts hF₁ Xp hmH Hh hforms sent hformsE hLE

/-- **The assembly at the head's segment, hE paid too.** -/
theorem givesTotalB_head_rows {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
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
    (hLE : LensEqAsked Zp) :
    GivesTotalB Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps 24) own rdW (Desc.K9.rowsFit p.rows) tst Front :=
  givesTotalB_head_paid h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (P1K8.rowsAsked_of_head Z D r Zp Np cF h.toAtMg) O
    Sd e3 hd hC hD own hown rdW tst Front htst F₁ hFacts hF₁ Hc Hh hforms sent hformsE hLE

/-- **The assembly at a feed-forward segment, hE paid too.** -/
theorem givesTotalB_lay_rows {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
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
    (h4 : K4Behind Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g)) share4 run4) :
    GivesTotalB Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g)) own rdW (Desc.K9.rowsFit p.rows) tst Front :=
  givesTotalB_lay_paid h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (P1K8.rowsAsked_of_head Z D r Zp Np cF h.toAtMg) O
    hg Sd e3 hd hk hC hD own hown rdW tst share4 Front run4 hr4 htst F₁ hFacts hF₁ Xp hmH Hh hforms sent hformsE hLE
    h4

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.givesTotalB_att_rows
#print axioms ProofFile.Honest.K9.givesTotalB_head_rows
#print axioms ProofFile.Honest.K9.givesTotalB_lay_rows
