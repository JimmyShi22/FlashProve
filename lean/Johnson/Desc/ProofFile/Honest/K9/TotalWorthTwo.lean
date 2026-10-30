-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TotalWorthTwo.lean: FOR THE ITEM "totalB": THE THREE ASSEMBLIES OF
Honest/K9/TotalWorth.lean WITH THEIR TWO NAMED PREMISES hCell AND hMask PAID, UNDER THE HEAD, BY THE SMALLNESS TEST's
HOUSE's THEOREMS. PAID: NO NEW PREMISE COMES IN FOR THEM. SO WHAT WAS THE DEBT hFacts NOW HANGS ON ONE CONDITION ON THE
FREE LETTER Front ALONE: hF₁, AT THE LIBRARY's `WorthTwo`: WHICH NOBODY PAYS. IMPLICATIONS STILL. The statements are
TotalWorth.lean's own, cut by program, with the two binders struck. No definition is made; no prover is in this file; no
goal is stated.
  **`givesTotalB_att_two`**   at 2 g + 1, g < 12. DEBTS: htst · hLE
  **`givesTotalB_head_two`**   at 24. DEBTS: htst · hLE
  **`givesTotalB_lay_two`**   at 2 g, g < 12. DEBTS: htst · hLE · h4
BY: that house's `cellOkR_at_stand`, `maskOkR_at_stand` (Honest/K8/FourFactsOfWorthTwo.lean): at every stand of the
frame's own thread at the head, in front of each of the 25 batchings, at every part a of its state: the library's
`CellOkR`, `MaskOkR` at the head's data's letters and at own := `h.𝔇.N.group l` · our binder hown and `own_at_head`
(Honest/K9/OwnAtHead.lean), which is called here: our own is that.
BESIDE THE DEBTS, THREE CONDITIONS ON THE FREE LETTER Front: hforms, hformsE (at the library's
reader `rdC`) and hF₁ (`Front` at "K8.equations" gives `WorthTwo` … s v): that these can be met
together with `exchange_totalB_seat`'s hfront is not shown here (`ExchangeAtS` at the item is had
with neither as a premise, at the laid Fronts `frontC` and `frontS`, over the bridge:
Honest/K9/FrontLaid.lean, TotalExchangeFree.lean).
WHERE THE WITNESS STANDS: as in Honest/K9/TotalWorth.lean: v under "for all" throughout; the two
premises struck here read none.
GROUND: beneath this file, beside the sealed library, lie 573 files, this one among them: what lies beneath
Honest/K9/TotalWorth.lean, Honest/K9/OwnAtHead.lean, and four more of the smallness test's house's: reading copies, all
but ours.
WHAT IS NOT CLAIMED. Any of the debts at any thread or public part. The conditions on Front at any
Front. THAT A STAND IS THERE: where there is none all three say nothing. No member; the three are
called by Honest/K9/FrontLaid.lean alone. At the full size and the format's second hash function
alone: the head's. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.TotalWorth
import Johnson.Desc.ProofFile.Honest.K9.OwnAtHead
import Johnson.Desc.ProofFile.Honest.K8.FourFactsOfWorthTwo

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

/-- **The assembly at an attention segment, with hCell and hMask paid.** -/
theorem givesTotalB_att_two {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where}
    {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp (2 * g + 1) kk Lk p ww) {A : Attention.Plan}
    (hA : (P5J.At.X Zp).A[g]? = some A) {Xl : LinkH} (e3 : Bs.G₀.built[2 * g + 1]? = some Xl) {xx : First.Look.Place}
    {tlD : HTailF2} (hd : First.Look.digAt (P5J.At.X Zp) (2 * g + 1) = some (xx, tlD)) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) (2 * g + 1) false = some pC) (hD : placeAt (P5J.At.X Zp) (2 * g + 1) true = some pD)
    (own : List (ℕ × ℕ)) (hown : own = (P5J.At.N Zp cF).group (2 * g + 1)) (tst : S → Option String)
    (Front : ℕ × String → S → (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Wt → Prop)
    (htst : ∀ e, tst e = none → freeSlotShare ww.2.2.filled e = none ∧ k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none)
    (hF₁ : ∀ s v, Front (4, "K8.equations") s v → LinkJoin.WorthTwo S.fork? LinkJoin.heardDig xx tlD h.𝔇.sent
      h.𝔇.l3.rad (fun j => h.𝔇.l3.seat xx.link true j.1) h.𝔇.l3.arr s v) (Xp : Verify.Public) {mH : ℕ}
    (hmH : (2 * g + 1 == mH) = false) (Hh : Desc.K9.LinkHoles)
    (hforms : ∀ o ∈ [(2, "first"), (2, "keys"), (2, "second")] ++ [(1, "objects"), (2, "join"), (1, "planes"), (6,
      "objects")], ∀ s v, Front o s v → Sound.formsQ (Desc.K9.readersOfLink (Desc.K9.holesAt Xp mH (2 * g + 1) Lk) Lk)
      own o.1 o.2 s (LinkJoin.rdC h.𝔇.cs h.𝔇.arr h.𝔇.ms v)) (sent : ℕ → List (ℕ × ℕ))
    (hformsE : ∀ s v, Front (4, "K8.equations") s v → Sound.formsQA sent own (Desc.K9.readersOfLink (Desc.K9.withSmall
      Hh) Lk) 4 "K8.equations" s (LinkJoin.rdC h.𝔇.cs h.𝔇.arr h.𝔇.ms v)) (hLE : LensEqAsked Zp) :
    GivesTotalB Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links P5J.At.ps
      (2 * g + 1)) own (fun v => LinkJoin.rdC h.𝔇.cs h.𝔇.arr h.𝔇.ms v) (Desc.K9.rowsFit p.rows) tst Front := by
  have hm : 2 * g + 1 < 25 := by omega
  exact givesTotalB_att_worth h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O hg Sd hA e3 hd hC hD own hown tst Front
    htst
    (fun κ s m En ds y cols s' x' z G St a ha => by
      rw [hown, ← own_at_head h]
      exact ProofFile.Honest.K8.cellOkR_at_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm hd
        κ s m En ds y cols s' x' z G St a ha)
    (fun κ s m En ds y cols s' x' z G St a ha => by
      rw [hown, ← own_at_head h]
      exact ProofFile.Honest.K8.maskOkR_at_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm hd
        κ s m En ds y cols s' x' z G St a ha)
    hF₁ Xp hmH Hh hforms sent hformsE hLE

/-- **The assembly at the head's segment, with hCell and hMask paid.** -/
theorem givesTotalB_head_two {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree cF Zp 24 kk Lk p ww) {Xl : LinkH} (e3 : Bs.G₀.built[24]? = some Xl) {xx : First.Look.Place}
    {tlD : HTailF2} (hd : First.Look.digAt (P5J.At.X Zp) 24 = some (xx, tlD)) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) 24 false = some pC) (hD : placeAt (P5J.At.X Zp) 24 true = some pD)
    (own : List (ℕ × ℕ)) (hown : own = (P5J.At.N Zp cF).group 24) (tst : S → Option String)
    (Front : ℕ × String → S → (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Wt → Prop)
    (htst : ∀ e, tst e = none → freeSlotShare ww.2.2.filled e = none ∧ k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none)
    (hF₁ : ∀ s v, Front (5, "K8.equations") s v → LinkJoin.WorthTwo S.fork? LinkJoin.heardDig xx tlD h.𝔇.sent
      h.𝔇.l3.rad (fun j => h.𝔇.l3.seat xx.link true j.1) h.𝔇.l3.arr s v) (Hc Hh : Desc.K9.LinkHoles)
    (hforms : ∀ o ∈ [(3, "norm"), (3, "policy"), (3, "logits"), (8, "the merge"), (3, "join")] ++ [(2, "objects"), (2,
      "planes"), (7, "objects")], ∀ s v, Front o s v → Sound.formsQ (Desc.K9.readersOfLink Hc Lk) own o.1 o.2 s
      (LinkJoin.rdC h.𝔇.cs h.𝔇.arr h.𝔇.ms v)) (sent : ℕ → List (ℕ × ℕ))
    (hformsE : ∀ s v, Front (5, "K8.equations") s v → Sound.formsQA sent own (Desc.K9.readersOfLink (Desc.K9.withSmall
      Hh) Lk) 5 "K8.equations" s (LinkJoin.rdC h.𝔇.cs h.𝔇.arr h.𝔇.ms v)) (hLE : LensEqAsked Zp) :
    GivesTotalB Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links P5J.At.ps
      24) own (fun v => LinkJoin.rdC h.𝔇.cs h.𝔇.arr h.𝔇.ms v) (Desc.K9.rowsFit p.rows) tst Front := by
  have hm : 24 < 25 := by omega
  exact givesTotalB_head_worth h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O Sd e3 hd hC hD own hown tst Front htst
    (fun κ s m En ds y cols s' x' z G St a ha => by
      rw [hown, ← own_at_head h]
      exact ProofFile.Honest.K8.cellOkR_at_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm hd
        κ s m En ds y cols s' x' z G St a ha)
    (fun κ s m En ds y cols s' x' z G St a ha => by
      rw [hown, ← own_at_head h]
      exact ProofFile.Honest.K8.maskOkR_at_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm hd
        κ s m En ds y cols s' x' z G St a ha)
    hF₁ Hc Hh hforms sent hformsE hLE

/-- **The assembly at a feed-forward segment, with hCell and hMask paid.** -/
theorem givesTotalB_lay_two {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where}
    {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp (2 * g) kk Lk p ww) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g]? = some Xl) {xx : First.Look.Place} {tlD : HTailF2}
    (hd : First.Look.digAt (P5J.At.X Zp) (2 * g) = some (xx, tlD)) {p4 : OnBytes.Desc.First.K4.Par}
    (hk : LPFK9.k4ParAt Zp Bs.G₀ (2 * g) = some p4) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) (2 * g) false = some pC) (hD : placeAt (P5J.At.X Zp) (2 * g) true = some pD)
    (own : List (ℕ × ℕ)) (hown : own = (P5J.At.N Zp cF).group (2 * g)) (tst share4 : S → Option String)
    (Front : ℕ × String → S → (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Wt → Prop)
    (run4 : S → Except String S) (hr4 : (OnBytes.Desc.First.K4.blockAtC p4).after.lookup "free-slot" = some run4)
    (htst : ∀ e, tst e = none → freeSlotShare ww.2.2.filled e = none ∧ k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none ∧ share4 e
      = none)
    (hF₁ : ∀ s v, Front (4, "K8.equations") s v → LinkJoin.WorthTwo S.fork? LinkJoin.heardDig xx tlD h.𝔇.sent
      h.𝔇.l3.rad (fun j => h.𝔇.l3.seat xx.link true j.1) h.𝔇.l3.arr s v) (Xp : Verify.Public) {mH : ℕ}
    (hmH : (2 * g == mH) = false) (Hh : Desc.K9.LinkHoles)
    (hforms : ∀ o ∈ [(2, "front"), (2, "back")] ++ [(1, "objects"), (6, "objects")], ∀ s v, Front o s v → Sound.formsQ
      (Desc.K9.readersOfLink (Desc.K9.holesAt Xp mH (2 * g) Lk) Lk) own o.1 o.2 s (LinkJoin.rdC h.𝔇.cs h.𝔇.arr h.𝔇.ms
      v)) (sent : ℕ → List (ℕ × ℕ))
    (hformsE : ∀ s v, Front (4, "K8.equations") s v → Sound.formsQA sent own (Desc.K9.readersOfLink (Desc.K9.withSmall
      Hh) Lk) 4 "K8.equations" s (LinkJoin.rdC h.𝔇.cs h.𝔇.arr h.𝔇.ms v)) (hLE : LensEqAsked Zp)
    (h4 : K4Behind Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links
      P5J.At.ps (2 * g)) share4 run4) :
    GivesTotalB Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links P5J.At.ps
      (2 * g)) own (fun v => LinkJoin.rdC h.𝔇.cs h.𝔇.arr h.𝔇.ms v) (Desc.K9.rowsFit p.rows) tst Front := by
  have hm : 2 * g < 25 := by omega
  exact givesTotalB_lay_worth h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O hg Sd e3 hd hk hC hD own hown tst share4
    Front run4 hr4 htst
    (fun κ s m En ds y cols s' x' z G St a ha => by
      rw [hown, ← own_at_head h]
      exact ProofFile.Honest.K8.cellOkR_at_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm hd
        κ s m En ds y cols s' x' z G St a ha)
    (fun κ s m En ds y cols s' x' z G St a ha => by
      rw [hown, ← own_at_head h]
      exact ProofFile.Honest.K8.maskOkR_at_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm hd
        κ s m En ds y cols s' x' z G St a ha)
    hF₁ Xp hmH Hh hforms sent hformsE hLE h4

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.givesTotalB_att_two
#print axioms ProofFile.Honest.K9.givesTotalB_head_two
#print axioms ProofFile.Honest.K9.givesTotalB_lay_two
