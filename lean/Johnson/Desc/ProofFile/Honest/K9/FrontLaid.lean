-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/FrontLaid.lean: FOR THE ITEM "totalB": OUR FREE LETTER Front IS LAID. IMPLICATIONS
STILL: no stand is shown. The three assemblies of Honest/K9/TotalWorthTwo.lean at Front := `frontC`
(Honest/K9/FrontBridge.lean): THEIR THREE CONDITIONS ON Front (hforms, hformsE, hF₁) ARE PROJECTIONS THERE; then each
over the bridge, to the reader and the Front at which the frame's own thread speaks. The statements are
TotalWorthTwo.lean's own, turned by program. No definition is made; no prover is in this file; no goal is stated.
  `notEq_of_all`   an entry of a list none of whose names is "K8.equations"
  **`givesTotalB_att_front`**, **`_head_front`**, **`_lay_front`**   `GivesTotalB` at own := `h.𝔇.N.group l`, the reader
      `rdC`, `frontC h l xx tlD`. THE LETTERS LAID: own (`own_at_head`) · Xp := `P5J.At.X Zp` · mH := the library's
      `headLink` of it (24: `headLink_in_scope`) · Hc, Hh := `holesAt` at these (the library's `k03_hlink`: the data's
      readers ARE the link's own at these holes; `withSmall` of them is them, by unfolding) · sent := `h.𝔇.N.sent l`.
      DEBTS: htst · hLE; at a feed-forward segment h4 beside
  **`givesTotalB_att_seat`**, **`_head_seat`**, **`_lay_seat`**: the same at the reader `seatTab` and `frontS h l xx
      tlD`: hin is paid (`insideAt_at_stand`); hbeh IS A NAMED PREMISE HERE (paid in Honest/K9/TotalExchangeFree.lean:
      `insideAt_behind_seat`, from K9's seat)
WHAT IS NOT CLAIMED. Any of the debts. THAT A STAND IS THERE. No member. The first three are called by the second three;
these by Honest/K9/TotalExchangeFree.lean alone. At the full size and the format's second hash function alone: the
head's. Nothing on any property.
GROUND: beneath this file, beside the sealed library, lie 579 files, this one among them: reading copies, all but ours.

-/
import Johnson.Desc.ProofFile.Honest.K9.FrontBridge
import Johnson.Desc.ProofFile.Honest.K9.InsideAtStand
import Johnson.P5J.RowsAtMg

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

/-- An entry of a list none of whose names is "K8.equations". -/
theorem notEq_of_all {L : List (ℕ × String)} (hL : (L.all fun o => o.2 != "K8.equations") = true) {o : ℕ × String}
    (ho : o ∈ L) : o.2 ≠ "K8.equations" := by
  have e := List.all_eq_true.1 hL o ho
  exact bne_iff_ne.1 e

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The assembly at an attention segment, AT THE LAID Front `frontC`**: the three conditions on Front are
projections. -/
theorem givesTotalB_att_front {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where}
    {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp (2 * g + 1) kk Lk p ww) {A : Attention.Plan}
    (hA : (P5J.At.X Zp).A[g]? = some A) {Xl : LinkH} (e3 : Bs.G₀.built[2 * g + 1]? = some Xl) {xx : First.Look.Place}
    {tlD : HTailF2} (hd : First.Look.digAt (P5J.At.X Zp) (2 * g + 1) = some (xx, tlD)) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) (2 * g + 1) false = some pC) (hD : placeAt (P5J.At.X Zp) (2 * g + 1) true = some pD)
    (tst : S → Option String)
    (htst : ∀ e, tst e = none → freeSlotShare ww.2.2.filled e = none ∧ k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none)
    (hLE : LensEqAsked Zp) :
    GivesTotalB Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links P5J.At.ps
      (2 * g + 1)) (h.𝔇.N.group (2 * g + 1)) (fun v => LinkJoin.rdC h.𝔇.cs h.𝔇.arr h.𝔇.ms v) (Desc.K9.rowsFit p.rows)
      tst (frontC h (2 * g + 1) xx tlD) := by
  have eR : h.𝔇.Rd (2 * g + 1) = Desc.K9.readersOfLink
      (Desc.K9.holesAt (P5J.At.X Zp) (OnPublicFiles.headLink (P5J.At.X Zp)) (2 * g + 1) Lk) Lk :=
    P5J.k03_hlink h (2 * g + 1) Lk Sd.link
  have hmH : (2 * g + 1 == OnPublicFiles.headLink (P5J.At.X Zp)) = false := by
    rw [P5J.headLink_in_scope h.scope h.reads h.pubOne]
    exact beq_false_of_ne (by omega)
  exact givesTotalB_att_two h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O hg Sd hA e3 hd hC hD
    (h.𝔇.N.group (2 * g + 1)) (own_at_head h (2 * g + 1)) tst (frontC h (2 * g + 1) xx tlD) htst
    (fun s v f => (f.2 rfl).2) (P5J.At.X Zp) hmH
    (Desc.K9.holesAt (P5J.At.X Zp) (OnPublicFiles.headLink (P5J.At.X Zp)) (2 * g + 1) Lk)
    (fun o ho s v f => eR ▸ f.1 (notEq_of_all (by decide) ho)) (h.𝔇.N.sent (2 * g + 1))
    (fun s v f => eR ▸ (f.2 rfl).1) hLE

/-- **The assembly at the head's segment, at the laid Front `frontC`.** -/
theorem givesTotalB_head_front {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree cF Zp 24 kk Lk p ww) {Xl : LinkH} (e3 : Bs.G₀.built[24]? = some Xl) {xx : First.Look.Place}
    {tlD : HTailF2} (hd : First.Look.digAt (P5J.At.X Zp) 24 = some (xx, tlD)) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) 24 false = some pC) (hD : placeAt (P5J.At.X Zp) 24 true = some pD)
    (tst : S → Option String)
    (htst : ∀ e, tst e = none → freeSlotShare ww.2.2.filled e = none ∧ k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none)
    (hLE : LensEqAsked Zp) :
    GivesTotalB Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links P5J.At.ps
      24) (h.𝔇.N.group 24) (fun v => LinkJoin.rdC h.𝔇.cs h.𝔇.arr h.𝔇.ms v) (Desc.K9.rowsFit p.rows) tst (frontC h 24
      xx tlD) := by
  have eR : h.𝔇.Rd 24 = Desc.K9.readersOfLink
      (Desc.K9.holesAt (P5J.At.X Zp) (OnPublicFiles.headLink (P5J.At.X Zp)) 24 Lk) Lk :=
    P5J.k03_hlink h 24 Lk Sd.link
  exact givesTotalB_head_two h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O Sd e3 hd hC hD (h.𝔇.N.group 24)
    (own_at_head h 24) tst (frontC h 24 xx tlD) htst (fun s v f => (f.2 rfl).2)
    (Desc.K9.holesAt (P5J.At.X Zp) (OnPublicFiles.headLink (P5J.At.X Zp)) 24 Lk)
    (Desc.K9.holesAt (P5J.At.X Zp) (OnPublicFiles.headLink (P5J.At.X Zp)) 24 Lk)
    (fun o ho s v f => eR ▸ f.1 (notEq_of_all (by decide) ho)) (h.𝔇.N.sent 24) (fun s v f => eR ▸ (f.2 rfl).1) hLE

/-- **The assembly at a feed-forward segment, at the laid Front `frontC`.** -/
theorem givesTotalB_lay_front {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where}
    {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp (2 * g) kk Lk p ww) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g]? = some Xl) {xx : First.Look.Place} {tlD : HTailF2}
    (hd : First.Look.digAt (P5J.At.X Zp) (2 * g) = some (xx, tlD)) {p4 : OnBytes.Desc.First.K4.Par}
    (hk : LPFK9.k4ParAt Zp Bs.G₀ (2 * g) = some p4) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) (2 * g) false = some pC) (hD : placeAt (P5J.At.X Zp) (2 * g) true = some pD)
    (tst share4 : S → Option String) (run4 : S → Except String S)
    (hr4 : (OnBytes.Desc.First.K4.blockAtC p4).after.lookup "free-slot" = some run4)
    (htst : ∀ e, tst e = none → freeSlotShare ww.2.2.filled e = none ∧ k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none ∧ share4 e
      = none) (hLE : LensEqAsked Zp)
    (h4 : K4Behind Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links
      P5J.At.ps (2 * g)) share4 run4) :
    GivesTotalB Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links P5J.At.ps
      (2 * g)) (h.𝔇.N.group (2 * g)) (fun v => LinkJoin.rdC h.𝔇.cs h.𝔇.arr h.𝔇.ms v) (Desc.K9.rowsFit p.rows) tst
      (frontC h (2 * g) xx tlD) := by
  have eR : h.𝔇.Rd (2 * g) = Desc.K9.readersOfLink
      (Desc.K9.holesAt (P5J.At.X Zp) (OnPublicFiles.headLink (P5J.At.X Zp)) (2 * g) Lk) Lk :=
    P5J.k03_hlink h (2 * g) Lk Sd.link
  have hmH : (2 * g == OnPublicFiles.headLink (P5J.At.X Zp)) = false := by
    rw [P5J.headLink_in_scope h.scope h.reads h.pubOne]
    exact beq_false_of_ne (by omega)
  exact givesTotalB_lay_two h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O hg Sd e3 hd hk hC hD (h.𝔇.N.group (2 * g))
    (own_at_head h (2 * g)) tst share4 (frontC h (2 * g) xx tlD) run4 hr4 htst (fun s v f => (f.2 rfl).2)
    (P5J.At.X Zp) hmH (Desc.K9.holesAt (P5J.At.X Zp) (OnPublicFiles.headLink (P5J.At.X Zp)) (2 * g) Lk)
    (fun o ho s v f => eR ▸ f.1 (notEq_of_all (by decide) ho)) (h.𝔇.N.sent (2 * g)) (fun s v f => eR ▸ (f.2 rfl).1)
    hLE h4

/-- **At an attention segment, OVER THE BRIDGE: at the witness's tables by seat and the exchange's Front `frontS`.** -/
theorem givesTotalB_att_seat {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where}
    {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp (2 * g + 1) kk Lk p ww) {A : Attention.Plan}
    (hA : (P5J.At.X Zp).A[g]? = some A) {Xl : LinkH} (e3 : Bs.G₀.built[2 * g + 1]? = some Xl) {xx : First.Look.Place}
    {tlD : HTailF2} (hd : First.Look.digAt (P5J.At.X Zp) (2 * g + 1) = some (xx, tlD)) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) (2 * g + 1) false = some pC) (hD : placeAt (P5J.At.X Zp) (2 * g + 1) true = some pD)
    (tst : S → Option String)
    (htst : ∀ e, tst e = none → freeSlotShare ww.2.2.filled e = none ∧ k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none)
    (hLE : LensEqAsked Zp)
    (hbeh : ∀ κ s m En ds y cols s' x' z G, BatStand Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp
      w).thread (batchAt P5J.At.links P5J.At.ps (2 * g + 1)) κ s m En ds y cols s' x' z G → ∀ t a, Lk.runBehind s' =
      .ok t → Desc.K9.atS.get? t = some a → Sound.InsideAt h.𝔇.cs h.𝔇.ms (h.𝔇.N.group (2 * g + 1)) a) :
    GivesTotalB Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links P5J.At.ps
      (2 * g + 1)) (h.𝔇.N.group (2 * g + 1)) (fun v => Sound.seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v) (Desc.K9.rowsFit p.rows)
      tst (frontS h (2 * g + 1) xx tlD) := by
  have hm : 2 * g + 1 < 25 := by omega
  exact givesTotalB_seat h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm xx tlD _ tst
    (givesTotalB_att_front h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O hg Sd hA e3 hd hC hD tst htst hLE)
    (insideAt_at_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm) hbeh

/-- **At the head's segment, over the bridge.** -/
theorem givesTotalB_head_seat {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree cF Zp 24 kk Lk p ww) {Xl : LinkH} (e3 : Bs.G₀.built[24]? = some Xl) {xx : First.Look.Place}
    {tlD : HTailF2} (hd : First.Look.digAt (P5J.At.X Zp) 24 = some (xx, tlD)) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) 24 false = some pC) (hD : placeAt (P5J.At.X Zp) 24 true = some pD)
    (tst : S → Option String)
    (htst : ∀ e, tst e = none → freeSlotShare ww.2.2.filled e = none ∧ k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none)
    (hLE : LensEqAsked Zp)
    (hbeh : ∀ κ s m En ds y cols s' x' z G, BatStand Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp
      w).thread (batchAt P5J.At.links P5J.At.ps 24) κ s m En ds y cols s' x' z G → ∀ t a, Lk.runBehind s' = .ok t →
      Desc.K9.atS.get? t = some a → Sound.InsideAt h.𝔇.cs h.𝔇.ms (h.𝔇.N.group 24) a) :
    GivesTotalB Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links P5J.At.ps
      24) (h.𝔇.N.group 24) (fun v => Sound.seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v) (Desc.K9.rowsFit p.rows) tst (frontS h 24
      xx tlD) := by
  have hm : 24 < 25 := by omega
  exact givesTotalB_seat h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm xx tlD _ tst
    (givesTotalB_head_front h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O Sd e3 hd hC hD tst htst hLE)
    (insideAt_at_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm) hbeh

/-- **At a feed-forward segment, over the bridge.** -/
theorem givesTotalB_lay_seat {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where}
    {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp (2 * g) kk Lk p ww) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g]? = some Xl) {xx : First.Look.Place} {tlD : HTailF2}
    (hd : First.Look.digAt (P5J.At.X Zp) (2 * g) = some (xx, tlD)) {p4 : OnBytes.Desc.First.K4.Par}
    (hk : LPFK9.k4ParAt Zp Bs.G₀ (2 * g) = some p4) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) (2 * g) false = some pC) (hD : placeAt (P5J.At.X Zp) (2 * g) true = some pD)
    (tst share4 : S → Option String) (run4 : S → Except String S)
    (hr4 : (OnBytes.Desc.First.K4.blockAtC p4).after.lookup "free-slot" = some run4)
    (htst : ∀ e, tst e = none → freeSlotShare ww.2.2.filled e = none ∧ k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none ∧ share4 e
      = none) (hLE : LensEqAsked Zp)
    (h4 : K4Behind Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links
      P5J.At.ps (2 * g)) share4 run4)
    (hbeh : ∀ κ s m En ds y cols s' x' z G, BatStand Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp
      w).thread (batchAt P5J.At.links P5J.At.ps (2 * g)) κ s m En ds y cols s' x' z G → ∀ t a, Lk.runBehind s' = .ok t
      → Desc.K9.atS.get? t = some a → Sound.InsideAt h.𝔇.cs h.𝔇.ms (h.𝔇.N.group (2 * g)) a) :
    GivesTotalB Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links P5J.At.ps
      (2 * g)) (h.𝔇.N.group (2 * g)) (fun v => Sound.seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v) (Desc.K9.rowsFit p.rows) tst
      (frontS h (2 * g) xx tlD) := by
  have hm : 2 * g < 25 := by omega
  exact givesTotalB_seat h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm xx tlD _ tst
    (givesTotalB_lay_front h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O hg Sd e3 hd hk hC hD tst share4 run4 hr4 htst
    hLE h4)
    (insideAt_at_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm) hbeh

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.notEq_of_all
#print axioms ProofFile.Honest.K9.givesTotalB_att_front
#print axioms ProofFile.Honest.K9.givesTotalB_head_front
#print axioms ProofFile.Honest.K9.givesTotalB_lay_front
#print axioms ProofFile.Honest.K9.givesTotalB_att_seat
#print axioms ProofFile.Honest.K9.givesTotalB_head_seat
#print axioms ProofFile.Honest.K9.givesTotalB_lay_seat
