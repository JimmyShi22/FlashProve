-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TotalExchangeLens.lean: THE FRAME's DEBT AT THE ITEM totalB (`ExchangeAtS` at
`SaidOk`), AT THE FRAME's OWN THREAD AT THE LIBRARY's HEAD, AT THE BATCHING OF EACH OF THE 25 SEGMENTS, WITH THE PREMISE
hLE PAID: the three closing theorems of Honest/K9/TotalExchangeFree.lean called at `lensEqAsked_of_head`
(Johnson/Desc/K9/Honest/LensPaid/Paid.lean: the public test `LensEqAsked` holds under the head). WHAT THEY STILL ASK:
K9's seat Sd, which the head hands (`seated_at_head`, Honest/K9/AtHead.lean) · public readings · htst · at the twelve
feed-forward segments h4. IMPLICATIONS STILL: NO MEMBER: that the thread stands in front of a batching at any run is
shown by nobody; in the words that go with these forms: "at the filling of record not
shown to speak at any of the 25 ([…], argued: empty from 13 on with PlayedTo in Said; L25: not at SaidOk alone)". The
statements are those of that file with one binder struck, made by program; each proof is one call. No definition; no
prover is made; no goal is stated.
  **`exchange_totalB_att_lens`**, **`_24_lens`**, **`_lay_lens`**   at 2 g + 1, at 24, at 2 g
WHAT IS NOT CLAIMED. htst (a condition on whoever lays the letter test) · h4 (`K4Behind`; in words
which go with every quotation of it: "share IS A FREE LETTER: at share ≡ some _ the debt is met for nothing: wherever it
is paid, share4 is K4's own named, closed test; run4 is pinned in _lay_free, not in the definition"; here: by hr4 of
`_lay_lens`) at anything. Who opens the two items "worth" in front (the lookups' exchange). All that
Honest/K9/TotalExchangeFree.lean's head says on a list without a half at K9's place, and on a filling at which the
thread fails for another member's sake, holds here. The three are called by Honest/K9/ExchangeAtHead.lean, where the seat, the
public readings and h4 are paid and htst alone is left. At the full size and the format's second hash function alone. Nothing on any
property.
GROUND: beneath this file lie files, of several groups of authors, that are no part of the sealed library.
-/
import Johnson.Desc.ProofFile.Honest.K9.TotalExchangeFree
import Johnson.Desc.K9.Honest.LensPaid.Paid

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

/-- **At an attention segment.** `exchange_totalB_att_free` (Honest/K9/TotalExchangeFree.lean) with its premise hLE
paid. -/
theorem exchange_totalB_att_lens {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} (O : IM.Open OnBytes.secondHashFunction
                Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g
                            < 12) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd :
                                  SeatedFree cF Zp (2 * g + 1) kk Lk p ww) {A : Attention.Plan} (hA : (P5J.At.X Zp).A[g]? = some A) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g + 1]? = some Xl) {xx : First.Look.Place} {tlD : HTailF2} (hd : First.Look.digAt
    (P5J.At.X Zp) (2 * g + 1) = some (xx, tlD)) {pC pD : First.Look.P} (hC : placeAt (P5J.At.X Zp) (2 * g + 1) false
    = some pC) (hD : placeAt (P5J.At.X Zp) (2 * g + 1) true = some pD) (htst : ∀ e, test (2 * g + 1) e = none →
    freeSlotShare ww.2.2.filled e = none ∧ k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none) : ExchangeAtS (lettersHead h H Q
          test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk (batchAt P5J.At.links P5J.At.ps (2 * g + 1)) (Item.totalB (2
          * g + 1)) :=
  exchange_totalB_att_free h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O hg Sd hA e3 hd hC hD htst (lensEqAsked_of_head
    h.toAtMg)

/-- **At the head's segment.** `exchange_totalB_24_free` (Honest/K9/TotalExchangeFree.lean) with its premise hLE
paid. -/
theorem exchange_totalB_24_lens {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} (O : IM.Open OnBytes.secondHashFunction Z.pol
                Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np) (secondAt Zp Np)) {kk : ℕ} {Lk : Link S
                            ProofFile.Cl} {p : Desc.K9.Where} {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp 24 kk Lk p ww)
    {Xl : LinkH} (e3 : Bs.G₀.built[24]? = some Xl) {xx : First.Look.Place} {tlD : HTailF2} (hd : First.Look.digAt
    (P5J.At.X Zp) 24 = some (xx, tlD)) {pC pD : First.Look.P} (hC : placeAt (P5J.At.X Zp) 24 false = some pC) (hD :
    placeAt (P5J.At.X Zp) 24 true = some pD) (htst : ∀ e, test 24 e = none → freeSlotShare ww.2.2.filled e = none ∧
    k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none) : ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp
          w).thread SaidOk (batchAt P5J.At.links P5J.At.ps 24) (Item.totalB 24) :=
  exchange_totalB_24_free h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O Sd e3 hd hC hD htst (lensEqAsked_of_head
    h.toAtMg)

/-- **At a feed-forward segment.** `exchange_totalB_lay_free` (Honest/K9/TotalExchangeFree.lean) with its premise hLE
paid. -/
theorem exchange_totalB_lay_lens {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} (O : IM.Open OnBytes.secondHashFunction
                Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g
                            < 12) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd :
                                  SeatedFree cF Zp (2 * g) kk Lk p ww) {Xl : LinkH} (e3 : Bs.G₀.built[2 * g]? = some Xl) {xx : First.Look.Place}
    {tlD : HTailF2} (hd : First.Look.digAt (P5J.At.X Zp) (2 * g) = some (xx, tlD)) {p4 : OnBytes.Desc.First.K4.Par}
    (hk : LPFK9.k4ParAt Zp Bs.G₀ (2 * g) = some p4) {pC pD : First.Look.P} (hC : placeAt (P5J.At.X Zp) (2 * g) false
    = some pC) (hD : placeAt (P5J.At.X Zp) (2 * g) true = some pD) (share4 : S → Option String) (run4 : S → Except
    String S) (hr4 : (OnBytes.Desc.First.K4.blockAtC p4).after.lookup "free-slot" = some run4) (htst : ∀ e, test (2
    * g) e = none → freeSlotShare ww.2.2.filled e = none ∧ k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none ∧ share4 e = none)
    (h4 : K4Behind Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links
    P5J.At.ps (2 * g)) share4 run4) : ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
    SaidOk (batchAt P5J.At.links P5J.At.ps (2 * g)) (Item.totalB (2 * g)) :=
  exchange_totalB_lay_free h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O hg Sd e3 hd hk hC hD share4 run4 hr4 htst
    (lensEqAsked_of_head h.toAtMg) h4

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.exchange_totalB_att_lens
#print axioms ProofFile.Honest.K9.exchange_totalB_24_lens
#print axioms ProofFile.Honest.K9.exchange_totalB_lay_lens
