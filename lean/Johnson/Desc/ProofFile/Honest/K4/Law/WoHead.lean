-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/WoHead.lean

What is here. The threads' own debt ExchangeAtS at the pending row's item `Item.wo m`, at the
member of the layers' own rounds (kind K4), at the first chain's thread at the library's own
parameters (`lettersHead`). PAID INSIDE: the table's parameters at the item (by unfolding, as
Law/WoAt.lean) · `K4Sits` · the seat's other fields · hws (the weights' layout is what the
verifier's own maker returns: Law/W/PlanHead.lean) · hlay (the data's layout is the public data's)
· hkC (the reader's number of column bits is the layout's: both are the library's kRef).
Statements with their proofs: calls.

  `wsLay_pub`: the public data's layout of the weights is that of the public part's own structure.
  `kCol_head`: the number of column bits at which the library's reader is typed is the layout's.
  `k4_exchange_wo_head`: ExchangeAtS T Said k (Item.wo m).

Limits. CONDITIONAL THROUGHOUT. THE FULL SIZE ALONE, AND THE FORMAT's EARLIER HASH ALONE: the
hypothesis h stands at the library's full-size structure and at OnBytes.secondHashFunction; that h holds of any
files is not shown here: the side library AtFullSide proves, with no hypothesis, that h has a member
at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own
Limits say what it is worth). Of h together with LaidK4 · hQ · half · front · fits · K4MaskTieAt ·
hLook · hTok · hAsk · K4IndexTieAt · K4WeightsTieK no example is known to us; the statement speaks
only where the thread stands: at a thread none of whose steps accepts it holds emptily. WHAT STAYS A
HYPOTHESIS, BY NAME: h · LaidK4 (h and the place give it: Law/SeatedHead.lean) · of the seat: hQ ·
half · front · fits · three ties of Law/ScriptAt.lean wherever the thread stands (the mask, at the
seats and the reader that the table lays; what the lookup has sampled; the tokens) · the library's
seven conditions at every accepted step (`KeptAsks`) · THE TWO TIES ON THE WITNESS at the library's
own reader of the pile of pending rows: nothing shows either. Its imports reach modules under
Johnson/Goal/ through h, as those of Law/ElevenHead.lean and Law/W/PlanHead.lean do: it is a law; no
part may import it; it states no goal. Nothing on soundness, on completeness or on any other
property.
No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.WoShareK
import Johnson.Desc.ProofFile.Honest.K4.Law.WoAt
import Johnson.Desc.ProofFile.Honest.K4.Law.W.ExchangeParts
import Johnson.Desc.ProofFile.Honest.K4.Law.W.PlanHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (zeroE)
open OnBytes.Model (Reading Forest.Heard)
open OnBytes.Model.Layer (Own)
open OnBytes.Road (unitOK_of_layout)
open OnBytes.Road.K4 (parOf)
open OnBytes.Desc.First.K4 (Par k0)
open OnBytes.Desc.First.K4.Total (KeptAsks)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open Inst.Model.Layout (kRef)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT seatTab)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4 k4Sits_head pub_of)
open ProofFile.Honest.K4.W (seated_all_head wsLay_head)
open ProofFile.Honest.SumLaw (SumCoins endRun)
open ProofFile.Honest.K4.SlotsOwn (SumAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- The public data's layout of the weights. CONDITIONAL: on Lh and hQ. -/
theorem wsLay_pub {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {Qp : K4Pub} (hQ : k4PubOf Zp x.2 = some Qp) :
    Qp.P.wsLay = (P5J.At.X Zp).layers.wsLay := by
  obtain ⟨⟨eP, _, _, _, _⟩, _, _, _⟩ := pub_of Lh hQ
  exact congrArg (fun P => P.wsLay) (eP.symm.trans Lh.P)

/-- The two numbers of column bits are one: both are the library's kRef. CONDITIONAL: on h and
Lh. -/
theorem kCol_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀) :
    h.𝔇.P13.lin.kCol = h.𝔇.d1.lay.lk :=
  (Nat.pow_right_injective (le_refl 2)
    (show 2 ^ h.𝔇.P13.lin.kCol = 2 ^ kRef from h.cols13)).trans
    (unitOK_of_layout (wsLay_head h Lh.lt Lh.hp)).1.symm

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **`ExchangeAtS` AT THE PENDING ROW's ITEM, AT THE THREAD.** CONDITIONAL: on every hypothesis
named. hIx: the first tie on the witness, at the reading of the first end coin of whatever the lent
row hands the merge's part. hWt: the second, at the matrix of the honest input's weights. -/
theorem k4_exchange_wo_head
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp)
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights tokens look Qp))
    (front : Qp.r0 = roundsTo cF.blocksInOrder k)
    (fits : ∀ fr, drawsFit (declsTo cF.blocksInOrder k) fr = true → Vd w₁ →
      k4Fits Qp (look Qp fr) (tokens w₁.x) = true)
    (hMask : ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      K4MaskTieAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cells weights
        tokens look Qp (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm)
    (hLook : ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      K4LookTieAt look Qp s mm)
    (hTok : ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      K4TokensTieAt tokens s mm)
    (hAsk : ∀ blk,
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
      ∀ c s mm E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y
        cols s' →
      ∃ (P₀ : OnBytes.Model.Layer.Pub) (o₀ : Own), KeptAsks (parOf x) s s' P₀ o₀)
    (hIx : ∀ blk,
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
      ∀ c s mm E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y
        cols s' →
      ∀ cc name endName (cp : SumCoins name endName (mergeSum Qp)),
        lendRow Bk
          (Bk.rowsOf (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain)
          (c.look (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain)
          (k4Place Qp) (k4Half (Rc := Rc) (X := X') cells weights tokens look Qp).parts 0 = .ok cc →
        SumAt cc (k0 Qp.g + 15) name endName (mergeSum Qp) cp →
        K4IndexTieAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread h.𝔇.rw13 c
          y.2 s' (Reading.gl.val ((endRun cp).getD 0 zeroE)))
    (hWt : ∀ blk,
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
      ∀ c s mm E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y
        cols s' →
      K4WeightsTieK (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread h.𝔇.d1
        h.𝔇.rw13 c y.2 s' (wmOf (k4Wit Qp cells weights tokens (look Qp) mm.st.input).w)) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k
      (Item.wo m) :=
  k4_exchangeAtS_wo_k Said (kCol_head h Lh)
    (k4WoTable_at h _ Q _ _ test carryX item n₁ n₂ _ _ _ m)
    (seated_all_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hQ half front fits)
    (k4Sits_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh) hMask hLook hTok hAsk
    (by rw [wsLay_pub Lh hQ]; exact wsLay_head h Lh.lt Lh.hp) (wsLay_pub Lh hQ).symm hIx hWt

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.wsLay_pub
#print axioms ProofFile.Honest.K4.kCol_head
#print axioms ProofFile.Honest.K4.k4_exchange_wo_head
