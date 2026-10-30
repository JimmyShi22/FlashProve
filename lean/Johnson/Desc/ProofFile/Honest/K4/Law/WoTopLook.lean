-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/WoTopLook.lean: CONDITIONAL.

What is here. The threads' debt ExchangeAtS at the pending row's item `Item.wo m`, at the member of
the layers' own rounds (kind K4), at the first chain's thread at the library's own parameters
(`lettersHead`): `k4_exchange_wo_top` (Law/WoTop.lean) WITH TWO OF ITS HYPOTHESES STRUCK. «front»
(the count of rounds in the place's public data is the chain's) is a theorem under h, the member's
laying and hQ (`front_head`, Law/FrontCount.lean). The tie on what the lookup has heard
(`K4LookTieAt`, asked wherever the thread stands) comes out of the thread's own sentence and ONE
SENTENCE ON THE PARAMETER look ALONE, at the run's instance: `LookIsK3`: at every list of challenges
look agrees, in three fields, with the text of the writers of the kind "lookup" (`lookTie_k3`,
Law/LookPtsHead.lean). One statement with its proof: three calls.

  `k4_exchange_wo_look`: ExchangeAtS T Said k (Item.wo m).

Limits. CONDITIONAL: on h · LaidK4 · hQ (it names what `k4PubOf` returns; `k4Pub_head`,
Law/FrontCount.lean, shows that it returns) · half · fits · LookIsK3 · AND FOUR NAMED TIES, EACH
STILL A HYPOTHESIS: `K4MaskTieAt` · `K4TokensTieAt` (the tokens that the state holds are the
instance's) · `K4IndexTieAt` · `K4WeightsTieK`. ON LookIsK3: under h and LaidK4 `lookAt_isK3`
(Law/LookAtFill.lean) has it at `k4LookAt` (Honest/K4/Look.lean), from one equation on numbers of
rounds, which `lookBase_head` (Law/LookBaseHead.lean) has. `look_fill` (Law/LookOpenHead.lean) has
it where look is the kind K3's whole text `lookOfK3`; at `k4LookAt` that statement's hypothesis
hfill is false wherever the shape has a call (`lookOf_ne`, Law/LookAtFill.lean), so it cannot be
called there. Of h together with LaidK4 · hQ · half · fits · K4MaskTieAt · hL · hTok · K4IndexTieAt
· K4WeightsTieK no example is known to us; the statement speaks only where the thread stands and the
member's step accepts. THE FULL SIZE ALONE, AND THE FORMAT's EARLIER HASH ALONE; that h holds of any
files is not shown here: the side library AtFullSide proves, with no hypothesis, that h has a member
at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own
Limits say what it is worth). IT IS A LAW, NOT A PART: it rests on modules under Johnson/Goal/: no
file that defines a part may build on it; it states no goal. Nothing on soundness, on completeness
or on any other property. No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.WoTop
import Johnson.Desc.ProofFile.Honest.K4.Law.FrontCount
import Johnson.Desc.ProofFile.Honest.K4.Law.LookPtsHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (zeroE)
open OnBytes.Model (Reading Forest.Heard)
open OnBytes.Desc.First.K4 (Par k0)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT seatTab)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open ProofFile.Honest.K4.W (LookIsK3 lookTie_k3)
open ProofFile.Honest.SumLaw (SumCoins endRun)
open ProofFile.Honest.K4.SlotsOwn (SumAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **`ExchangeAtS` AT THE PENDING ROW's ITEM, AT THE THREAD: «front» AND THE LOOKUP's TIE
STRUCK.** CONDITIONAL: on every hypothesis named. hL: the sentence on look, at the run's instance.
hIx, hWt: what each says: Law/WoTopLot.lean. -/
theorem k4_exchange_wo_look
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp)
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights tokens look Qp))
    (fits : ∀ fr, drawsFit (declsTo cF.blocksInOrder k) fr = true → Vd w₁ →
      k4Fits Qp (look Qp fr) (tokens w₁.x) = true)
    (hMask : ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      K4MaskTieAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cells weights
        tokens look Qp (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm)
    (hL : LookIsK3 look Qp Zp cF g w₁.x)
    (hTok : ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      K4TokensTieAt tokens s mm)
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
  k4_exchange_wo_top h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said Lh hQ half
    (front_head h Lh hQ) fits hMask
    (fun _ _ mm _ hT => lookTie_k3 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hT.1 (by
      obtain ⟨-, -, -, -, -, -, hv⟩ := hT.1
      have hv' : mm.st.input = w₁ ∧ Vd mm.st.input := hv
      rw [hv'.1]
      exact hL))
    hTok hIx hWt

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_exchange_wo_look
