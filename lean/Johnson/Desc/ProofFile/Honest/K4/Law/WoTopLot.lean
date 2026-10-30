-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/WoTopLot.lean: CONDITIONAL.

What is here. The threads' debt ExchangeAtS at the pending row's item `Item.wo m`, at the member of
the layers' own rounds (kind K4), at the first chain's thread at the library's own parameters
(`lettersHead`), AT WHAT K4's OWN LOT LAYS (`k4HLot`, Honest/K4/Part.lean): the reader of the tokens
is `k4Tokens` and the public data are `k4PubAt cF k x` (Law/DearTop.lean). It is
`k4_exchange_wo_look` (Law/WoTopLook.lean) WITH TWO MORE OF ITS HYPOTHESES STRUCK: hQ (`k4PubOf`
returns these public data: `k4Pub_head`, Law/FrontCount.lean) and the tie on the tokens
(`K4TokensTieAt`: the tokens that the state holds are the instance's: `tokensTie_head`,
Law/TokensIs.lean: a theorem under h wherever the thread stands). One statement with its proof:
three calls.

  `k4_exchange_wo_lot`: ExchangeAtS T Said k (Item.wo m).

Limits. CONDITIONAL: on h · LaidK4 · half · fits · LookIsK3 · AND THREE NAMED TIES, EACH STILL A
HYPOTHESIS: `K4MaskTieAt` · `K4IndexTieAt` · `K4WeightsTieK`. `K4WeightsTieK` (Law/WoShareK.lean)
holds, beside the tie on the witness, a public inequality (the matrix's rows are at most 2 ^ kRow:
not shown here) and a sentence on the index alone (its reader is 0 from the row nR on), which only
Vd can give. ON LookIsK3: under h and LaidK4 `lookAt_isK3` (Law/LookAtFill.lean) has it at
`k4LookAt` (Honest/K4/Look.lean), from one equation on numbers of rounds, which `lookBase_head`
(Law/LookBaseHead.lean) has. `look_fill` (Law/LookOpenHead.lean) has it where look is the kind K3's
whole text `lookOfK3`; at `k4LookAt` that statement's hypothesis hfill is false wherever the shape
has a call (`lookOf_ne`, Law/LookAtFill.lean), so it cannot be called there. fits holds the test on
the tokens at w₁ under Vd: Law/WoTopThr.lean strikes it: where the thread stands `tokensFit_k4`
(Law/TokensIs.lean) has it. half is a fact on the prover's term: it is false of a term that lays no
half of this kind. Of h together with LaidK4 · half · fits · K4MaskTieAt · hL · K4IndexTieAt ·
K4WeightsTieK no example is known to us; the statement speaks only where the thread stands and the
member's step accepts. THE FULL SIZE ALONE, AND THE FORMAT's EARLIER HASH ALONE; that h holds of any
files is not shown here: the side library AtFullSide proves, with no hypothesis, that h has a member
at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own
Limits say what it is worth). IT IS A LAW, NOT A PART: it rests on modules under Johnson/Goal/: no
file that defines a part may build on it; it states no goal. Nothing on soundness, on completeness
or on any other property. No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.WoTopLook
import Johnson.Desc.ProofFile.Honest.K4.Law.TokensIs

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
open ProofFile.Honest.K4.W (LookIsK3)
open ProofFile.Honest.SumLaw (SumCoins endRun)
open ProofFile.Honest.K4.SlotsOwn (SumAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **`ExchangeAtS` AT THE PENDING ROW's ITEM, AT WHAT K4's LOT LAYS: hQ AND THE TIE ON THE TOKENS
STRUCK.** CONDITIONAL: on every hypothesis named. hL: look agrees with the kind K3's text in the
fields zx, zk and e, at every list of challenges. hIx: the witness's mask entry under the index
masks' next entry, at the state behind the step, is the first end coin that the lent row hands the
merge's part. hWt: three clauses: nR ≤ 2 ^ kRow; the reader's matrix is 0 from the row nR on; the
witness's matrix is the reader's inside. -/
theorem k4_exchange_wo_lot
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {cells : Tr → Cells} {weights : W₀ → Weights}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard}
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights k4Tokens look (k4PubAt cF k x)))
    (fits : ∀ fr, drawsFit (declsTo cF.blocksInOrder k) fr = true → Vd w₁ →
      k4Fits (k4PubAt cF k x) (look (k4PubAt cF k x) fr) (k4Tokens w₁.x) = true)
    (hMask : ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      K4MaskTieAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cells weights
        k4Tokens look (k4PubAt cF k x) (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm)
    (hL : LookIsK3 look (k4PubAt cF k x) Zp cF g w₁.x)
    (hIx : ∀ blk,
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
      ∀ c s mm E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y
        cols s' →
      ∀ cc name endName (cp : SumCoins name endName (mergeSum (k4PubAt cF k x))),
        lendRow Bk
          (Bk.rowsOf (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain)
          (c.look (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain)
          (k4Place (k4PubAt cF k x))
          (k4Half (Rc := Rc) (X := X') cells weights k4Tokens look (k4PubAt cF k x)).parts 0 =
            .ok cc →
        SumAt cc (k0 (k4PubAt cF k x).g + 15) name endName (mergeSum (k4PubAt cF k x)) cp →
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
        h.𝔇.rw13 c y.2 s'
        (wmOf (k4Wit (k4PubAt cF k x) cells weights k4Tokens (look (k4PubAt cF k x))
          mm.st.input).w)) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k
      (Item.wo m) :=
  k4_exchange_wo_look h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said Lh (k4Pub_head h Lh) half
    fits hMask hL
    (fun _ _ _ _ hT => tokensTie_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁
      (Nat.le_of_lt (List.getElem?_eq_some_iff.1 Lh.member).1) hT.1)
    hIx hWt

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_exchange_wo_lot
