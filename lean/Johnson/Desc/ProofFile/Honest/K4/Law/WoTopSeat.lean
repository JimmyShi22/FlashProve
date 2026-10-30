-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/WoTopSeat.lean

What is here. The threads' debt ExchangeAtS at the pending row's item `Item.wo m`, at the member of
the layers' own rounds (kind K4), at the first chain's thread at the library's own parameters
(`lettersHead`), at what K4's own lot lays (`k4HLot`, Honest/K4/Part.lean). It is
`k4_exchange_wo_lot` (Law/WoTopLot.lean) WITH ITS HYPOTHESIS fits, the public test `k4Fits`, DOWN TO
TWO OF ITS FOUR TESTS: hLk, the test on the sizes of what the lookup has sampled (`k4LookFits`), and
hTk, the test on the tokens (`k4TokensFit`): `fits_member` (Law/FitsMember.lean). hLk and hTk have
the form of the hypotheses of these names of `k4Seated_member` (Law/SeatedMember.lean). The
parameter `look` stays free: the statement fixes no filling of it. One statement with its proof: two
calls.

  `k4_exchange_wo_seat`: ExchangeAtS T Said k (Item.wo m).

Limits. CONDITIONAL: on h · LaidK4 · half · hLk · hTk · LookIsK3 · AND THREE NAMED TIES, EACH STILL
A HYPOTHESIS: `K4MaskTieAt` · `K4IndexTieAt` · `K4WeightsTieK`. half is a fact on the prover's term:
it is false of a term that lays no half of this kind. hLk and LookIsK3 are facts on `look`: shown
here of no `look`. Of h together with LaidK4 · half · hLk · hTk · K4MaskTieAt · hL · K4IndexTieAt ·
K4WeightsTieK no example is known to us; the statement speaks only where the thread stands and the
member's step accepts. THE FULL SIZE ALONE, AND THE FORMAT's EARLIER HASH ALONE; that h holds of any
files is not shown here: the side library AtFullSide proves, with no hypothesis, that h has a member
at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own
Limits say what it is worth). Beneath `fits_member` stand comparisons by Lean's own kernel that no
independent checker has replayed (Law/FitsMember.lean's head names them). IT IS A LAW, NOT A PART:
it rests on modules under Johnson/Goal/: no file that defines a part may build on it; it states no
goal. Nothing on soundness, on completeness or on any other property.
No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.WoTopLot
import Johnson.Desc.ProofFile.Honest.K4.Law.FitsMember

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

/-- **`ExchangeAtS` AT THE PENDING ROW's ITEM, AT WHAT K4's LOT LAYS: fits DOWN TO TWO LIGHT
TESTS.** CONDITIONAL: on every hypothesis named. hL, hIx, hWt: as in Law/WoTopLook.lean. -/
theorem k4_exchange_wo_seat
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {cells : Tr → Cells} {weights : W₀ → Weights}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard}
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights k4Tokens look (k4PubAt cF k x)))
    (hLk : ∀ fr, drawsFit (declsTo cF.blocksInOrder k) fr = true →
      k4LookFits (k4PubAt cF k x) (look (k4PubAt cF k x) fr) = true)
    (hTk : Vd w₁ → k4TokensFit (k4PubAt cF k x) (k4Tokens w₁.x) = true)
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
  k4_exchange_wo_lot h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said Lh half
    (fun fr hd hV => fits_member h Lh (hLk fr hd) (hTk hV)) hMask hL hIx hWt

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_exchange_wo_seat
