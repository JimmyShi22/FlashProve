-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/WoTopAtPure.lean: CONDITIONAL.

What is here. The threads' debt `ExchangeAtS` (Honest/Thread/SharesS.lean) at the pending row's item
`Item.wo m` (Johnson/Desc/First/Borders.lean), at the member of the layers' own rounds (kind K4), at
the first chain's thread (`lettersHead`) OF THE HONEST PROVER THAT THE FRAME's MAKER `onlineProverFromPublicFiles`
RETURNS at the public files of h, where K4's own lot (`k4HLot`, Honest/K4/Part.lean) is among the
filling's lots WITH ITS PARAMETER `look` FILLED BY `k4LookAt` (Honest/K4/Look.lean). It is
`k4_exchange_wo_seat` (Law/WoTopSeat.lean) WITH THREE OF ITS HYPOTHESES STRUCK AND ONE BROUGHT DOWN:
half (`half_atPure`, Law/HalfAtPure.lean) · hLk (`lookFits_lookAt`, Law/LookAtFill.lean) · LookIsK3
(`lookAt_isK3`, the same file, over `lookBase_head`, Law/LookBaseHead.lean) · hTk, which falls to
one clause on Vd (`hTk_of`, Law/TokensSeat.lean). `k4_exchange_wo_lookAt_thr` (Law/WoTopThr.lean)
ASKS LESS: not hVd. One statement with its proof: six calls.

  `k4_exchange_wo_lookAt`: ExchangeAtS T Said k (Item.wo m).

Limits. CONDITIONAL: on h · LaidK4 · hA (the maker returns) · hL (K4's lot is among the filling's
lots) · ho (no other lot of the filling has a half at a place of the kind K4) · hVd (under Vd the
verifier's test on the request's words accepts) · AND THREE NAMED TIES, EACH STILL A HYPOTHESIS:
`K4MaskTieAt` · `K4IndexTieAt` · `K4WeightsTieK`. `K4WeightsTieK` (Law/WoShareK.lean) holds, beside
the tie on the witness, a public inequality (the matrix's rows are at most 2 ^ kRow: not shown here)
and a sentence on the index alone (its reader is 0 from the row nR on), which only Vd can give. hVd:
`hVd_of_mark` (Law/TokensSeatMark.lean) has it from the start's state bearing no mark. That `onlineProverFromPublicFiles`
returns at any filling that holds K4's lot is not shown here. Of h together with hA · LaidK4 · hL ·
ho · hVd · K4MaskTieAt · K4IndexTieAt · K4WeightsTieK no example is known to us; the statement
speaks only where the thread stands and the member's step accepts. THE FULL SIZE ALONE, AND THE
FORMAT's EARLIER HASH ALONE; that h holds of any files is not shown here: the side library
AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). Beneath `fits_member` and `half_atPure` stand comparisons by Lean's own kernel that no
independent checker has replayed (Law/FitsMember.lean's head names them). IT IS A LAW, NOT A PART:
it rests on modules under Johnson/Goal/: no file that defines a part may build on it; it states no
goal. Nothing on soundness, on completeness or on any other property.
No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.WoTopSeat
import Johnson.Desc.ProofFile.Honest.K4.Law.HalfAtPure
import Johnson.Desc.ProofFile.Honest.K4.Law.TokensSeat
import Johnson.Desc.ProofFile.Honest.K4.Law.LookAtFill
import Johnson.Desc.ProofFile.Honest.K4.Law.LookBaseHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (zeroE)
open OnBytes.Model (Reading)
open OnBytes.Desc.First.K4 (Par k0)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT seatTab)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open ProofFile.Honest.K4.W (lookFits_lookAt lookAt_isK3 lookBase_head)
open ProofFile.Honest.SumLaw (SumCoins endRun)
open ProofFile.Honest.K4.SlotsOwn (SumAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Tr X₀ X' : Type}
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **`ExchangeAtS` AT THE PENDING ROW's ITEM, AT THE MAKER's PROVER, AT look := `k4LookAt`.**
CONDITIONAL: on every hypothesis named. hIx, hWt: what each says: Law/WoTopLot.lean. -/
theorem k4_exchange_wo_lookAt {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    (hL : k4HLot cells weights (fun _ _ => k4LookAt) ∈ P.lots)
    (ho : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M.halves A.Z A.G = (k4HLot cells weights (fun _ _ => k4LookAt)).halves A.Z A.G)
    (hVd : Vd w₁ → reqFine Zp w₁.x.pub = true)
    (hMask : ∀ c s mm E,
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      K4MaskTieAt (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cells weights
        k4Tokens k4LookAt (k4PubAt cF k x) (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm)
    (hIx : ∀ blk,
      (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
      ∀ c s mm E ds y cols s',
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      drawsFit blk.rounds ds = true →
      (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y
        cols s' →
      ∀ cc name endName (cp : SumCoins name endName (mergeSum (k4PubAt cF k x))),
        lendRow Bk
          (Bk.rowsOf (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain)
          (c.look (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain)
          (k4Place (k4PubAt cF k x))
          (k4Half (Rc := Rc) (X := X') cells weights k4Tokens k4LookAt (k4PubAt cF k x)).parts 0 =
            .ok cc →
        SumAt cc (k0 (k4PubAt cF k x).g + 15) name endName (mergeSum (k4PubAt cF k x)) cp →
        K4IndexTieAt (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread h.𝔇.rw13 c
          y.2 s' (Reading.gl.val ((endRun cp).getD 0 zeroE)))
    (hWt : ∀ blk,
      (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
      ∀ c s mm E ds y cols s',
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      drawsFit blk.rounds ds = true →
      (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y
        cols s' →
      K4WeightsTieK (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread h.𝔇.d1
        h.𝔇.rw13 c y.2 s'
        (wmOf (k4Wit (k4PubAt cF k x) cells weights k4Tokens (k4LookAt (k4PubAt cF k x))
          mm.st.input).w)) :
    ExchangeAtS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k
      (Item.wo m) :=
  k4_exchange_wo_seat h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said Lh
    (half_atPure h Lh hA cells weights (fun _ _ => k4LookAt) hL ho)
    (fun fr _ => lookFits_lookAt h Lh fr) (hTk_of h Vd w₁ Lh hVd) hMask
    (lookAt_isK3 h Lh w₁.x (lookBase_head h Lh)).2 hIx hWt

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_exchange_wo_lookAt
