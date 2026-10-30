-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/LookJoin.lean: CONDITIONAL.

What is here. The hypothesis `LookRestIx` (Law/LookMemberHead.lean) under h : AtMgA alone, by one
call of `look_rest_link` (Johnson/Desc/ProofFile/Honest/K3/Law/Thread/AtLink.lean, by the writers of
Honest/K3/); and so `AcceptedS` at the member of the feed-forward layers' rounds with no hypothesis
on what the lookup has heard. Statements and proofs: calls. Words: Law/ElevenHead.lean's head.

Not shown here. THAT THE TOP's HYPOTHESES CAN HOLD TOGETHER: no example is known (by binder, beside
h: `k4_accepted_top`: hB, Lh, hQ, half, hTok, hf). `lookRestIx_head` takes h and g < 12 alone, and
of h alone: the side library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). `Behind` and `AcceptedS` speak only where the thread stands: that it stands at any run is
not shown. NOT COMPLETENESS. THE MEMBER's STEP TESTS NO SENT VALUE (Law/Hears.lean): it accepts
every play of the right shape, a false one too. WHAT STAYS FOR `AcceptedS`, BY NAME: the structure
Lh : LaidK4 on the member (h and AtK4 give one) · a proof of `k4PublicX (P5J.At.X Zp) = true`
(Law/PublicX.lean; Zp is a variable under h, so no evaluation gives it; Law/DearX.lean has it under
h: `publicX_head`) · hQ (that `k4PubOf` returns the public data at the member's parameters:
Law/FrontCount.lean has it under h and `LaidK4`) · half (the prover's list of halves holds K4's half
at the member's place; whoever shows it out of K4's lot's honest side shows `k4TableFits` of the
public data beside) · the test on the tokens that the verifier's state holds (`tokensFit`), in the
first group alone (Law/TokensHead.lean has it under h and `LaidK4`; Law/LookJoinDear.lean asks
neither hQ nor this test) · that where the fall says nothing the honest side's test on one sampled
element says nothing. THE FULL SIZE ALONE, and at `OnBytes.secondHashFunction`, the format's second hash function,
alone. A LAW, NOT A PART: no file that defines a part of the proof file's description may import
this one: its imports reach Johnson/Goal/. Transitive imports: those of Law/PublicOne.lean and of
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/AtLink.lean: not counted. No property is claimed.

  `lookRestIx_head`   **`LookRestIx cF.blocksInOrder (28 g + 3)` under h, at each group g below 12.**
  `k4_accepted_top`   **`AcceptedS` at the member.**

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PublicOne
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Desc.First.K4.RtPub (tokensFit)
open OnBytes.Road.K4 (parOf)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Claim Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **`LookRestIx` UNDER h ALONE.** -/
theorem lookRestIx_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12) :
    LookRestIx cF.blocksInOrder (28 * g + 3) := fun blk hb =>
  ProofFile.Honest.K3.Law.AtThr.look_rest_link h (2 * g) (by omega) blk (by
          rw [border_calls hg]
          exact hb)

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **`AcceptedS` AT THE MEMBER**, with no hypothesis on what the lookup has heard. CONDITIONAL. -/
theorem k4_accepted_top (hB : k4PublicX (P5J.At.X Zp) = true)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    {fall : Nat → S → List Fmt.Drawn → Option String} (hQ : k4PubOf Zp x.2 = some Qp)
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights tokens look Qp))
    (hTok : g = 0 → ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said k c s mm E →
      tokensFit { (parOf x).P with tokv := seatS.tokv s } (parOf x).g = true)
    (hf : ∀ s ds, fall k s ds = none → k4CoinZero Qp ds = none) :
    AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall k :=
  k4_accepted_one h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hB Said Lh hQ half
    (lookRestIx_head h Lh.lt) hTok hf

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.lookRestIx_head
#print axioms ProofFile.Honest.K4.k4_accepted_top
