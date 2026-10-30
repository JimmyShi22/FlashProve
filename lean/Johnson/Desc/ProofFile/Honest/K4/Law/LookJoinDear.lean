-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/LookJoinDear.lean: CONDITIONAL.

What is here. `AcceptedS` AT THE MEMBER OF THE FEED-FORWARD LAYERS' ROUNDS, AT THE FIRST CHAIN's
THREAD (`lettersHead`), FROM h : AtMgA, `LaidK4`, half AND hf ALONE: no hypothesis on what the
lookup has heard (Law/LookJoin.lean), on the plan beside what half holds (Law/DearX.lean), on
`k4PubOf` (Law/FrontCount.lean) or on the state's tokens (Law/TokensHead.lean). One statement: a
call. Words: Law/ElevenHead.lean's head.

Not shown here. THAT h CAN HOLD: the side library AtFullSide proves, with no hypothesis, that h has
a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). OF h TOGETHER WITH half AND hf NO EXAMPLE IS KNOWN TO US (`LaidK4`
asks nothing beyond h: `laid_head`, Law/SeatedHead.lean, at the library's `atK4_full`). `Behind` and
`AcceptedS` speak only where the thread stands: that it stands at any run is not shown. NOT
COMPLETENESS. THE MEMBER's STEP TESTS NO SENT VALUE (Law/Hears.lean): it accepts every play of the
right shape, a false one too. WHAT STAYS FOR `AcceptedS`, BY NAME: the structure Lh : LaidK4 on the
member (h and AtK4 give one) · half (the prover's list of halves holds K4's half at the member's
place, at the public data `k4PubAt`; whoever shows it out of K4's lot's honest side shows
`k4TableFits` of that public data beside: A TEST ON THE PLAN, Honest/K4/Part.lean) · hf (where the
fall says nothing the honest side's test on one sampled element says nothing). THE FULL SIZE ALONE,
and at `OnBytes.secondHashFunction`, the format's second hash function, alone. TEN OF THE FOURTEEN CLAUSES OF THE TEST
ON THE PLAN REST WHOLLY ON CHECKS BY LEAN's OWN KERNEL (`kernel_rfl`: seven facts under
Johnson/Road/K4/C/Free/, over Johnson/Road/K4/RowHead/ClosedAt.lean and ClosedTies.lean); three more
lean on one such fact beside a law; no independent checker has replayed them. A LAW, NOT A PART: no
file that defines a part of the proof file's description may import this one: as Law/DearTop.lean
says of itself. Transitive imports: those of Law/LookJoin.lean and of Law/DearTop.lean: not counted.
No property is claimed.

  `k4_accepted_last`   **`AcceptedS` at the member.**

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.LookJoin
import Johnson.Desc.ProofFile.Honest.K4.Law.DearTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Claim Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL. **`AcceptedS` AT THE MEMBER**, from h, `LaidK4`, half and hf alone. -/
theorem k4_accepted_last (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop)
    {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard}
    {fall : Nat → S → List Fmt.Drawn → Option String}
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights tokens look (k4PubAt cF k x)))
    (hf : ∀ s ds, fall k s ds = none → k4CoinZero (k4PubAt cF k x) ds = none) :
    AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall k :=
  k4_accepted_dear h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said Lh half (lookRestIx_head h Lh.lt)
    hf

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_accepted_last
