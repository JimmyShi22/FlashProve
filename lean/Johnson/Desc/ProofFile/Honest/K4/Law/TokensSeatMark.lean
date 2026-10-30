-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TokensSeatMark.lean: CONDITIONAL.

What is here. The clause hVd of `hTk_of` and `k4Seated_tokens` (Law/TokensSeat.lean: at the input w
the request passes the verifier's public test on its words) from hmark: the chain's first state at
the input's public part bears no mark. `enters_head` (Honest/Thread/EntersHead.lean) has a premise
of that name at the run's instance ξ; at w := the run's own input R.own the two are one UP TO
R.own.x = ξ, which is not called here: Law/TokensSeatReady.lean has it (`own_x_of_ready`), and
`k4Seated_ready` there takes both premises as `enters_head` has them. Why hmark is enough: the start
keeps its first state only where the test accepts, and lays the marked blank state else
(`reqFine_of_start`). So `K4Seated` at the thread, at the tokens that K4's own half reads, asks of
the tokens nothing beyond hmark (`k4Seated_mark`).

Not shown here. hmark IS A HYPOTHESIS. It is false at a request file of another length; with a token
from the size of the vocabulary on; where the covered range is empty or ends beyond the plan's
number of tokens; and wherever the public part's own first state bears a mark. That h can hold: the
side library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). Of h together with `LaidK4`, half, hLk and hmark no example is known to us. half and hLk:
hypotheses, as in Law/SeatedMember.lean. It reads only the public request; it says nothing about the
model's values at these tokens. `hVd_of_mark` is general; the two others are only for the full-size
model and the format's second hash function.
No property is claimed.
A LAW, NOT A PART: no file that defines a part of the proof file's description may import this one:
its imports reach modules under Johnson/Goal/, as those of Law/TokensSeat.lean do.

  `hVd_of_mark`   **hVd, at every Vd.**
  `hTk_of_mark`   **hTk.**
  `k4Seated_mark`   **`K4Seated` at tokens := `k4Tokens`, from half, hLk and hmark.**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.TokensSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
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
  {k m g : ℕ} {x : Bool × Par} {blk : Block TS ProofFile.Cl}

/-- CONDITIONAL on hmark. **hVd**, at every Vd. -/
theorem hVd_of_mark (hmark : (ProofFile.startS Zp w.x.pub).failed = none) :
    Vd w → reqFine Zp w.x.pub = true :=
  fun _ => reqFine_of_start hmark

include h in
/-- CONDITIONAL on h, `LaidK4` and hmark. **hTk.** -/
theorem hTk_of_mark (Lh : LaidK4 Zp cF k m g x blk)
    (hmark : (ProofFile.startS Zp w.x.pub).failed = none) :
    Vd w → k4TokensFit (k4PubAt cF k x) (k4Tokens w.x) = true :=
  hTk_of h Vd w Lh (hVd_of_mark Vd w hmark)

/-- CONDITIONAL on h, `LaidK4`, half, hLk and hmark. **`K4Seated` AT THE THREAD, AT THE LOT's OWN
READER OF THE TOKENS.** -/
theorem k4Seated_mark (Lh : LaidK4 Zp cF k m g x blk) {cells : Tr → Cells}
    {weights : W₀ → Weights} {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard}
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights k4Tokens look (k4PubAt cF k x)))
    (hLk : ∀ fr, drawsFit (declsTo cF.blocksInOrder k) fr = true →
      k4LookFits (k4PubAt cF k x) (look (k4PubAt cF k x) fr) = true)
    (hmark : (ProofFile.startS Zp w.x.pub).failed = none) :
    K4Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k cells weights
      k4Tokens look (k4PubAt cF k x) { x.2 with k3Runs := true } blk :=
  k4Seated_tokens h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lh half hLk
    (hVd_of_mark Vd w hmark)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.hVd_of_mark
#print axioms ProofFile.Honest.K4.hTk_of_mark
#print axioms ProofFile.Honest.K4.k4Seated_mark
