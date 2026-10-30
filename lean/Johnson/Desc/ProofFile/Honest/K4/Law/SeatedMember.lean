-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/SeatedMember.lean: CONDITIONAL. A statement with its proof.

What is here: THE SEAT OF THE FEED-FORWARD LAYERS' OWN ROUNDS (the sub-protocol K4) AT THE THREAD
WITH THE LIBRARY's OWN VALUES: `K4Seated` (Law/Seated.lean) at `lettersHead`'s thread, at the
member's own public data (`k4PubAt`, Law/DearTop.lean). The words member, thread and seat:
Law/SeatedHead.lean's paragraph "Words". Law/SeatedHead.lean's `k4Seated_letters` leaves four
hypotheses: hQ, half, front, fits. HERE hQ AND front ARE PROVED (`k4Pub_head`, Law/FrontCount.lean;
the count of rounds in front is the data's own field), AND fits, the public test `k4Fits` at every
list of challenges that the rounds in front can sample, IS BROUGHT DOWN TO TWO OF ITS FOUR TESTS
(`fits_member`, Law/FitsMember.lean): hLk: the test on the sizes of what `look` returns
(`k4LookFits`), AT EVERY SUCH LIST: a law on `look`: no evaluation gives it; hTk: the test on the
run's tokens (`k4TokensFit`): one evaluation at the run's request.

Not shown here. half: that the prover's list of halves holds K4's half at the member's place: a
hypothesis. hLk and hTk: hypotheses, on the parameters `look` and `tokens`, which a caller lays (hTk
at `k4Tokens`, from a test on the request: `hTk_of`, Law/TokensSeat.lean). That h can hold: the side
library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). Of h together with half, hLk and hTk no example is known to us (`LaidK4`: h gives it at
each group: `laid_at`, Law/LaidAtGroup.lean). THE FULL SIZE ALONE, and the format's second hash function
alone. `K4Seated` is a hypothesis's form: that the half stands at the member; it says nothing on
what any part sends. WHAT THE TEST DOES NOT SEE: at the small synthetic plan, with the number of
column bits of the weights' layout one higher, all eighteen clauses of `k4Fits` still say true
(Law/FitsXBends.lean). Beneath it stand uses of kernel_rfl, comparisons by Lean's own kernel: one in
each of the eight facts of Johnson/Road/K4/C/Free/ that it calls, and seven that these share
(Johnson/Road/K4/RowHead/ClosedAt.lean, ClosedTies.lean), five of them with the parameter file's
eight free numbers as a variable; and one `decide +kernel` (`k4_front_closed`, Law/FrontClosed.lean,
through `k4Pub_head`). No independent checker has replayed them. IT RESTS BY NAME ON A STATEMENT OF
A FILE UNDER Johnson/Goal/ (`P5J.pins_of_laid`, through `cuts_head`, Law/FrontCount.lean). Its
imports reach files under Johnson/Goal/: a program's walk from import to import, which reads import
lines alone and stops unopened at Johnson/Goal/, ThirdParty/, Johnson/D/, Johnson/Bridge/ and
Cb/Bridge*, stopped at 71 modules under Johnson/Goal/: a floor (with h): A LAW, NOT A PART: no file
that defines a part of the proof file's description may import this one. Nothing on soundness, on
completeness or on any other property. No property is claimed.

  `k4Seated_member`   **`K4Seated` at the thread, from half, hLk and hTk**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FitsMember
import Johnson.Desc.ProofFile.Honest.K4.Law.FrontCount
import Johnson.Desc.ProofFile.Honest.K4.Law.SeatedHead

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
open ProofFile.Honest.K4.SeatedHead (LaidK4 k4Seated_letters)

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

/-- CONDITIONAL on h, `LaidK4`, half, hLk and hTk. **`K4Seated` AT THE THREAD, AT THE MEMBER's OWN
PUBLIC DATA, FROM half, hLk AND hTk.** -/
theorem k4Seated_member (Lh : LaidK4 Zp cF k m g x blk) {cells : Tr → Cells}
    {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard}
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights tokens look (k4PubAt cF k x)))
    (hLk : ∀ fr, drawsFit (declsTo cF.blocksInOrder k) fr = true →
      k4LookFits (k4PubAt cF k x) (look (k4PubAt cF k x) fr) = true)
    (hTk : Vd w → k4TokensFit (k4PubAt cF k x) (tokens w.x) = true) :
    K4Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k cells weights
      tokens look (k4PubAt cF k x) { x.2 with k3Runs := true } blk :=
  k4Seated_letters h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lh (k4Pub_head h Lh) half rfl
    fun fr hd hV => fits_member h Lh (hLk fr hd) (hTk hV)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4Seated_member
