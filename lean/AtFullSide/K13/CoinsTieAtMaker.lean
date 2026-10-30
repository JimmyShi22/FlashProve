-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K13/CoinsTieAtMaker.lean: kind K13, the members' batching: THE KIND's TIE `CoinsTie` AT
THE BORDER 355 (Johnson/Desc/ProofFile/Honest/K13/ExchangeAtM3.lean), AT THE THREAD OVER THE PROVER
AND THE BOOK THAT THE MAKER `onlineProverFromPublicFiles` RETURNS, AT ANY FILLING: FROM KIND K1's RECORD OF PREMISES AT
THE OPENING (`K1Seated`) AND THAT THE OPENING's JOB HAS THE PLAN AND THE RIDE OF THE MAKER's OWN
GROUND. One statement with its proof: a call; no definition. THE FULL SIZE ALONE, AT THE FORMAT's
SECOND HASH FUNCTION ALONE: under the library's one hypothesis h (`P5J.AtMgA`) and hA: the maker
returns A.

What the tie says: the mask entries under the slots that the verifier takes at the batching are the
coins that the book lends the kind's sumcheck's part.

How it differs from `k13_coinsTie_of_five` (CoinsTieFive.lean of this folder), which has five
premises. Two are not asked: "the thread's book is the one that the book's maker returns": the
thread is typed at A.B, and that is this book (`atPure_book_at_head`,
Johnson/Desc/ProofFile/Honest/K14/AtPureBookAtHead.lean); and the library's "opened", which h has.
Two are said at the ground at which the prover is laid, A.G, not at the description's own: the two
are one value (`base_ground_atPure`, Johnson/Desc/ProofFile/Honest/AtBaseGround.lean).

WHAT IS LEFT: K: the record at the opening, number 2 of the first chain: A PREMISE, WHOLE: its field
`msgs` is the tie between the Script and the sender's text. hP, hR: the job's plan and ride. Kind
K1's own law gives this record at A.B from two premises on the filling's lots and the fields msgs
and pads, at a job whose plan and ride are these (`k1Seated_two_at_book`,
Johnson/Desc/ProofFile/Honest/K1/Law/RecordAtBookFill.lean).

Limits. Those of CoinsTieFive.lean hold here. It speaks at each run's coins one by one, and is no
statement on their distribution. Where the thread stands nowhere the tie holds for nothing; so it
would where the book's lending to the kind's row erred: at A.B it returns, under h and hA: by
`k13_lendRow_at_head` (LendRowAtHead.lean of this folder), whose premise on the book is what
`atPure_book_at_head` says of A.B; no statement joins the two.

What is not claimed. That the record holds at any Script. That h holds at any public files; that the
maker returns. Nothing on soundness, completeness or hiding.
-/
import AtFullSide.K13.CoinsTieFive
import Johnson.Desc.ProofFile.Honest.K14.AtPureBookAtHead
import Johnson.Desc.ProofFile.Honest.AtBaseGround
import Johnson.Desc.ProofFile.Honest.AtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K13
open OnBytes
open ProofFile.Honest ProofFile.Honest.K13
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.K1 (firstPar gpOf)
open VerifiableInference.Desc.Sound (MsgT Mem)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K1 (K1Seated PlaceIn)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- THE RECORD IS A PREMISE. **`CoinsTie` AT 355, AT THE MAKER's PROVER AND BOOK**, at any filling:
from kind K1's record at the opening, and that its job has the plan and the ride of the maker's own
ground. -/
theorem k13_coinsTie_at_maker (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {W₀ Rc Tr X₀ X' : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (Q : Script A.B (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w₁ : Local W₀ Rc ProofFile.Inst Tr) {weights : W₀ → Weights} {pile : PileOf ProofFile.Inst}
    {blk₂ : Block TS ProofFile.Cl} {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst}
    {J : K1.SendJob (PlaceIn ProofFile.Inst) X'} {own₀ : X'} {seats₀ : List (ℕ × ℕ)} {ms : List Mem}
    {rad : ℕ → ℕ}
    (K : K1Seated (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) 2 blk₂ wit J
      own₀ .opening (P5J.At.arr Zp) seats₀ ms rad)
    (hP : J.P = firstPar A.G.first (gpOf Zp))
    (hR : J.ride = K1.rideOf (K1.firstFold A.G.first)) :
    CoinsTie (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) 355 weights pile h.𝔇.P13
      (k13ReaderAt h) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hG : Bs.G₀ = A.G := base_ground_atPure O.made hA (atPure_at_laid h.laid hA).1
  exact k13_coinsTie_of_five h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ O K
    (by rw [hG]; exact hP) (by rw [hG]; exact hR) (K14.atPure_book_at_head h hA)

end AtFullSide.K13

#print axioms AtFullSide.K13.k13_coinsTie_at_maker
