-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverCutHead.lean: what `falls_asks` (Honest/Law/CoverAsks.lean)
asks of the first chain's sub-protocols holds of the proof file's first chain under the library's
hypothesis `P5J.AtMg` (Johnson/P5J/AtMg.lean). `members_cut` (Honest/Law/CoverCut.lean) proves the
six statements from one hypothesis: the chain's cut into sub-protocols is the library's written one.
The library proves that hypothesis under `P5J.AtMg`: `cut_of_head`
(Johnson/Road/K4/K4HeadWritten.lean). This file applies the one to the other.

  1  `members_head`   the six statements, under `P5J.AtMg`

Limits.
  * `P5J.AtMg` is a hypothesis. The library's file says that it is not proved in Lean that anything
    satisfies it.
  * `cut_of_head` rests on two rows of the verifier's tests on the public files, which compare the
    plan and the cut with written values.
  * The statements are at the library's full-size parameter set alone.
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverCut
import Johnson.Road.K4.K4HeadWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place KindName Block Chain)
open OnBytes.Maker (WholeD)
open P5J (TS)

/-- Under `P5J.AtMg`: the six statements of `members_cut` at the proof file's first chain `cF`.
`pre`, `e₁`: all its sub-protocols but the last, and the last. -/
theorem members_head {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} (h : P5J.AtMg o Z D r Zp Np cF)
    {pre : List (Block TS ProofFile.Cl)} {e₁ : Block TS ProofFile.Cl} (cut : cF.blocksInOrder = pre ++ [e₁]) :
    (∀ (A : List (Block TS ProofFile.Cl)) (c d : Block TS ProofFile.Cl) (B : List (Block TS ProofFile.Cl)),
      cF.blocksInOrder = A ++ c :: d :: B → fallSeat P5J.At.links d.place = true → d.rounds = [] →
      c.rounds ≠ [] ∧ fallSeat P5J.At.links c.place = true) ∧
    fallSeat P5J.At.links e₁.place = false ∧
    (∀ A b, pre = A ++ [b] → b.rounds ≠ []) ∧
    (∀ A b, pre = A ++ [b] →
      ¬ (markSeat b.place = true ∨ (fallSeat P5J.At.links b.place = true ∧ b.rounds ≠ []))) ∧
    (∀ b ∈ pre, markSeat b.place = true → b.rounds ≠ []) ∧ ∃ z, e₁.rounds = [z] :=
  members_cut (OnBytes.Road.K4.cut_of_head h) cut

end ProofFile.Honest

#print axioms ProofFile.Honest.members_head
