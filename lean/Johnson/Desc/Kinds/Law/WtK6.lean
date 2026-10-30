-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/WtK6.lean: THE SENTENCE ON THE CLAIM ON THE WEIGHTS AT THE OUTPUT HEAD, AS IT
IS TO STAND IN THE COMPOSED MEANING'S PARAMETER wt (by report): a
definition, in a file that imports nothing of that meaning.

  wtK6 cs arr msR N Wp lay6 num n rb m a y w: at segment 24, AT A WITNESS WHOSE CELLS HOLD AN INDEX,
      WeightAt (Law/MergeClaimAt.lean) at the verifier's state a.2, at the cells and
      the mask row that compCut reads off the witness (Law/K6Cut.lean, at the terms of
      Law/PlanK6At.lean); at every other number nothing.

Why this sentence. The item on the run "weights" is open from the border behind the sub-protocol at
the output head (piece 4 of the head's segment) to the border in front of the merge (piece 9).
WeightAt reads the request, the heard reply, what the lookup and the head HEARD (the fields
lookHeard, x and squaresP of the head's own part) and the ledger's shown values at the slots that x
names. It does not read the field claim of that part, which is laid behind piece 8 alone
(Law/WtNeedsClaim.lean). THAT ALL IT READS STAYS FROM PIECE 5 TO PIECE 8 IS NOT SHOWN HERE. Why the
guard: WeightAt reads the output matrix's weights as
whOf w.cells: 0 where the cells hold no index (Law/K6CutGuarded.lean).

What it does not say. That the sentence rides back past the pieces 5 to 8, or follows from the
merge's own: other files'. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.MergeClaimAt
import Johnson.Desc.Kinds.Law.PlanK6At

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Params (ReqLayout)
open VerifiableInference.OnPublicFiles.Flat (GE InRange)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.Sound (Mem MsgT)

/-- **What the item "weights" says.** -/
def wtK6 {rows cols : Nat} {P Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (msR : List Mem)
    (N : Numbers) (Wp : OnBytes.Model.Verify.Public) (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ)
    (n rb : ℕ) : ℕ → P × S → Strs → Wit (Fin rows → Fin cols → GE) Tok MsgT → Prop :=
  fun m a _ w => m = 24 → InRange w.cells →
    WeightAt Wp a.2
      (compCut cs arr msR N (Meaning.sizesOf Wp) (seatLay Wp lay6 num) Wp (plAt n rb) w).1.toCells
      (compCut cs arr msR N (Meaning.sizesOf Wp) (seatLay Wp lay6 num) Wp (plAt n rb) w).2

end VerifiableInference.Desc.Kinds.Head.Law.AtTable
