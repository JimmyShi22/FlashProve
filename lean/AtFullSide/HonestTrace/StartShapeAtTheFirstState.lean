-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/HonestTrace/StartShapeAtTheFirstState.lean   (in the side library: "shapesAtFirst" lies there)

Nothing on hiding. No property of the protocol is claimed. Two theorems, by calls. Public data alone.

TWO SMALL PIECES BENEATH "theDebts" (AtFullSide/Honest/ThreadsPaidAtTheTerm.lean), IN THEIR OWN LETTERS:
* "base_at_the_head": its premise hB: under a head at a return the public part's seat makes a base: ∃ base, baseOf A.Z (pureSeat secondHashFunction A.Z) = .ok base. It is the
  field "made" of the opening that the head's "laid" gives.
* "start_shape_at_the_first_state": the field "startJ" of "ThreadFields" at the third family of the term's letters, J₁ := shapesAtFirst H base: where "okStart"
  accepts the instance, the first chain's first state has the written shape: by "first_chain_start" (Johnson/AtFull/Shape/RuleAtTable.lean) and
  "reqOk_of_okStart" (Johnson/AtFull/Shape/ReqOkOfStart.lean). The base is a letter: the law holds at every g and vals.

Limits. The head and "okStart" are premises. It speaks of border 0 alone: that the shape is carried one member on is the field "carry₁".
Everything here stands at a return of the maker with coins of the type IndexCommitterCoins, the base filling's.
The online prover of E2E/TheHonestProver.lean is made at that filling read through a map of the
coins: another type of coins and another return. Nothing here crosses to it.
-/
import AtFullSide.Honest.ThreadsAtTheTerm
import Johnson.AtFull.Shape.ReqOkOfStart

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace HonestTraceRun.Meets

open ProofFile.Honest ProofFile.Honest.FirstThread
open AtFullSide.Honest (shapesAtFirst)

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **Under a head at a return the public part's seat makes a base.** -/
theorem base_at_the_head (H : HeadAtReturn files A) :
    ∃ base : ProofFile.PureBase, ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok base := by
  obtain ⟨Bs, _, O⟩ := H.head.laid.opened
  exact ⟨Bs, O.made⟩

/-- **The field "startJ" at the run on shapes**: where "okStart" accepts, the first state has the written shape. -/
theorem start_shape_at_the_first_state (H : HeadAtReturn files A) (base : ProofFile.PureBase)
    {x : ProofFile.Inst} (accepts : H.description.okStart x = true) :
    shapesAtFirst H base 0 (H.description.start₁ (H.description.pub x)) :=
  Johnson.AtFull.Shape.first_chain_start H.head x.pub
    (Johnson.AtFull.Shape.reqOk_of_okStart accepts) _ _

end HonestTraceRun.Meets

#print axioms HonestTraceRun.Meets.base_at_the_head
#print axioms HonestTraceRun.Meets.start_shape_at_the_first_state
