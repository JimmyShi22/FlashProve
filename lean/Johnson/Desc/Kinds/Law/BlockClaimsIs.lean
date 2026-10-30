-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/BlockClaimsIs.lean: THE OUTPUT HEAD's BLOCK WITH ITS FOUR RUNS TYPED AT Claim (Johnson/Stored/HeadAddsAtS.lean: blockClaims) IS THE BLOCK AT
THE UNIT TYPE (Johnson/Stored/HeadSeatAt.lean: blockOf), OF WHICH OUR LAWS SPEAK, IN EVERY FIELD BUT WHAT ITS RUNS OF CLAIMS GIVE.
WHY. The fold seats blockOf (a claim is a letter there). On the road on which a link's claims are gathered from the runs that its blocks
state, the block must state its runs at Claim: blockClaims. The law on the block's decision (Law/RowRides.lean: of blockOf W l = some b,
from b.decide) then applies to the other block through decide_is.
WHAT IT DOES NOT SHOW. Nothing of soundness. NOTHING ON WHAT THE RUNS GIVE: the two blocks' runs have different types; runs_named says that they bear the
same four names in the same order, and no more.
  both_or_none · data_is (name, place, planOk, rounds, oracles, before) · decide_is · after_is · runs_named · runs_are ("norm" · "join" · "policy" · "logits")

-/
import Johnson.Stored.HeadAddsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.AtClaim

open OnBytes.Model.Verify (Public)

/-- There is the one just where there is the other. -/
theorem both_or_none (W : Public) (l : Nat) : (blockClaims W l).isSome = (blockOf W l).isSome := by
  unfold blockClaims blockOf
  cases W.H.tl.ix.U.getD 2 none <;> rfl

/-- The data: the same. -/
theorem data_is (W : Public) (l : Nat) :
    (blockClaims W l).map (fun b => (b.name, b.place, b.planOk, b.rounds, b.oracles, b.before)) =
      (blockOf W l).map (fun b => (b.name, b.place, b.planOk, b.rounds, b.oracles, b.before)) := by
  unfold blockClaims blockOf
  cases W.H.tl.ix.U.getD 2 none <;> rfl

/-- **The decision: the same function.** -/
theorem decide_is (W : Public) (l : Nat) :
    (blockClaims W l).map (fun b => b.decide) = (blockOf W l).map (fun b => b.decide) := by
  unfold blockClaims blockOf
  cases W.H.tl.ix.U.getD 2 none <;> rfl

/-- The runs behind the batching: the same. -/
theorem after_is (W : Public) (l : Nat) :
    (blockClaims W l).map (fun b => b.after) = (blockOf W l).map (fun b => b.after) := by
  unfold blockClaims blockOf
  cases W.H.tl.ix.U.getD 2 none <;> rfl

/-- The runs of claims bear the same names in the same order. -/
theorem runs_named (W : Public) (l : Nat) :
    (blockClaims W l).map (fun b => b.claims.map (·.1)) =
      (blockOf W l).map (fun b => b.claims.map (·.1)) := by
  unfold blockClaims blockOf
  cases W.H.tl.ix.U.getD 2 none <;> rfl

/-- The four names, written out, in their order. -/
theorem runs_are (W : Public) (l : Nat) :
    (blockClaims W l).map (fun b => b.claims.map (·.1)) =
      (blockClaims W l).map (fun _ => ["norm", "join", "policy", "logits"]) := by
  unfold blockClaims
  cases W.H.tl.ix.U.getD 2 none <;> rfl

end VerifiableInference.Desc.Kinds.Head.Law.AtClaim

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtClaim.decide_is
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtClaim.data_is
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtClaim.runs_named
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtClaim.runs_are
