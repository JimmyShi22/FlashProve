-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Live/BehindStatement.lean: BEHIND A YES OF THE DECISION OF THE MERGE OF THE CLAIMS
ON THE WEIGHTS THE CONDITION `MergeLive` (RunStatement.lean of this folder) HOLDS, WHERE NONE OF THE
CHALLENGES THAT THE SUMCHECK's ROUNDS DREW READS AS 0: one definition with code, and A STATEMENT: a
definition of a proposition. NOTHING IS PROVED IN THIS FILE, and it is none of the library's goals:
it is a lemma's statement. The texts are the description's; no prover is named.

  `laterDraws rs`          the elements that the rounds from number 1 on have drawn, in their order:
                           of the merge's lk + 4 rounds these are the round that draws the factor of
                           the summand, the lk rounds in the column bits, the round in the further
                           variable, and the round of the end value, which draws none. (Number 0
                           batches the claims.)
  `HeadMergeLiveBehind`    where the decision (`headMergeDecide`,
                           Johnson/Desc/First/Fork/MergeKind.lean) says yes from s to s' on the
                           rounds rs; a, x: the head's own fields and what the head heard, in front;
                           the slot of the claim's value lies below the ledger's next free number;
                           and every element of `laterDraws rs` reads other than 0:
                           `MergeLive P.lay.lk a.F.next x.sV s'`

Limits. The yes is a premise. That the slot of the claim's value lies below the next free number is
a premise on the state in front. How often a challenge reads as 0 is not said. Nothing on any
property.
-/
import Johnson.Desc.K11.Live.RunStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Live
open OnBytes (E)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.First (S HeadOwn)

/-- **The elements drawn from round number 1 on.** -/
def laterDraws (rs : List Fmt.RoundView) : List E :=
  (rs.drop 1).flatMap fun r => r.drawn.elems.map E.ofTriple

/-- The statement behind the decision's yes. Not proved here; a lemma's statement, none of the
library's goals. -/
def HeadMergeLiveBehind : Prop :=
  ∀ (P : HeadMergeP) (s s' : S) (rs : List Fmt.RoundView) (a : HeadOwn)
    (x : OnBytes.Model.Head.Heard),
    headMergeDecide P s rs = .ok s' → s.here = .head a → a.x = some x → x.sV < a.F.next →
    (∀ e ∈ laterDraws rs, Reading.gl.val e ≠ 0) →
    MergeLive P.lay.lk a.F.next x.sV s'

end Johnson.Desc.First.ForkMerge.Live

#print axioms Johnson.Desc.First.ForkMerge.Live.laterDraws
#print axioms Johnson.Desc.First.ForkMerge.Live.HeadMergeLiveBehind
