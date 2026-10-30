-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverData.lean: three lemmas that say, for the data that a
description computes from a proof file, that each chain's data fit the declared rounds of that
chain's gated sub-protocols, one by one (`KindFits`, Honest/Law/Due.lean). This is the hypothesis
`hfit` of `debt_busy` (Honest/Law/CoverBusy.lean; not in the sealed library) and the hypothesis `h`
of the lemmas of Honest/Law/CoverFitAt.lean (not in the sealed library) and
Honest/Law/CoverCall.lean (not in the sealed library).

`kinds_of_data` (Honest/Law/DataKinds.lean) proves the fit for the lists of declared rounds that the
library's `FileDescription.roundsDeclaredByBlocks` returns; for the first chain, for that list without its last round. The
lemmas here rewrite these lists as the rounds of the gated sub-protocols. In the first chain the
gated sub-protocols are all but the last one, whose one round is the sealing round.

  1  `kindFits_first`   the first chain, without its last sub-protocol
  2  `kindFits_shared`, `kindFits_second`   the other two chains

Limits.
  * That the first chain's last sub-protocol has exactly one round (`he`) is a hypothesis.
  * The lemmas say which entry and kind each round's data bear. They say nothing on how challenges
    are drawn.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.DataKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes.Maker (WholeD)

variable {Xi : Type}

/-- The first chain's data fit the rounds of its sub-protocols before the last. `pre₁`: these
sub-protocols; `e₁`: the last one; `z`: its one round. -/
theorem kindFits_first {F : FileDescription Xi} {file : String} {D : WholeD} (h : F.data file = .ok D)
    {pre₁ : List (Block F.S₁ F.Cl)} {e₁ : Block F.S₁ F.Cl} (cut : F.first.blocksInOrder = pre₁ ++ [e₁])
    {z : Fmt.DeclaredRound} (he : e₁.rounds = [z]) :
    List.Forall₂ KindFits D.ds₁ (pre₁.flatMap (·.rounds)) := by
  have e : F.roundsDeclaredByBlocks.1.dropLast = pre₁.flatMap (·.rounds) := by
    show (F.first.blocksInOrder.flatMap (·.rounds)).dropLast = _
    simp only [cut, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, he,
      List.dropLast_concat]
  rw [← e]
  exact (kinds_of_data h).1

/-- The shared chain's data fit its rounds. -/
theorem kindFits_shared {F : FileDescription Xi} {file : String} {D : WholeD}
    (h : F.data file = .ok D) : List.Forall₂ KindFits D.ds₂ (F.shared.blocksInOrder.flatMap (·.rounds)) :=
  (kinds_of_data h).2.1

/-- The second chain's data fit its rounds. -/
theorem kindFits_second {F : FileDescription Xi} {file : String} {D : WholeD}
    (h : F.data file = .ok D) : List.Forall₂ KindFits D.ds₃ (F.second.blocksInOrder.flatMap (·.rounds)) :=
  (kinds_of_data h).2.2.1

end ProofFile.Honest

#print axioms ProofFile.Honest.kindFits_first
#print axioms ProofFile.Honest.kindFits_shared
#print axioms ProofFile.Honest.kindFits_second
