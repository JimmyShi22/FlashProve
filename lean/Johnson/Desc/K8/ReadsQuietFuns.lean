-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/ReadsQuietFuns.lean: the list of tables that the two blocks of
Johnson/Desc/K8/ReadsQuiet.lean hand to the closing is the carried record's own list (S.funs?,
Johnson/Desc/First/State.lean), as it stands.

At a layers' link the list lies in the record in front of the block (the link's own rounds laid it):
a yes says that S.funs? gives it there, that this very list went to the closing, and that S.funs?
gives the same list behind the block.
At the head's link the list is made in this very block (tables): in front of it S.funs? need not
give anything. A yes says that the list that went to the closing is the one that S.funs? gives
behind the block.

Main names: layers_funs, head_funs.

What is not claimed. What the closing does with the list that it is handed: that is a matter of the
closing's own text. That the head's tables are the right ones. Nothing on soundness, on an honest
prover or on hiding.

-/
import Johnson.Desc.K8.ReadsQuietLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K8.ReadsQuiet
open OnBytes OnBytes.Model OnBytes.Model.Head
open VerifiableInference.Desc.First (S)

/-- **At a layers' link the closing is handed S.funs? as it stands**, and the list stays. -/
theorem layers_funs {P : PG} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (layers P).decide s rs gs = .ok s') :
    ∃ a funs tl', s.here = .lay a ∧ s.funs? = some funs ∧
      closed P.tl funs a.L s.st = .ok tl' ∧ s'.funs? = some funs := by
  obtain ⟨a, own, tl', ha, ho, hc, hs⟩ := layers_ok h
  refine ⟨a, own.funs, tl', ha, ?_, hc, ?_⟩
  · simp [S.funs?, ha, ho]
  · subst hs
    simp [S.funs?, ho]

/-- **At the head's link the closing is handed the list that S.funs? gives behind the block.** -/
theorem head_funs {P : PH} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (head P).decide s rs gs = .ok s') :
    ∃ a funs tl', s.here = .head a ∧
      closed P.hp.tl funs a.L s.st = .ok tl' ∧ s'.funs? = some funs := by
  obtain ⟨a, cov, x, t, tl', ha, hop, _, _, _, hc, hs⟩ := head_ok h
  refine ⟨a, t.funs, tl', ha, hc, ?_⟩
  subst hs
  simp [S.funs?, hop]

end VerifiableInference.Desc.K8.ReadsQuiet
