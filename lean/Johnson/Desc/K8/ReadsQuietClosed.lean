--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/ReadsQuietClosed.lean: behind a yes of either block of
Johnson/Desc/K8/ReadsQuiet.lean the carried record's record of the smallness test (S.tl?,
Johnson/Desc/First/State.lean) is closed, and the list that it holds is the carried record's own
list of tables (S.funs?) behind the block.

So a block that is run on the very record that this block leaves finds: the list of tables is closed
(funClosed = true), and it is the list that the claims take.

Main names: layers_closed, head_closed.

What is not claimed. That the list is the right one. Which block stands next at a link, or that
none between this one and the matrix's draw turns the record of the smallness test: that is a matter
of the chain's make, not shown here. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K8.ReadsQuietFuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K8.ReadsQuiet
open OnBytes OnBytes.Model OnBytes.Model.Head
open VerifiableInference.Desc.First (S)

/-- **Behind the block at a layers' link the list is closed, and it is S.funs?.** -/
theorem layers_closed {P : PG} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (layers P).decide s rs gs = .ok s') :
    ∃ tl' funs, s'.tl? = some tl' ∧ tl'.funClosed = true ∧ tl'.funs = funs ∧
      s'.funs? = some funs := by
  obtain ⟨a, own, tl', _, ho, hc, hs⟩ := layers_ok h
  obtain ⟨h1, h2, _⟩ := closed_fields hc
  refine ⟨tl', own.funs, ?_, h1, h2, ?_⟩
  · subst hs
    simp [S.tl?]
  · subst hs
    simp [S.funs?, ho]

/-- **Behind the block at the head's link the list is closed, and it is S.funs?.** -/
theorem head_closed {P : PH} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (head P).decide s rs gs = .ok s') :
    ∃ tl' funs, s'.tl? = some tl' ∧ tl'.funClosed = true ∧ tl'.funs = funs ∧
      s'.funs? = some funs := by
  obtain ⟨a, cov, x, t, tl', _, hop, _, _, _, hc, hs⟩ := head_ok h
  obtain ⟨h1, h2, _⟩ := closed_fields hc
  refine ⟨tl', t.funs, ?_, h1, h2, ?_⟩
  · subst hs
    simp [S.tl?, hop]
  · subst hs
    simp [S.funs?, hop]

end VerifiableInference.Desc.K8.ReadsQuiet
