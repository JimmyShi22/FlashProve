-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05LeftLens.lean: two lengths of the record that the lookup's hearing leaves
(K3LeftIs, Att/K05Left.lean): it has as many values e and as
many key points as the shape has calls.

Main names: `left_sizes`.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Left

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Cb OnBytes OnBytes.Model

theorem left_sizes {h : Forest.Shape} {lm : ℕ} {F F' : Fork} {g : Forest.Heard} {rs : TwV.Rounds Cb.Gl.E}
    (L : K3LeftIs h lm F F' g rs) : g.e.size = h.NC ∧ g.zk.size = h.NC := by
  have e1 := congrArg List.length L.heardIs.e
  have e2 := congrArg List.length L.heardIs.zk
  unfold Fo.endsOf at e1 e2
  simp only [List.length_map, List.length_range, Array.length_toList] at e1 e2
  refine ⟨?_, e2⟩
  unfold Fo.rdA at e1
  simpa using e1

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.left_sizes
