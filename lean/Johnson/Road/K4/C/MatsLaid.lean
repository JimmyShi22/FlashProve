-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/MatsLaid.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the prover's side: the public hypothesis
MatsLaid (Feats.lean) at every plan whose list of matrices has the rows and columns of the layout's
own list (matsR, Johnson/Road/FormsKeysRun.lean), in a group of the layout: by the library's law on
that list (tails_sizes, Johnson/Road/FormsKeysTab.lean). Statement and proof.

  `matsLaid_of_tails`   MatsLaid.

Not shown here. That the two premises hold at any plan: no example is known.
No property is claimed.
-/
import Johnson.Road.K4.C.Feats
import Johnson.Road.FormsKeysTab

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (matIx)
open OnBytes.Desc.First.K4.Honest (K4Pub matsOf)

/-- **Each part of each of the six matrices stands in the plan's list**, off the matrix of the
lookup's planes. -/
theorem matsLaid_of_tails (Q : K4Pub) (hm : matsOf Q = matsR Q.P.y Q.g)
    (hg : Q.g < Q.P.y.NGr) : MatsLaid Q := by
  intro mat hmat part hp
  obtain ⟨hi, h1, h2⟩ := (tails_sizes Q.P.y hg).2 mat part (by omega) hp
  have hB : (matIx Q.P.y).iB = Q.P.y.parts.getD 0 0 + Q.P.y.parts.getD 1 0 + 1 := rfl
  refine ⟨?_, ?_⟩
  · rw [hB]
    interval_cases mat
    · have e : firstM Q.P.y 0 = 0 := rfl
      have hp' : part < Q.P.y.parts.getD 0 0 := hp
      omega
    · have e : firstM Q.P.y 1 = Q.P.y.parts.getD 0 0 := rfl
      have hp' : part < Q.P.y.parts.getD 1 0 := hp
      omega
    · have e : firstM Q.P.y 2 = Q.P.y.parts.getD 0 0 + Q.P.y.parts.getD 1 0 := rfl
      have hp' : part < 1 := hp
      omega
    · have e : firstM Q.P.y 3 = Q.P.y.parts.getD 0 0 + Q.P.y.parts.getD 1 0 + 2 := rfl
      omega
    · have e : firstM Q.P.y 4 = Q.P.y.parts.getD 0 0 + Q.P.y.parts.getD 1 0 + 4 := rfl
      omega
    · have e : firstM Q.P.y 5 = Q.P.y.parts.getD 0 0 + Q.P.y.parts.getD 1 0 + 3 := rfl
      omega
  · rw [hm]
    unfold matsR
    rw [getD_map_sizes _ hi, h1, h2]

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.matsLaid_of_tails
