-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/MgAt/Runs.lean: THE MAP OF NAMES AT A REAL CHAIN (`runsAt links`,
Johnson/Desc/Sound/BordersForms.lean: the term that is meant for the letter runs of the composed
filling), SEGMENT BY SEGMENT: which runs each of the table's names stands for. Theorems, for the
laws
that ask "my run stands under that name".
  `runsAt_of`: at a segment of sort sub the map is the table's own `First.runsOf sub`.
  `runs_layers`, `runs_attention`, `runs_head`: at each sort, every name with its list, written out.
  `mem_runsAt`: membership at a segment from membership in the table's list.
Limits: equations of small lists, by evaluation. Nothing on any run. Nothing on soundness.

-/
import Johnson.Desc.Sound.BordersForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart runsOf)

theorem runsAt_of (links : List ModelPart) (m : ℕ) (sub : ModelPart) (h : links[m]? = some sub) (k : ℕ)
    (r : String) : runsAt links m k r = runsOf sub k r := by
  unfold runsAt
  rw [h]
  rfl

theorem mem_runsAt (links : List ModelPart) (m : ℕ) (sub : ModelPart) (h : links[m]? = some sub) (k : ℕ)
    (r : String) (p : ℕ × String) (hp : p ∈ runsOf sub k r) : p ∈ runsAt links m k r := by
  rw [runsAt_of links m sub h k r]
  exact hp

/-- A feed-forward segment's names. -/
theorem runs_layers :
    runsOf .layers 2 "objects" = [(1, "objects"), (1, "guests")] ∧
    runsOf .layers 3 "own" = [(2, "front"), (2, "back")] ∧
    runsOf .layers 5 "small" = [(4, "K8.equations")] ∧
    runsOf .layers 7 "objects" = [(6, "objects"), (6, "guests")] ∧
    runsOf .layers 2 "planes" = [] ∧ runsOf .layers 2 "join" = [] := by decide

/-- An attention segment's names. -/
theorem runs_attention :
    runsOf .attention 2 "objects" = [(1, "objects"), (1, "guests")] ∧
    runsOf .attention 2 "planes" = [(1, "planes")] ∧
    runsOf .attention 2 "join" = [(2, "join")] ∧
    runsOf .attention 3 "own" = [(2, "first"), (2, "keys"), (2, "second")] ∧
    runsOf .attention 5 "small" = [(4, "K8.equations")] ∧
    runsOf .attention 7 "objects" = [(6, "objects"), (6, "guests")] := by decide

/-- The head's segment's names. -/
theorem runs_head :
    runsOf .head 3 "objects" = [(2, "objects"), (2, "guests")] ∧
    runsOf .head 3 "planes" = [(2, "planes")] ∧
    runsOf .head 4 "join" = [(3, "join")] ∧
    runsOf .head 4 "own" = [(3, "norm"), (3, "policy"), (3, "logits")] ∧
    runsOf .head 4 "weights" = [] ∧
    runsOf .head 6 "small" = [(5, "K8.equations")] ∧
    runsOf .head 8 "objects" = [(7, "objects"), (7, "guests")] ∧
    runsOf .head 9 "merged" = [(8, "the merge")] := by decide

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.runsAt_of
#print axioms VerifiableInference.Desc.Sound.mem_runsAt
#print axioms VerifiableInference.Desc.Sound.runs_layers
#print axioms VerifiableInference.Desc.Sound.runs_attention
#print axioms VerifiableInference.Desc.Sound.runs_head
