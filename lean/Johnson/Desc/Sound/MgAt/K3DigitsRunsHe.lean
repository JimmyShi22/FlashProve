-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/MgAt/K3DigitsRunsHe.lean: the lookup on the digits of a segment's approximate
range proof: THE PREMISES «he» OF objects_pass_dig, planes_pass_dig, join_pass_dig
(MgAt/K3DigitsFormsOurs.lean), small_pass_dig (MgAt/K3DigitsFormsSmall.lean) AND objIn_dig
(MgAt/K3DigitsObjIn.lean): «what the table's name lists» (First.runsOf,
Johnson/Desc/First/Borders.lean): AT EACH SORT OF SEGMENT AT WHICH THE NAME IS LIVE, BY «decide»: SO
THAT NONE OF THESE PREMISES IS UNMEETABLE. The name "objects" stands for TWO runs: "objects" and
"guests". NO SOUNDNESS IS CLAIMED.

Main names. Each: for every sort of segment (for planes, join: but the layers', where the name is
idle).
  he_objects_calls: runsOf sub (2 + shift sub) "objects" = [(1 + shift sub, "objects"), (1 + shift
    sub, "guests")].
  he_objects_digits: runsOf sub (7 + shift sub) "objects" = [(6 + shift sub, "objects"), (6 + shift
    sub, "guests")].
  he_small: runsOf sub (5 + shift sub) "small" = [(4 + shift sub, "K8.equations")].
  he_planes: sub ≠ layers → runsOf sub (2 + shift sub) "planes" = [(1 + shift sub, "planes")].
  he_join: sub ≠ layers → runsOf sub (joinAt sub) "join" = [(2 + shift sub, "join")].
OBJECT. The table's map of names.
Used by K3DigitsFormsJoin.lean and K3DigitsFormsKept.lean (Johnson/Desc/Sound/MgAt/) and 3 more.
LETTERS. sub.
IS IT EMPTY? No premise but «not the layers'» at two.


Compiled with the whole library.


Limits. The like lists at closed numbers: runs_layers, runs_attention, runs_head
(Johnson/Desc/Sound/MgAt/Runs.lean).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.First (ModelPart runsOf shift joinAt)

theorem he_objects_calls (sub : ModelPart) :
    runsOf sub (2 + shift sub) "objects" =
      [(1 + shift sub, "objects"), (1 + shift sub, "guests")] := by
  cases sub <;> decide

theorem he_objects_digits (sub : ModelPart) :
    runsOf sub (7 + shift sub) "objects" =
      [(6 + shift sub, "objects"), (6 + shift sub, "guests")] := by
  cases sub <;> decide

theorem he_small (sub : ModelPart) :
    runsOf sub (5 + shift sub) "small" = [(4 + shift sub, "K8.equations")] := by
  cases sub <;> decide

theorem he_planes (sub : ModelPart) (h : sub ≠ .layers) :
    runsOf sub (2 + shift sub) "planes" = [(1 + shift sub, "planes")] := by
  cases sub with
  | layers => exact absurd rfl h
  | attention => decide
  | head => decide

theorem he_join (sub : ModelPart) (h : sub ≠ .layers) :
    runsOf sub (joinAt sub) "join" = [(2 + shift sub, "join")] := by
  cases sub with
  | layers => exact absurd rfl h
  | attention => decide
  | head => decide

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.he_objects_calls
#print axioms VerifiableInference.OnPublicFiles.he_objects_digits
#print axioms VerifiableInference.OnPublicFiles.he_small
#print axioms VerifiableInference.OnPublicFiles.he_planes
#print axioms VerifiableInference.OnPublicFiles.he_join
