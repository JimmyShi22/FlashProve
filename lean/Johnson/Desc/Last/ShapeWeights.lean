-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeWeights.lean: THE WEIGHTS' "ok" AT THE DOOR OF THE LAST CHAIN: the third of
the tests on the first chain's end (Johnson/Desc/Last/ShapeDoor.lean: "one pending row, and its row
weights are lawful") from a test that can ride along the first chain; and who keeps that test.
Statements and proofs; no definition. THAT IT RIDES ALONG THE WHOLE CHAIN IS NOT SHOWN.

Why. No block asks `Tensor.ok` of a pending row's weights, yet the law on the row (Dot) spends it
(`atDot_of_start`, AtDotStart.lean). It is no prover's
choice: the weights are made by one text and then only scaled. That the made vectors pass lies
in the library (Johnson/Desc/First/Pend/RowOk.lean: `memberWeightsOnRows_ok`,
`pending_rows_weights_ok`, `scale_ok`). Here the rest, as far as the texts at hand reach.

Main names (namespace `VerifiableInference.Desc.Last`).
  THE TEST THAT RIDES: `First.weightsB s` (Johnson/Desc/First/Pend/WeightsB.lean): every vector of
    every row of `First.S.rows s` passes `Tensor.ok`: the pile in front of the batching, the one row
    behind it. As a named item of the first table's promise: Johnson/Desc/First/FillWeights.lean.
  **`weightsClause_of`**: `firstOfS s = some f` and `weightsB s = true` give the door's clause at f:
    that there is just one pending row comes for nothing there.
  WHO KEEPS IT. `weights_pendingKept`: the pile's one writer, where the row laid is one that
    `pendingRowO` returned. KIND K13's BLOCKS: `rowOf_weights`, `batt_weights`, `weights_atM3`,
    `weights_oneRowB`, `weights_rowsB`: they stand in the thin file
    Johnson/Desc/K13/Law/WeightsKept.lean, which this file imports. (Any step that leaves `S.rows`
    keeps it: `First.weightsB_same`.)

Every "there is": none.
Limits. (1) NOT SHOWN: that every OTHER block of the first chain leaves `S.rows`; that the seated
description's door-quiet step lays its row by `pendingKept` and `pendingRowO`; that W's commitment
(another kind's block, in front of `rowsB` inside `atM4`) leaves the rows. So nothing rides yet:
whoever fills the first chain's promise has to lay `weightsB` into it and keep it row by row. (That
it holds at a first record lies typed: `First.weightsB_start`, `fillWeights_start`.)
`weights_pendingKept` speaks of a pile under "for all", not of `weightsB` on a record, and the step
that calls `pendingKept` walks another record type: that join is not typed. (2) Past K13's two steps
as its files state them: `K13.Law.weightsKeeps` (Johnson/Desc/K13/Law/RidersWeights.lean). (3) NO
MEMBER. Nothing on what the weights' entries are. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.ShapeDoorLess
import Johnson.Desc.K13.Law.WeightsKept
import Johnson.Desc.First.Walk.Quiet

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third
open VerifiableInference.Desc.First (weightsB)

/-- **The third of the tests on the first chain's end, from the test that rides**: where
`firstOfS` hands something there is just one pending row (the claim's), so the clause asks its
weights alone. -/
theorem weightsClause_of {s : First.S} {f : FirstEnd₃} (hf : firstOfS s = some f)
    (hw : weightsB s = true) :
    (match f.pending with
      | [r] => r.g.all (·.ok)
      | _ => false) = true := by
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 hf
  show (match s.rows with
      | [r] => r.g.all (·.ok)
      | _ => false) = true
  unfold weightsB at hw
  unfold First.S.firstEnd? at he
  split at he
  · rename_i a ha
    cases hl : a.lin with
    | none =>
      rw [hl] at he
      cases he
    | some l =>
      have e : s.rows = [First.rowOfClaim l.claim] := by
        unfold First.S.rows
        rw [ha]
        show (match a.lin with
          | some l => [First.rowOfClaim l.claim]
          | none => s.out.pending) = _
        rw [hl]
      rw [e] at hw ⊢
      simpa using hw
  · cases he

/-- **The pile's one writer keeps it**: `pendingKept` (Johnson/Desc/First/Walk/Quiet.lean) lays a
row at the pile's end; where that row is one that `pendingRowO` has returned, the longer pile passes
if the pile did. -/
theorem weights_pendingKept {lay : Model.WsLay} {indexMasks : ℕ} {o : Model.WsForkOut} {claims : ℕ}
    {S : Params.LinShape} {oracles oracles' : Array OnBytes.Oracle} {row : TensorRow}
    (h : First.Pend.pendingRowO lay indexMasks o claims S oracles = .ok (row, oracles'))
    (out : Proof.LinksResult) (hp : ∀ r ∈ out.pending, ∀ t ∈ r.g, t.ok = true) :
    ∀ r ∈ (Johnson.Desc.First.Walk.pendingKept out row).pending, ∀ t ∈ r.g, t.ok = true := by
  intro r hr
  have hr' : r ∈ out.pending ++ [row] := hr
  rcases List.mem_append.1 hr' with c | c
  · exact hp r c
  · obtain rfl := List.mem_singleton.1 c
    exact First.Pend.pending_rows_weights_ok h

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.weights_pendingKept
#print axioms VerifiableInference.Desc.Last.weightsClause_of
