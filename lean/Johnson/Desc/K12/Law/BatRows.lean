-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/BatRows.lean: the batching of a proximity test asks that its round's entry
count the batched rows. A statement and its proof.

`bat_ok` (Johnson/Desc/K12/Law/BatMeans.lean) unfolds the batching's plain text and drops its guard
"K10.rows"; this file keeps it. A count `lstJ e * (rows - 1)` with `rows := (runRows S G).size` is a
number of the record; with `bat_rows` it is the plan's: the entry's own number.
Main names:
  `bat_rows`: the batching's plain text returns, and the group `G` stands under `g`: then `e.rows =
    (runRows S G).size`.
Limits: It says nothing where the batching refuses. No soundness is claimed, and nothing is said on
hiding.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the
file's end.

-/
import Johnson.Desc.K12.Law.BatMeans

set_option autoImplicit false
namespace H2K.ClaimSays
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc
open H2K.FoldLaw (bind_ok)

theorem bat_rows (S S' : Statement) (g : Nat) (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow)
    (L : GroupLayout) (h : First.Close.bat S g e r = .ok (row, L, S')) (G : Group)
    (hG : S.groups[g]? = some G) : e.rows = (runRows S G).size := by
  unfold First.Close.bat at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨⟨input, d⟩, hb, h⟩ := bind_ok h
  obtain ⟨x, _, h⟩ := bind_ok h
  obtain ⟨_, hr, h⟩ := bind_ok h
  obtain ⟨G', lay, a1, _, rfl, rfl⟩ := H2K.Sw.beginRunP_ok (H2K.FoldLaw.got_ok hb)
  obtain rfl : G' = G := Option.some.inj (a1.symm.trans hG)
  exact beq_iff_eq.1 (H2K.FoldLaw.need_ok hr)

end H2K.ClaimSays

#print axioms H2K.ClaimSays.bat_rows
