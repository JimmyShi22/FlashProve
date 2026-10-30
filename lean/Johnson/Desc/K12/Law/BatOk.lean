-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/BatOk.lean: what a yes of the plain text of the batching in front of a
proximity test (the kind K12) holds.

One statement with its proof. It stands in a file of its own, over
Johnson/Desc/K12/Law/SwUnfold.lean and Johnson/Desc/K12/Law/FoldLaw.lean alone, so that a file which
wants it need not import the files on words beneath Johnson/Desc/K12/Law/BatMeans.lean.
Main names:
  `bat_ok`: a yes of `First.Close.bat S g e r` with the row, the layout L and the statement S' gives
    the group G in front and an element x with: `S.groups[g]? = some G`, `S.layout g = some L` (the
    layout in front), `S' = begun S g G`, the round draws just the one element x, and `Bat.combine`
    at the statement behind, at the layout in front and `runRows S G`, gives the row.
Limits: Code against a record, by unfolding: no field, no probability, no hash. Nothing on what the
row means (Johnson/Desc/K12/Law/BatMeans.lean). Nothing on soundness. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.SwUnfold
import Johnson.Desc.K12.Law.FoldLaw

set_option autoImplicit false
namespace H2K.ClaimSays
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc
open H2K.FoldLaw (bind_ok)

/-- What a yes of the batching's plain text `First.Close.bat` holds. -/
theorem bat_ok (S S' : Statement) (g : Nat) (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow)
    (L : GroupLayout) (h : First.Close.bat S g e r = .ok (row, L, S')) :
    ∃ (G : Group) (x : E), S.groups[g]? = some G ∧ S.layout g = some L ∧ S' = begun S g G ∧
      r.drawn.elems.map E.ofTriple = [x] ∧ Bat.combine S' g ⟨L, runRows S G⟩ x = some row := by
  unfold First.Close.bat at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨⟨input, d⟩, hb, h⟩ := bind_ok h
  obtain ⟨x, hx, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨row', hc, h⟩ := bind_ok h
  cases h
  obtain ⟨G, lay, a1, a2, rfl, rfl⟩ := H2K.Sw.beginRunP_ok (H2K.FoldLaw.got_ok hb)
  cases hh : First.Close.heard "BAT" 0 e r with
  | error w => rw [hh] at hx; cases hx
  | ok v =>
    rw [hh] at hx
    cases hx
    obtain ⟨_, t, ht, hv⟩ := H2K.FoldLaw.heard_ok _ _ _ _ _ v.1 v.2 hh
    exact ⟨G, v.2, a1, a2, rfl, by rw [ht, hv]; rfl, H2K.FoldLaw.got_ok hc⟩

end H2K.ClaimSays
