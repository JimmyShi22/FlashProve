-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/NzLaw.lean: nzOk p = true gives its clauses as a proposition; with it roundsFit
holds at the written rounds of the place.

Statements and proofs, over Johnson/Desc/K12/Law/NzOk.lean and Johnson/Desc/K12/Law/FitWritten.lean.
Main names:
  `nz_of_ok`: every declared round of the place has drawNZ ≤ drawE.
  `fit_of_ok`: roundsFit (Johnson/Desc/Block.lean: seven clauses a round) at r0 followed by the
    written rounds behind "BAT", from nzOk, the declared and the written rounds off the place's
    numbers, and "r0 fits the declared round "BAT"".
Limits: No soundness is claimed, and nothing is said on hiding.
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.K12.Law.NzOk
import Johnson.Desc.K12.Law.FitWritten

set_option autoImplicit false
namespace H2K.Fit
open Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.First (nzOk nzOn ok)
open H2K.Pub (WR writtenOf)

theorem nz_of_ok (p : P12) (ds : List Fmt.DeclaredRound) (hd : H2U.roundsOfNums p.nums = some ds)
    (h : nzOk p = true) : ∀ d ∈ ds, d.entry.drawNZ ≤ d.entry.drawE := by
  unfold nzOk at h
  rw [hd, Option.any_some] at h
  unfold ok nzOn at h
  rw [List.all_map, List.all_eq_true] at h
  intro d hdm
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hdm
  have := h (d, i) (by
    rw [List.mem_zipIdx_iff_getElem?]
    simpa using hi)
  exact of_decide_eq_true this

theorem fit_of_ok (p : P12) (d0 : Fmt.DeclaredRound) (ds : List Fmt.DeclaredRound) (w0 : WR) (ws : List WR)
    (hd : H2U.roundsOfNums p.nums = some (d0 :: ds)) (hw : writtenOf p.nums = some (w0 :: ws))
    (hz : nzOk p = true) (r0 : Fmt.RoundView) (h0 : roundsFit [d0] [r0] = true)
    (τ : Iop.Tr (PQ.uL (ckP .two) (ws.map WR.rd))) :
    roundsFit (d0 :: ds) (r0 :: PQ.rvSL (ckP .two) (ws.map WR.rd) τ) = true :=
  roundsFit_behind p.nums d0 ds w0 ws hd hw
    (fun d h => nz_of_ok p _ hd hz d (List.mem_cons_of_mem _ h)) r0 h0 τ

end H2K.Fit
