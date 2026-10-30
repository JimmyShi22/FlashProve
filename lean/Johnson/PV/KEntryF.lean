-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/KEntryF.lean: THE FULL SIZE: Johnson/PV/KLeastF.lean's law
  speaks of the entry's rounds as the library's description has them (OnBytes.Slice.frD.ds); a run
  lays PV.EntryFive.dsF: another text, another type of round.
  **dsF_rounds**: round by round the two have ONE entry and ONE kind (by evaluation in Lean's
    kernel: decide +kernel; closed terms) · **KF_entry_run**: so K serves every round of
    PV.EntryFive.dsF too.


-/
import Johnson.PV.KLeastF

set_option autoImplicit false
set_option maxRecDepth 100000

namespace W4N
open OnBytes.Flat OnBytes.Slice OnBytes.Maker _root_.Run

theorem dsF_rounds : (PV.EntryFive.dsF.map fun d => (d.entry, d.kind)) = (OnBytes.Slice.frD.ds.map
    fun d => (d.entry, d.kind)) := by
  decide +kernel

theorem KF_entry_run (DK DP : WholeD) : ∀ d ∈ PV.EntryFive.dsF, (bsRound .two d.entry d.kind).b ≤
    LPFD.Full.KF DK DP := by
  intro d hd
  have h : (d.entry, d.kind) ∈ PV.EntryFive.dsF.map fun d => (d.entry, d.kind) := List.mem_map.2 ⟨d,
      hd, rfl⟩
  rw [dsF_rounds] at h
  obtain ⟨d', hd', e⟩ := List.mem_map.1 h
  have k := (KF_serves DK DP).entry d' hd'
  have e1 : d'.entry = d.entry := congrArg Prod.fst e
  have e2 : d'.kind = d.kind := congrArg Prod.snd e
  rw [e1, e2] at k
  exact k

end W4N

#print axioms W4N.dsF_rounds
#print axioms W4N.KF_entry_run
