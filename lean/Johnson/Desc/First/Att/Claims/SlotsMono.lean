-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/SlotsMono.lean: kind K5: the two records of Claims/SlotsIn.lean are monotone
in the predicate on slots: what holds at Ps holds at every Qs that Ps implies.

Main names: ptsSlots_mono · rowsSlots_mono.
For what: from "filled in the ledger behind the hearing" to "filled in a later ledger"
(OnBytes/Tie/Pv/Psc/PscLater.lean: Later.keep).
IS IT EMPTY HERE? Implications from a record to a record; neither is shown of anything here.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.SlotsIn

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att

variable {Ps Qs : ℕ → Prop} {g : P.Geo} {p : P.Pts}

theorem ptsSlots_mono (m : ∀ j, Ps j → Qs j) (h : PtsSlots Ps g p) : PtsSlots Qs g p where
  planes pc hpc := ⟨(h.planes pc hpc).1, fun i hi => m _ ((h.planes pc hpc).2 i hi)⟩
  scores k hk := ⟨fun i hi => m _ ((h.scores k hk).1 i hi), fun i hi => m _ ((h.scores k hk).2 i hi)⟩
  five i hi := m _ (h.five i hi)
  bits i hi := m _ (h.bits i hi)
  two i hi := m _ (h.two i hi)
  values i hi := m _ (h.values i hi)
  maxima i hi := m _ (h.maxima i hi)
  scE i hi := m _ (h.scE i hi)
  vpm i hi := m _ (h.vpm i hi)
  vpd i hi := m _ (h.vpd i hi)
  scF i hi := m _ (h.scF i hi)
  scd i hi := m _ (h.scd i hi)
  scH i hi := m _ (h.scH i hi)

theorem rowsSlots_mono (m : ∀ j, Ps j → Qs j) (h : RowsSlots Ps p) : RowsSlots Qs p where
  units k hk := slotsIn_mono m (h.units k hk)
  scE := slotsIn_mono m h.scE
  vpm := slotsIn_mono m h.vpm
  vpd := slotsIn_mono m h.vpd
  scF := slotsIn_mono m h.scF
  scd := slotsIn_mono m h.scd
  scH := slotsIn_mono m h.scH

end K5Law

#print axioms K5Law.ptsSlots_mono
#print axioms K5Law.rowsSlots_mono
