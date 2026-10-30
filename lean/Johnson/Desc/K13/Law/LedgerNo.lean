-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/LedgerNo.lean: WHICH NUMBER THE LEDGER GIVES: at the ledger of k takes
(`LedgerAt`, Johnson/Desc/K13/Law/LedgerWithin.lean) the entry that is taken next has the number
`takenNo m k` (OnBytes/Iop/LedgerPlaces.lean), m the message's mask rows: the k-th number that the
search gives. Three theorems.
  `nextOf_no`       at the number that a ledger gives next (`nextOf`).
  `takeEntry_no`    at the pending row's take (`takeEntry`, Johnson/Desc/First/Pend/Row.lean).
  `takeEntry_free`  so it is the number of the k-th free entry by the format's page: row k % m,
                    place k / m (`takenNo_eq`, CALLED).
What is not claimed. That a record's ledger has `LedgerAt` at any k. Nothing on soundness.

-/
import Johnson.Desc.K13.Law.LedgerWithin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes
open Fmt.Places (entryNo freeAt)
open VerifiableInference.Desc.First.Pend (takeEntry)

/-- The number that the ledger of k takes gives next. -/
theorem nextOf_no {st : Statement} {o k : ℕ} {x : Oracle} {l : Ledger} (h : LedgerAt st o k)
    (hx : st.oracles[o]? = some x) (hl : x.ledger = some l) :
    nextOf l = takenNo x.shape.maskRows k := by
  obtain ⟨x₀, l₀, hx₀, hl₀, _, _, hr, hq, _, hnext⟩ := h
  obtain rfl := Option.some.inj (hx₀.symm.trans hx)
  obtain rfl := Option.some.inj (hl₀.symm.trans hl)
  unfold nextOf
  rw [hr, hq, hnext]
  exact takenNo_at x₀.shape.maskRows k

/-- **The entry that is taken has the k-th number given.** -/
theorem takeEntry_no {st : Statement} {o k c : ℕ} {x : Oracle} {l l' : Ledger}
    (h : LedgerAt st o k) (hx : st.oracles[o]? = some x) (hl : x.ledger = some l)
    (ht : takeEntry l = some (c, l')) : c = takenNo x.shape.maskRows k := by
  rw [(takeEntry_is ht).2.1]
  exact nextOf_no h hx hl

/-- So it is the number of the k-th free entry. -/
theorem takeEntry_free {st : Statement} {o k c : ℕ} {x : Oracle} {l l' : Ledger}
    (h : LedgerAt st o k) (hx : st.oracles[o]? = some x) (hl : x.ledger = some l)
    (ht : takeEntry l = some (c, l')) :
    c = entryNo x.shape.maskRows (freeAt x.shape.maskRows k).1 (freeAt x.shape.maskRows k).2 := by
  have hm : 0 < x.shape.maskRows := by
    obtain ⟨x₀, _, hx₀, _, hm, _⟩ := h
    obtain rfl := Option.some.inj (hx₀.symm.trans hx)
    exact hm
  rw [takeEntry_no h hx hl ht, takenNo_eq hm k]

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.nextOf_no
#print axioms VerifiableInference.Desc.K13.Law.takeEntry_no
#print axioms VerifiableInference.Desc.K13.Law.takeEntry_free
