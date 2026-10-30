-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/AtHead2.lean: the code switch's law at the closed constant: UNDER
THE WIDER HEAD THE TYPED TABLE's MAKER RETURNS.
  table_returns_head   ∃ t, tableOf Z.pol Z.lay Z.KL = .ok t, from AtMgA: its field opts
                       holds the test spotsB (Johnson/P5J/OptsOk.lean), whose text matches on the
                       maker's value and rejects where there is none; the public part bears the
                       files' own bytes (pub_files)
ON AtMgA (its field opts), NOT ON AtMg. At every letter o for the second hash function; no pin.
WHAT IT IS FOR. table_in_scope (Johnson/LPFE1R/TableClosed.lean): in scope,
under the pin, wherever the maker returns it returns the written table: with this: «the made table
is the written one»: AtHead3.lean's tableWritten_head. LIMITS. spotsB is a named test among the
wider head's fields; its own text runs the maker; no entry test asks it; by
reading it hangs on «the rows' maker returns» (P5J.rowsRead Z), which is not paid. SO «IT RETURNS»
IS READ OFF THE HEAD: MOVED, NOT SPARED. A member of the head is proved at storedPublicFiles and zGap alone (at
secondHashFunction; side library AtFullSide/Top/). No soundness is claimed.
-/
import Johnson.P5J.MgAtAll
import Johnson.Desc.ProofFile.Law.CarryAtLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K2Ties
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.K2Caller (SwRow tableOf)
open OnBytes.Maker (WholeD)
open P5J (AtMg AtMgA TS)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under the wider head the typed table's maker returns**: the head's field opts holds the test
spotsB, which rejects where it does not. -/
theorem table_returns_head (h : AtMgA o Z D r₀ Zp Np cF x) :
    ∃ t, tableOf Z.pol Z.lay Z.KL = .ok t := by
  obtain ⟨e1, e2⟩ := ProofFile.Law.pub_files h.laid.pub
  have hs := h.opts.spots
  unfold P5J.At.spotsB at hs
  rw [e1, e2] at hs
  cases ht : tableOf Z.pol Z.lay Z.KL with
  | ok t => exact ⟨t, rfl⟩
  | error e =>
    rw [ht] at hs
    cases hs

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.table_returns_head
