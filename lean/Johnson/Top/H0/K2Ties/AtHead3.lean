-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Top/H0/K2Ties/AtHead3.lean: the code switch's law at the closed constant
(P5J.mgAtAll): TWO MORE OF K2's NAMED TESTS, FROM THE WIDER HEAD (WITH THE FOURTEEN ENTRY TESTS):
tableWrittenB («the made table is the written one») AND membersPlanB WITH NOTHING ELSE IN FRONT.

  tableWritten_head    tableOf Z.pol Z.lay Z.KL = .ok tableFullLit: AtHead2.lean's
                       table_returns_head (the maker returns: the head's field opts) with
                       table_in_scope (Johnson/LPFE1R/TableClosed.lean: in scope,
                       under the pin, wherever it returns it returns the written table) and
                       AtHead.lean's pin_head
  swRows_self · swRows_rejects  the comparison of tables accepts the written table against itself
                       and rejects it without its first row: by decide +kernel
  tableWrittenB_head   the named test tableWrittenB accepts
                       (Johnson/Top/H0/K2Caller/TableWritten.lean)
  rowsFirst_view       the written rows of the first chain have the written labels and numbers of
                       entries: by decide +kernel
  membersPlan_ofHead   membersPlanB accepts at all 25 switches: RadiiOfTable.lean's
                       radii_of_rows, its premise on the rows' labels now from TableClosed.lean's
                       first_rows_written, which asks no «live»: so membersPlanB asks protocolDataWellFormed no
                       more. (protocolDataWellFormed itself is not shown here, and stays in front elsewhere on the
                       road to K2's condition.)
ON AtMgA (its field opts), at the concrete second hash function.
WHAT «FROM THE HEAD (WITH THE FOURTEEN ENTRY TESTS)» MEANS. The head's field «laid» holds, in its
part «asks», that every entry test of the proof file accepts (LPFD.lawsAsk,
Johnson/Desc/Laid/ProofAsks.lean: fourteen rows, of which rows 9 and 10 are the two pins). The
verifier asks these fourteen. P5J.pins_of_laid
(Johnson/Goal/Skeleton/PinsOfLaid.lean) reads the two pins off that field. That a value is laid
under fourteen rows is proved at storedPublicFiles and zGap alone (a field of the head's member: at secondHashFunction, with
fixedConfigurationDigest in the digest's place; side library AtFullSide/Top/). A verifier whose entry tests lack these
two rows gives no such head. THE RIDER. tableWrittenB says two things: «the table's maker returns»
and «its value is the written table». THE SECOND IS A THEOREM (scope · laid · the pin). THE FIRST IS
READ OFF THE WIDER HEAD's FIELD opts (the named test spotsB, Johnson/P5J/OptsOk.lean), whose own
text runs the maker; no entry test asks it; by reading it hangs on «the rows'
maker returns» (P5J.rowsRead Z), which is not paid. SO FOR THAT HALF THE TEST IS MOVED INTO THE
HEAD, NOT SPARED.
LIMITS. The full size alone. A member of the head is proved at storedPublicFiles and zGap alone (at secondHashFunction; side
library AtFullSide/Top/). No soundness is claimed.

-/
import Johnson.Top.H0.K2Ties.AtHead
import Johnson.Top.H0.K2Ties.AtHead2
import Johnson.LPFE1R.TableClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K2Ties
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.LinkJoin (table_in_scope first_rows_written rowsFirstW)
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit tableOf tableOf_iff tableWrittenB
  swRowsB membersPlanB)
open OnBytes.Maker (WholeD)
open P5T (firstRows radOf)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE MADE TABLE IS THE WRITTEN ONE**, from the wider head (with the fourteen entry tests). -/
theorem tableWritten_head (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) :
    tableOf Z.pol Z.lay Z.KL = .ok tableFullLit := by
  obtain ⟨t, ht⟩ := table_returns_head h
  rw [ht, table_in_scope h.scope h.laid.pub (pin_head h.toAtMg) ht]

set_option maxRecDepth 1000000 in
theorem swRows_self : swRowsB tableFullLit tableFullLit = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: the comparison of tables rejects the written table without its first
row. -/
theorem swRows_rejects : swRowsB tableFullLit.tail tableFullLit = false := by decide +kernel

/-- **The named test tableWrittenB accepts.** -/
theorem tableWrittenB_head (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) :
    tableWrittenB Z.pol Z.lay Z.KL = true := by
  unfold tableWrittenB
  rw [tableWritten_head h]
  exact swRows_self

set_option maxRecDepth 1000000 in
/-- The written rows of the first chain have the written labels and numbers of entries. -/
theorem rowsFirst_view : rowsFirstW.map (fun y => (y.label, y.sampled.length)) = Wc := by
  decide +kernel

/-- **THE NAMED TEST membersPlanB ACCEPTS AT ALL 25 SWITCHES**, from the wider head
(with the fourteen entry tests): neither «live» nor «the made table is the written one» is asked. -/
theorem membersPlan_ofHead (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) {m : ℕ} (hm : m < 25)
    {r : SwRow} (hr : tableFullLit[m]? = some r) :
    membersPlanB Zp (P5J.At.rad Zp Z.lay) (P5J.At.N Zp cF) (m + 1) r = true := by
  obtain ⟨p, R, -, hR, e⟩ := tableOf_iff.1 (tableWritten_head h)
  obtain ⟨hlo, hl'⟩ := made_row _ _ R m r (by rw [← e]; exact hr)
  have hW : (firstRows R).map (fun y => (y.label, y.sampled.length)) = Wc := by
    rw [first_rows_written h.scope h.laid.pub (pin_head h.toAtMg) hR]
    exact rowsFirst_view
  have hrad : P5J.At.rad Zp Z.lay = radOf R := by
    obtain ⟨e1, e2⟩ := ProofFile.Law.pub_files h.laid.pub
    unfold P5J.At.rad P5T.rowsAt?
    rw [e1, e2, hR]
    rfl
  refine membersPlan_at (atWritten_head h.toAtMg) (sends_head h.toAtMg) hm hr _ ?_
  rw [hrad]
  exact radii_of_rows hW hlo hl' hm hr

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.tableWritten_head
#print axioms VerifiableInference.Desc.First.K2Ties.swRows_self
#print axioms VerifiableInference.Desc.First.K2Ties.swRows_rejects
#print axioms VerifiableInference.Desc.First.K2Ties.tableWrittenB_head
#print axioms VerifiableInference.Desc.First.K2Ties.rowsFirst_view
#print axioms VerifiableInference.Desc.First.K2Ties.membersPlan_ofHead
