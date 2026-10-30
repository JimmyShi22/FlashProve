-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadTabRows.lean.
WHAT IT DOES NOT SHOW. No soundness. Numbers of entries alone: nothing on what an entry is worth.
TWO PREMISES ON OTHER TEXTS STAY, each by name: hK: the plan's number of reads is at most the width
of the reads' array in the record's ledger (the planner lays that array with one row and just that
width: not shown here; that the record's ledger keeps it: not shown here) · e: the tables in the
record are what the reads' quiet step's own function returns.
LETTERS. reads_row0: tt, tr, o, F: the caller's, each read by an equation that pins it (ho, hF, ht,
htr); h', L, hp, cov, x: e alone reads them: they are whatever the quiet step was called at.
OBJECT. Desc/K8/ReadsQuiet.lean's tables (what the description's text lays into the record as the
table of tables); Stored/HeadSeatAt.lean's seatAt h iU3, its field reads.
USER. Whoever must know that a form of the output head names a cell of ROW 0 of the reads' array:
the row at which the batching's weights are laid.
WHAT IT IS. EVERY ROW OF THE TABLE OF TABLES (name; first entry; length) ENDS AT OR BELOW THE LENGTH
OF THE VECTOR OF READS; SO EVERY ENTRY THAT THE SEAT's READS NAME LIES IN ROW 0.
  tables_tab_below  after a yes of the quiet step's function: every row of t.tab ends at or below
                    t.p, and t.p is the plan's number of reads: the first from the record
                    WfT's clause "ends" (Johnson/Road/HeadReads.lean), which Law/TabsApart.lean's
                    tables_apart has at these tables. (Law/HeadTabsBelow.lean has the like for the
                    list t.funs.)
  entryAt_row0      below the width, the form at a position is the entry of row 0 at that column.
  reads_row0        where the seat's reads answer: below a read's length every one of the twelve
                    reads' entries is the entry of row 0 at column firstOf tt name + i, and that
                    column is below the width.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.TabsApart
import Johnson.Desc.Kinds.Law.ReadsAre

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model Fo
open VerifiableInference.Desc.K8
open VerifiableInference.Desc.First (S)

/-- **After a yes of the head's tables.** -/
theorem tables_tab_below {h : Model.Head.Shape} {L : Model.Head.HL} {hp : Model.Head.HPlanH2}
    {cov : Model.Head.Covered} {x : Model.Head.Heard} {t : Model.Head.Tables}
    (e : ReadsQuiet.tables h L hp cov x = .ok t) :
    (∀ r ∈ t.tab, r.2.1 + r.2.2 ≤ t.p) ∧ t.p = hp.nU.getD 2 0 :=
  ⟨fun r hr => ((tables_apart e).1.ends r hr).2, (tables_below e).2⟩

/-- Below the width the form at a position is the entry of row 0 at that column. -/
theorem entryAt_row0 (iU3 K pos : Nat) (h : pos < K) : entryAt iU3 K pos = Aff.ent iU3 0 pos := by
  unfold entryAt
  rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]

/-- **WHERE THE SEAT's READS ANSWER, EVERY ENTRY BELOW A READ's LENGTH LIES IN ROW 0.** -/
theorem reads_row0 (h : Model.Head.Shape) (iU3 : Nat) (s : S) (y : FinalNorm.Reads × Reads)
    (hy : (seatAt h iU3).reads s = some y) {o : VerifiableInference.Desc.First.HeadOwn} {F : Fork}
    {tt : Model.Head.Tables} {tr : HTree} (ho : s.here = .head o) (hF : s.fork? = some F)
    (ht : o.t = some tt) (htr : F.trees[iU3]? = some tr) {h' : Model.Head.Shape}
    {L : Model.Head.HL} {hp : Model.Head.HPlanH2} {cov : Model.Head.Covered}
    {x : Model.Head.Heard} (e : ReadsQuiet.tables h' L hp cov x = .ok tt)
    (hK : hp.nU.getD 2 0 ≤ tr.K) :
    (∀ r i, i < @readLenN (sizesOf h) r → firstOf tt (nameOfN r) + i < tr.K ∧
      y.1.entry r i = Aff.ent iU3 0 (firstOf tt (nameOfN r) + i)) ∧
    (∀ r i, i < @readLen (sizesOf h) r → firstOf tt (nameOf r) + i < tr.K ∧
      y.2.entry r i = Aff.ent iU3 0 (firstOf tt (nameOf r) + i)) := by
  obtain ⟨o', F', tt', tr', ho', hF', ht', htr', _, a1, _, a3⟩ := reads_are h iU3 s y hy
  obtain rfl : o = o' := by
    rw [ho] at ho'
    injection ho'
  obtain rfl : F = F' := Option.some.inj (hF.symm.trans hF')
  obtain rfl : tt = tt' := Option.some.inj (ht.symm.trans ht')
  obtain rfl : tr = tr' := Option.some.inj (htr.symm.trans htr')
  obtain ⟨w1, w2⟩ := reads_within h iU3 s y hy tt o ho ht
  obtain ⟨Z, hp'⟩ := tables_tab_below e
  constructor
  · intro r i hi
    obtain ⟨row, hf, h1, h2⟩ := w1 r
    have hz := Z row (List.mem_of_find?_eq_some hf)
    have hlt : firstOf tt (nameOfN r) + i < tr.K := by
      rw [h1]
      omega
    exact ⟨hlt, by rw [a1, entryAt_row0 _ _ _ hlt]⟩
  · intro r i hi
    obtain ⟨row, hf, h1, h2⟩ := w2 r
    have hz := Z row (List.mem_of_find?_eq_some hf)
    have hlt : firstOf tt (nameOf r) + i < tr.K := by
      rw [h1]
      omega
    exact ⟨hlt, by rw [a3, entryAt_row0 _ _ _ hlt]⟩

end VerifiableInference.Desc.Kinds.Head.Law
