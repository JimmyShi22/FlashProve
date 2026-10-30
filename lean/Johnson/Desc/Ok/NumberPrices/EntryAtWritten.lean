-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ok/NumberPrices/EntryAtWritten.lean: the entry file's part of the row number_prices
with the plan as data, as a closed statement. Every round of the entry file's written data at the
full size (`frD.ds`, OnBytes/Slice/FullRecSz.lean: 41 rounds) has, at its place, a round of the
entry file's written priced plan (`pricedEntryFull`, Johnson/G/PricedEntryLit.lean) with the four
clauses of `PricedAt` (Johnson/Desc/Ok/NumberPrices/AtData.lean), and the plan passes the public
test on a chain's plan (`Desc.chainAll 32`, Johnson/Desc/MadeOk.lean).

The key file's part is Johnson/Desc/Ok/NumberPrices/KeyAtWritten.lean. An entry file has one chain,
and its rounds' data are of another type than a key file's: a round with at most one tree
(`Run.PQ.RD`), where a key file's round has a list of trees and its stored tables (`RDT`).
`PricedAt` is typed on the second. Its four clauses read the round's entry, its kind and its
verifier messages alone, and `toRD` (OnBytes/Flat/RoundsT.lean) keeps all three. So the clauses are
stated here on the first type (`PricedRD`), and `pricedAt_iff` says that this is the same notion:
the entry file has no weaker clause.

`EntryPricesWritten` is a closed fact on two written values: it names no letter, no
public file, no planner and no description of the protocol. It becomes the row's clause for the
entry file where a description's data are shown to be these. All else here are tools, or facts on
the two written values.

Definitions.
  `PricedRD d r`: the four clauses of `PricedAt`, of a round's data d with at most one tree.
  `liftRD d`: d as a round with a list of trees, and no stored table: a tool for the proofs.
  `EntryPricedAt P`: `PricedRD` place by place, of `frD.ds` against the rounds of the chain in P
    (`chainRounds`: the entry under the name "RECORD" is none).
  `entryLitOk P`: the test, with code: `Desc.chainAll 32 P`, and the entries of `frD.ds` are those
    of P's rounds of the chain, one by one (`Aligned`, OnBytes/Flat/HeldAll.lean).
  `EntryPricesWritten`: `EntryPricedAt pricedEntryFull`, and `Desc.chainAll 32 pricedEntryFull` =
    true. The two belong together: `PricedRD` says that error / 2 ^ work is within 2 ^ -128; that no
    round counts more than 32 bits of work, and that work is counted at rounds that draw positions
    alone, is in `Desc.chainAll`.
Statements.
  `pricedAt_iff`: `PricedAt d r` ↔ `PricedRD (toRD d) r`. `toRD_lift`: `toRD (liftRD d)` = d.
  `pricedRD_aligned`: against a plan that passes `Desc.chainOk`, data whose entries are the plan's
    have `PricedRD` place by place. By `pricedAt_aligned`.
  `entryPriced_of_test`: a yes of `entryLitOk` gives `EntryPricedAt P`, at every P.
  `entry_lit_ok`: the test says yes at `pricedEntryFull`. `entryPricesWritten : EntryPricesWritten`.
  `entry_lengths`: 41 rounds of data against 41 priced rounds; the plan has 42. `entry_record`: the
    one more is the plan's first, the entry "RECORD".
  `entry_no_lin`: no entry of the plan has the name "LIN point".
  `dsFull_lib`: the written data as the compiled slot takes them (`dsFull`,
    OnBytes/Flat/LinkSibAt.lean) are `frD.ds`, carried round by round (`PQ.ofLib`).
By evaluations in Lean's kernel (`decide +kernel`): `entry_lit_ok`, `entry_lengths`, `entry_record`,
`entry_no_lin`. All else is by proof.

What holds an error here: from above the test; from below nobody yet. `PricedRD d r` serves a
caller only where it can show that its own count of bad values is at most `r.error` times the
number of values.

What of OnBytes/Model/ is used: nothing by name.

Limits. 42 in the plan, 41 in the clause: the entry "RECORD" (the stored table's own sample) is
tested by `Desc.chainAll` and has no `PricedRD`, as at the key file's first chain. That the written
priced plan is the planner's at the written lines is shown elsewhere, not here. `why`, `group`,
`rests`, `scope` and `wordFault` are the written records' own words, held against nothing in Lean.
That a description's data are `frD.ds` or `dsFull` is not said here. No count is bounded. No factor
for the slots of a batch is laid, and by the format's page none is due:
docs/format/FORMAT.md, section 18, condition 10, has that factor at a proof's round "LIN point"
(cited on another reader's word; the page was not at hand). Nothing on the small example. The limits
of Johnson/Desc/Ok/NumberPrices/AtData.lean hold here. Nothing on soundness.


-/
import Johnson.G.PricedEntryLit
import Johnson.Desc.Ok.NumberPrices.AtData
import OnBytes.Flat.LinkSibAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Number.ByRuns
open VerifiableInference VerifiableInference.Number
open _root_.Iop Prob _root_.Run OnBytes.Params OnBytes.Slice OnBytes.Flat OnBytes.Flat.Held
open OnBytes.Maker Johnson.G
open scoped ENNReal

/-! ## One notion, at two types -/

/-- The four clauses of `PricedAt`, of a round's data with at most one tree. -/
structure PricedRD (d : PQ.RD) (r : PlanRound) : Prop where
  entry : d.entry = r.entry
  share : kapSl 128 ^ exAll (Fmt.dsOf d.entry d.kind) *
    (ENNReal.ofReal (r.error.val : ℝ) / 2 ^ d.entry.work) ≤ ((2 : ℝ≥0∞)⁻¹ ^ 128)
  held : ∀ e : ℕ, (e : ℚ) ≤ r.error.val * (nVals (Fmt.dsOf d.entry d.kind) : ℚ) →
    ∃ c : ℝ≥0∞, (e : ℝ≥0∞) ≤ c * (Nat.card (Vals .two (Fmt.dsOf d.entry d.kind)) : ℝ≥0∞) ∧
      kapSl 128 ^ exAll (Fmt.dsOf d.entry d.kind) * (c / 2 ^ d.entry.work) ≤ ((2 : ℝ≥0∞)⁻¹ ^ 128)
  count : ∀ e : ℕ, (e : ℚ) ≤ r.error.val * (nVals (Fmt.dsOf d.entry d.kind) : ℚ) →
    ((e * (bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞) ≤
      ((2 : ℝ≥0∞)⁻¹ ^ 128) * (Fintype.card (wRound d).Chal : ℝ≥0∞)

/-- **It is the same notion**: `PricedAt` of a round with a list of trees is `PricedRD` of that
round with at most one. -/
theorem pricedAt_iff (d : RDT) (r : PlanRound) : PricedAt d r ↔ PricedRD (toRD d) r :=
  ⟨fun h => ⟨h.entry, h.share, h.held, h.count⟩, fun h => ⟨h.entry, h.share, h.held, h.count⟩⟩

/-- A round's data with at most one tree, as a round with a list of trees and no stored table. -/
def liftRD (d : PQ.RD) : RDT := ⟨TypedOracleCompiler.Run.PQ.ofLib d, []⟩

/-- `toRD` brings it back. -/
theorem toRD_lift (d : PQ.RD) : toRD (liftRD d) = d := by
  obtain ⟨e, k, it, t, o⟩ := d
  cases t <;> rfl

/-- Against the plan's rounds of the chain. -/
theorem pricedRD_aligned {w : ℕ} {P : Planned} (h : Desc.chainOk w P = true) (ds : List PQ.RD)
    (ha : Aligned ds P) : List.Forall₂ PricedRD ds (chainRounds P) := by
  have e : (ds.map liftRD).map toRD = ds := by
    rw [List.map_map]
    exact (List.map_congr_left fun d _ => toRD_lift d).trans (List.map_id ds)
  have H := pricedAt_aligned h (ds.map liftRD) (by rw [e]; exact ha)
  rw [List.forall₂_map_left_iff] at H
  refine H.imp fun d r Hd => ?_
  have k := (pricedAt_iff (liftRD d) r).1 Hd
  rw [toRD_lift] at k
  exact k

/-! ## The entry file's written data against a priced plan -/

/-- Every round of the entry file's written data has a priced round at its place. -/
def EntryPricedAt (P : Planned) : Prop := List.Forall₂ PricedRD frD.ds (chainRounds P)

/-- **The test on an entry file's written priced plan**, against the written data. -/
def entryLitOk (P : Planned) : Bool := Desc.chainAll 32 P && decide (Aligned frD.ds P)

/-- **A yes of the test gives the clause**, at every plan. -/
theorem entryPriced_of_test {P : Planned} (h : entryLitOk P = true) : EntryPricedAt P := by
  have c := Bool.and_eq_true_iff.1 h
  exact pricedRD_aligned ((Desc.chainAll_iff 32 P).1 c.1).1 frD.ds (of_decide_eq_true c.2)

/-- **The closed statement.** -/
def EntryPricesWritten : Prop :=
  EntryPricedAt pricedEntryFull ∧ Desc.chainAll 32 pricedEntryFull = true

/-- The test says yes at the written priced plan. -/
theorem entry_lit_ok : entryLitOk pricedEntryFull = true := by decide +kernel

/-- **It holds.** -/
theorem entryPricesWritten : EntryPricesWritten :=
  ⟨entryPriced_of_test entry_lit_ok, (Bool.and_eq_true_iff.1 entry_lit_ok).1⟩

/-- 41 rounds of data against 41 priced rounds; the plan has 42. -/
theorem entry_lengths :
    frD.ds.length = 41 ∧ (chainRounds pricedEntryFull).length = 41 ∧
      pricedEntryFull.rounds.length = 42 := by decide +kernel

/-- The one more is the plan's first: the entry "RECORD". -/
theorem entry_record :
    pricedEntryFull.rounds.head?.map (·.entry.name) = some Fmt.recordName ∧
      (chainRounds pricedEntryFull).map (·.entry) =
        pricedEntryFull.rounds.tail.map (·.entry) := by decide +kernel

/-- No entry of the plan has the name "LIN point". -/
theorem entry_no_lin :
    (pricedEntryFull.rounds.all fun r => r.entry.name != "LIN point") = true := by decide +kernel

/-- The written data as the compiled slot takes them are these, carried round by round. -/
theorem dsFull_lib : dsFull = frD.ds.map TypedOracleCompiler.Run.PQ.ofLib := by
  rw [dsFull_eq, fr_ds_C]

end VerifiableInference.Number.ByRuns

#print axioms VerifiableInference.Number.ByRuns.pricedAt_iff
#print axioms VerifiableInference.Number.ByRuns.toRD_lift
#print axioms VerifiableInference.Number.ByRuns.pricedRD_aligned
#print axioms VerifiableInference.Number.ByRuns.entryPriced_of_test
#print axioms VerifiableInference.Number.ByRuns.entry_lit_ok
#print axioms VerifiableInference.Number.ByRuns.entryPricesWritten
#print axioms VerifiableInference.Number.ByRuns.entry_lengths
#print axioms VerifiableInference.Number.ByRuns.entry_record
#print axioms VerifiableInference.Number.ByRuns.entry_no_lin
#print axioms VerifiableInference.Number.ByRuns.dsFull_lib
