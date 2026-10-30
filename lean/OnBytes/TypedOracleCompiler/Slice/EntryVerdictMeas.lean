-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryVerdictMeas.lean: the functions under the integrals in the bounds about the
closed check of an entry file are measurable.

OnBytes/TypedOracleCompiler/Slice/EntryVerdictBound.lean bounds `Rom.Pr A.withTrace (EntryBadFull rd cfg)`,
`Rom.Pr Mk.withTrace (EntryFailFull cfg)` and the like at the small example. `Rom.Pr c E`
(Rom/Measure.lean) is the lower integral, over the function g, of the probability over c's coins
that the outcome lies in E g, and these four events read g. An upper bound on a lower integral says
less than it seems if the function under the integral is not measurable. Here two things are shown
of each of the four events: for every outcome, the functions g under which it lies in the event are
a measurable set; and so the function of g under the integral is measurable. So each integral is the
average that it is meant to be.

Main names (namespace `TypedOracleCompiler.Slice`):
  `measurableSet_verdictG`: at a ground G whose description is in order at every digest of 32 bytes
    (hok) and whose pins fit at every digest (hpins), for every outcome x: the functions g under
    which the right side of `entryLose_iff` (EntryVerdictBound.lean) holds of x are a measurable
    set. By `entryLose_iff` and `measurableSet_entryLose` (OnBytes/TypedOracleCompiler/Slice/EntryOneMeas.lean).
  `measurableSet_entryBadFull`, `measurableSet_entryBadSmall`, `measurableSet_entryFailFull`,
    `measurableSet_entryFailSmall`: the same of the four events. The closed check is the tests on
    the parsed value, which do not read g, and `verifyEntryG`
    (OnBytes/TypedOracleCompiler/Slice/EntryVerdictG.lean), by `verifyEntryFull_iff` and `verifyEntrySmall_iff`
    (OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean). A parsed value can be written into files and read
    back: `AskedSection.exists_section` (OnBytes/TypedOracleCompiler/Slice/AskedSection.lean).
  `measurable_entryBadFull`, `measurable_entryBadSmall`: for every parser rd, all cfg and every
    maker A of files, `fun g => Rom.PrCoins g A.withTrace (EntryBadFull rd cfg g)` is measurable.
  `measurable_entryFailFull`, `measurable_entryFailSmall`: for all cfg and every maker Mk of a
    parsed value, `fun g => Rom.PrCoins g Mk.withTrace (EntryFailFull cfg g)` is measurable.
  These last four are closed by `Rom.measurable_PrCoins_dep` (Rom/Measure.lean).

No premise stands in the eight statements on the four events: at both grounds hok and hpins are
theorems (`record_ok`, `small_record_ok`, OnBytes/TypedOracleCompiler/Slice/EntryDescOk.lean; `record_pins`,
`small_record_pins`, OnBytes/K/Left/Pins.lean).

Limits: no bound is added and no statement of EntryVerdictBound.lean is turned. Of the limits in its
head this file answers one, the last sentence of its Limit 5: that the four events are not shown
measurable there. All its other limits stand. The σ-algebra on the functions is Mathlib's product
one, over the oracles and their points; Rom/Measure.lean makes every subset of an oracle's finite
range an event, and the uniform measure `Rom.U` lives on that product. No equation between integrals
is stated. No budget is asked of a maker. Nothing on the key file's or the proof file's events.
Three proofs raise two of Lean's limits (`maxRecDepth`, `maxHeartbeats`), as the proofs of
EntryVerdictBound.lean at the same terms do; whether each needs it was not tried.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryVerdictBound
import OnBytes.TypedOracleCompiler.Slice.EntryOneMeas

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (SgX View)
open TypedOracleCompiler.Run.PQ (XD bodyS)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open OnBytes.Tie (EntryGround linkAtCfg keyAt AskedE)
open OnBytes.Slice (Tab s0Of decRec GE GF DecR Raw)
open OnBytes.Slice.Shapes (Files FileSpec Size Cfg dgOf dgOf_size pubS₀ pubS₁ zFull zSmall rdC)
open OnBytes.Slice.Shapes.FileSpec (own₀ own₁)
open MeasureTheory
open scoped ENNReal

section Ground
variable (G : EntryGround)
  (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- At a ground whose description is in order (hok) and whose pins fit (hpins): the functions under
which the event of `entryLose_iff`, said in the terms of the check, holds of an outcome are a
measurable set. The letters εs and Bk are `entryLose_iff`'s; they do not stand in the set, so any
value serves. -/
theorem measurableSet_verdictG (eM : ℕ) (rd : Files → Option AskedE) (cfg : Cfg) (εs : ℝ≥0∞)
    (Bk : ℕ) (rdL : Tab → Tab → Trace (rom 256) → Dig 256 → Raw SgX)
    (hpins : ∀ c, pinsFit (entryXD G c) G.q.link.table = true)
    (x : Files × Trace (rom 256)) :
    MeasurableSet {g : Fam (rom 256) |
      ∃ a, rd x.1 = some a ∧ verifyEntryG G hok cfg a g = true ∧
        ¬ DecR.LangE (DecR.wayColl (decRec (groundSize G eM).T (groundSize G eM).v
            (groundSize G eM).eM (groundSize G eM).lg (groundSize G eM).s))
          ((xOfAskedC (groundSize G eM).lg (groundSize G eM).s a).2.1,
            anT (groundSize G eM).v (groundSize G eM).s
              (xOfAskedC (groundSize G eM).lg (groundSize G eM).s a).1.1)
          ((xOfAskedC (groundSize G eM).lg (groundSize G eM).s a).2.2,
            anT (groundSize G eM).v (groundSize G eM).s
              (xOfAskedC (groundSize G eM).lg (groundSize G eM).s a).1.2)
          (rdL (own₀ (pubS₀ cfg) g) (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) g) x.2
            (_root_.Run.bytesToDig a.first.root))
          (rdL (own₀ (pubS₀ cfg) g) (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) g) x.2
            (_root_.Run.bytesToDig a.further.root))} := by
  have h : MeasurableSet {g : Fam (rom 256) |
    x ∈ EntryLose (groundSize G eM).T (groundSize G eM).v (groundSize G eM).eM
        (anT (groundSize G eM).v (groundSize G eM).s) ((homeOf G hok eM).at cfg ((homeOf G hok
          eM).convOf cfg (convRd G hok eM rd))) εs
        ((homeOf G hok eM).typ cfg ((homeOf G hok eM).convOf cfg (convRd G hok eM rd)) εs) 0 Bk
          (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) rdL g} :=
    measurableSet_entryLose _ _ _ _ _ _ _ _ _ _ _ _ x
  exact h.congr (Set.ext fun g => entryLose_iff G hok eM rd cfg εs Bk rdL hpins g x)

end Ground

/-! ## The events on a maker's files -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- For every outcome: the functions under which it lies in `EntryBadFull rd cfg` are a
measurable set. -/
theorem measurableSet_entryBadFull (rd : Files → Option AskedE) (cfg : Cfg)
    (x : Files × Trace (rom 256)) : MeasurableSet {g | x ∈ EntryBadFull rd cfg g} := by
  have h := measurableSet_verdictG OnBytes.Tie.recordGround record_ok OnBytes.Params.recordRadius
    rd cfg 0 142 (rdC zFull cfg) OnBytes.K.Left.record_pins x
  by_cases hf : ∃ a, rd x.1 = some a ∧ askedFit OnBytes.Tie.recordGround.q.link.table a = true
  · refine h.congr (Set.ext fun g => ⟨?_, ?_⟩)
    · rintro ⟨a, ha, hy, hl⟩
      obtain ⟨a', ha', hf'⟩ := hf
      obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
      exact ⟨a', ha, (verifyEntryFull_iff cfg a' g).2 ⟨hf', hy⟩, hl⟩
    · rintro ⟨a, ha, hy, hl⟩
      exact ⟨a, ha, ((verifyEntryFull_iff cfg a g).1 hy).2, hl⟩
  · refine MeasurableSet.empty.congr (Set.ext fun g => ⟨fun h0 => False.elim h0, ?_⟩)
    rintro ⟨a, ha, hy, -⟩
    exact hf ⟨a, ha, ((verifyEntryFull_iff cfg a g).1 hy).1⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The same at the small example. -/
theorem measurableSet_entryBadSmall (rd : Files → Option AskedE) (cfg : Cfg)
    (x : Files × Trace (rom 256)) : MeasurableSet {g | x ∈ EntryBadSmall rd cfg g} := by
  have h := measurableSet_verdictG OnBytes.Tie.smallRecordGround small_record_ok
    OnBytes.Params.smallRecordRadius rd cfg 0 101 (rdC zSmall cfg)
    OnBytes.K.Left.small_record_pins x
  by_cases hf : ∃ a, rd x.1 = some a ∧
      askedFit OnBytes.Tie.smallRecordGround.q.link.table a = true
  · refine h.congr (Set.ext fun g => ⟨?_, ?_⟩)
    · rintro ⟨a, ha, hy, hl⟩
      obtain ⟨a', ha', hf'⟩ := hf
      obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
      exact ⟨a', ha, (verifyEntrySmall_iff cfg a' g).2 ⟨hf', hy⟩, hl⟩
    · rintro ⟨a, ha, hy, hl⟩
      exact ⟨a, ha, ((verifyEntrySmall_iff cfg a g).1 hy).2, hl⟩
  · refine MeasurableSet.empty.congr (Set.ext fun g => ⟨fun h0 => False.elim h0, ?_⟩)
    rintro ⟨a, ha, hy, -⟩
    exact hf ⟨a, ha, ((verifyEntrySmall_iff cfg a g).1 hy).1⟩

/-! ## The events on a parsed value -/

/-- For every outcome: the functions under which it lies in `EntryFailFull cfg` are a measurable
set. By writing the parsed value into files and reading it back. -/
theorem measurableSet_entryFailFull (cfg : Cfg) (y : AskedE × Trace (rom 256)) :
    MeasurableSet {g | y ∈ EntryFailFull cfg g} := by
  obtain ⟨enc, rd, hs⟩ := AskedSection.exists_section
  refine (measurableSet_entryBadFull rd cfg (enc y.1, y.2)).congr
    (Set.ext fun g => ⟨?_, ?_⟩)
  · rintro ⟨a, ha, hy, hl⟩
    obtain rfl : a = y.1 := Option.some.inj (ha.symm.trans (hs y.1))
    exact ⟨hy, hl⟩
  · rintro ⟨hy, hl⟩
    exact ⟨y.1, hs y.1, hy, hl⟩

/-- The same at the small example. -/
theorem measurableSet_entryFailSmall (cfg : Cfg) (y : AskedE × Trace (rom 256)) :
    MeasurableSet {g | y ∈ EntryFailSmall cfg g} := by
  obtain ⟨enc, rd, hs⟩ := AskedSection.exists_section
  refine (measurableSet_entryBadSmall rd cfg (enc y.1, y.2)).congr
    (Set.ext fun g => ⟨?_, ?_⟩)
  · rintro ⟨a, ha, hy, hl⟩
    obtain rfl : a = y.1 := Option.some.inj (ha.symm.trans (hs y.1))
    exact ⟨hy, hl⟩
  · rintro ⟨hy, hl⟩
    exact ⟨y.1, hs y.1, hy, hl⟩

/-! ## The integrands -/

/-- The integrand of the bound for makers of files, at the full size, is measurable. -/
theorem measurable_entryBadFull (rd : Files → Option AskedE) (cfg : Cfg)
    (A : OComp (rom 256) Files) :
    Measurable fun g => Rom.PrCoins g A.withTrace (EntryBadFull rd cfg g) :=
  Rom.measurable_PrCoins_dep A.withTrace (EntryBadFull rd cfg) (measurableSet_entryBadFull rd cfg)

/-- The same at the small example. -/
theorem measurable_entryBadSmall (rd : Files → Option AskedE) (cfg : Cfg)
    (A : OComp (rom 256) Files) :
    Measurable fun g => Rom.PrCoins g A.withTrace (EntryBadSmall rd cfg g) :=
  Rom.measurable_PrCoins_dep A.withTrace (EntryBadSmall rd cfg)
    (measurableSet_entryBadSmall rd cfg)

/-- The integrand of the bound for makers of a parsed value, at the full size, is measurable. -/
theorem measurable_entryFailFull (cfg : Cfg) (Mk : OComp (rom 256) AskedE) :
    Measurable fun g => Rom.PrCoins g Mk.withTrace (EntryFailFull cfg g) :=
  Rom.measurable_PrCoins_dep Mk.withTrace (EntryFailFull cfg) (measurableSet_entryFailFull cfg)

/-- The same at the small example. -/
theorem measurable_entryFailSmall (cfg : Cfg) (Mk : OComp (rom 256) AskedE) :
    Measurable fun g => Rom.PrCoins g Mk.withTrace (EntryFailSmall cfg g) :=
  Rom.measurable_PrCoins_dep Mk.withTrace (EntryFailSmall cfg) (measurableSet_entryFailSmall cfg)

end TypedOracleCompiler.Slice
