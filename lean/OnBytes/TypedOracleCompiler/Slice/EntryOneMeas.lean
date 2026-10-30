-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryOneMeas.lean: the integrand of `entry_one_world` is measurable.

`entry_one_world` (OnBytes/TypedOracleCompiler/Slice/EntryOne.lean) bounds `Rom.Pr A.withTrace (EntryLose …)`.
`Rom.Pr c E` (Rom/Measure.lean) is the lower integral, over the family g of oracle functions, of the
probability over c's coins that the outcome lies in E g. The event `EntryLose` reads g. An upper
bound on a lower integral says less than it seems if the function under the integral is not
measurable. Here that function is shown to be measurable, so the integral is the average meant.

Why it holds. For a fixed outcome the event looks at g in two ways: at the public strings, for the
two tables `own₀ S₀ g` and `own₁ S₀ S₁ g`; and through `(chk …).det g` (Rom/Cache.lean): the run
under g of the entry's checker, a tree of queries, in which every coin yields 0. On each path these
are finitely many places, each with finitely many answers.

Main names:
  `EntryLoseAt … T₀ T₁ g`: the text of `EntryLose` with two fixed tables in the place of the
    oracle's own. `entryLose_eq`: by unfolding, `EntryLose` is `EntryLoseAt` at the oracle's own.
  `measurableSet_entryLoseAt`, `measurableSet_entryLose`: for every outcome x the oracles g under
    which x lies in the event are a measurable set.
  `measurable_entryLose`: for every maker A the function
    `fun g => Rom.PrCoins g A.withTrace (EntryLose … g)` is measurable.

The proofs follow `measurableSet_loseAt` and `measurableSet_lose`
(OnBytes/TypedOracleCompiler/Slice/ShapesOne.lean). Tools: `measurableSet_det` (OnBytes/Slice/AtSet.lean);
`measurableSet_dep`, `askL`, `askL_toList` (OnBytes/TypedOracleCompiler/Slice/ShapesMeas.lean);
`Rom.measurable_PrCoins_dep` (Rom/Measure.lean). No premise: at all letters of EntryOne.lean.
`full_one_world` (OnBytes/TypedOracleCompiler/Slice/EntryFullTop.lean) and `small_one_world`
(OnBytes/TypedOracleCompiler/Slice/EntrySmallTop.lean) bound `EntryLose` at values of these letters, so the theorem
serves them as an instance; no line of Lean in this file lays these values in.

Limits: no bound is added and no statement is turned. EntryOne.lean states three bounds with
`Rom.Pr`: `entry_one_world`, `entry_yes_sound`, `entry_clash_rare`. This file serves the first
alone. The event of `entry_yes_sound` reads `recU g k`, and recU is a free letter: its integrand
need not be measurable, and this file does not serve it. The event of `entry_clash_rare` is not
treated here; for the event `ClashOwn` of a file's specification ShapesOne.lean has
`measurableSet_clashOwn`. The σ-algebra on the families is Mathlib's product one, over the oracles
and their points; Rom/Measure.lean makes every subset of an oracle's finite range an event, and the
uniform measure `Rom.U` lives on that product. Nothing on the key file's or the proof file's events.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryOne

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob Cb _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (SgX)
open OnBytes.Slice (DecR decRec GE NZ Tab Raw measurableSet_dep measurableSet_det)
open OnBytes.Slice.Shapes (Files FileSpec own cutT askL askL_toList)
open OnBytes.Slice.Shapes.FileSpec (own₀ own₁)
open MeasureTheory
open scoped ENNReal

variable {An : Type} {lg s : ℕ} [DecidableEq (Sd1 lg s)] {d₁ : Sd1 lg s}
  (T : _root_.Fmt.M1.Code) (v eM : ℕ)
  (an : An → (decRec T v eM lg s).ix.Row × (decRec T v eM lg s).Z.S → GE)
  (Θ : Tab → Tab → EntryAt An lg s d₁) (εs : ℝ≥0∞)
  (typ : ∀ T₀ T₁, Files → OComp (rom 256) (Option ((Θ T₀ T₁).base T v eM an εs).Out))
  (tT Bk : ℕ) (S₀ : Finset (List Bool)) (S₁ : Tab → Finset (List Bool))
  (rd : Tab → Tab → Trace (rom 256) → Dig 256 → Raw SgX)

/-- The entry file's event at two fixed tables. -/
def EntryLoseAt (T₀ T₁ : Tab) (g : Fam (rom 256)) : Set (Files × Trace (rom 256)) :=
  {x | ∃ (o : OutE (Θ T₀ T₁).Z) (r₀ r₁ : Dig 256),
    (((entrySpec T v eM an Θ εs typ tT Bk).toO S₀ S₁ T₀ T₁).chk x.1).det g = some o ∧
      o.1 = [r₀, r₁] ∧
    ¬ DecR.LangE (DecR.wayColl (decRec T v eM lg s)) (recE₀ T v eM an o) (recE₁ T v eM an o)
      (rd T₀ T₁ x.2 r₀) (rd T₀ T₁ x.2 r₁)}

/-- In one world the tables are the oracle's own values at the public strings. -/
theorem entryLose_eq (g : Fam (rom 256)) :
    EntryLose T v eM an Θ εs typ tT Bk S₀ S₁ rd g =
      EntryLoseAt T v eM an Θ εs typ tT Bk S₀ S₁ rd (own₀ S₀ g) (own₁ S₀ S₁ g) g := rfl

/-- At fixed tables the oracles under which an outcome lies in the event are a measurable set. -/
theorem measurableSet_entryLoseAt (T₀ T₁ : Tab) (x : Files × Trace (rom 256)) :
    MeasurableSet {g | x ∈ EntryLoseAt T v eM an Θ εs typ tT Bk S₀ S₁ rd T₀ T₁ g} :=
  measurableSet_det (((entrySpec T v eM an Θ εs typ tT Bk).toO S₀ S₁ T₀ T₁).chk x.1)
    {a | ∃ (o : OutE (Θ T₀ T₁).Z) (r₀ r₁ : Dig 256), a = some o ∧ o.1 = [r₀, r₁] ∧
      ¬ DecR.LangE (DecR.wayColl (decRec T v eM lg s)) (recE₀ T v eM an o) (recE₁ T v eM an o)
        (rd T₀ T₁ x.2 r₀) (rd T₀ T₁ x.2 r₁)}

/-- So they are in one world. -/
theorem measurableSet_entryLose (x : Files × Trace (rom 256)) :
    MeasurableSet {g | x ∈ EntryLose T v eM an Θ εs typ tT Bk S₀ S₁ rd g} := by
  have h := measurableSet_dep (askL S₀.toList)
    (fun T₀ => {g | x ∈ EntryLoseAt T v eM an Θ εs typ tT Bk S₀ S₁ rd T₀
      (cutT (S₁ T₀) (own g)) g}) (fun T₀ => by
      have h' := measurableSet_dep (askL (S₁ T₀).toList)
        (fun T₁ => {g | x ∈ EntryLoseAt T v eM an Θ εs typ tT Bk S₀ S₁ rd T₀ T₁ g})
        (fun T₁ => measurableSet_entryLoseAt T v eM an Θ εs typ tT Bk S₀ S₁ rd T₀ T₁ x)
      simp only [askL_toList] at h'
      exact h')
  simp only [askL_toList] at h
  exact h

/-- The integrand of `entry_one_world` is measurable, for every maker. -/
theorem measurable_entryLose (A : OComp (rom 256) Files) :
    Measurable fun g => Rom.PrCoins g A.withTrace
      (EntryLose T v eM an Θ εs typ tT Bk S₀ S₁ rd g) :=
  Rom.measurable_PrCoins_dep A.withTrace (EntryLose T v eM an Θ εs typ tT Bk S₀ S₁ rd)
    (measurableSet_entryLose T v eM an Θ εs typ tT Bk S₀ S₁ rd)

end TypedOracleCompiler.Slice
