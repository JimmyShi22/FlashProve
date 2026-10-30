-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Std.lean: what the statements on an entry file ask of a configuration, as one value
of Bool that can be evaluated on the three public files.

A statement on the verifier is made for configurations that are in order at given sizes. `StdCfg`
holds the three public files as bytes; `StdSize` holds what the first 32 lines of the parameter file
say, the shape of the stored tables and the radius at which a stored table is read; `stdFull` and
`stdSmall` are the two defaults of the setting "record with work", made of the typed values of
OnBytes/Params/EntryStagesRecord.lean, OnBytes/Params/RecordRound.lean and their small likes.
`stdEntry z cfg` has two clauses. `stdLines`: the reader of a parameter file returns z's lines on
the parameter file. `stdBytes`: what is hashed for the configuration's digest, in one call, has at
most 2 ^ 32 - 144 bytes, the number in the domain of the format's hash (`Fmt.hDom`,
Fmt/Rules23.lean). From a yes follow the two propositions (`stdEntry_lines`, `stdEntry_bytes`). An
entry's sizes hang on the lines alone; so at the two defaults a yes gives that the parameter file
reads as the typed lines, for which it is a theorem that an entry's sizes, codes and plan are the
typed ones, that the plan holds in the planner's reckoning, and that at every digest the parameter
bytes of an entry's chain are spelled from them (`stdEntry_full`, `stdEntry_small`).
A test that is not in this library evaluates `stdEntry` on copies of the public files.

Main definitions: `StdCfg`, `StdSize`, `stdFull`, `stdSmall`, `stdLines`, `stdBytes`, `stdEntry`.
Main theorems: `stdEntry_lines`, `stdEntry_bytes`, `stdEntry_full`, `stdEntry_small`.
What is not claimed: what a key's or a proof's statements ask of a configuration: of the layout
file, the scale file and the parameter file's lines after the first 32 `stdEntry` asks their lengths
alone. That the configuration's digest is `recordCfg` or `smallRecordCfg`, the typed digests under
which the rounds of OnBytes/Params/EntryDryRecord.lean and its small like are run dry: `stdEntry`
does not ask it, and no law here says that those rounds are the same at another digest. That z's
shape and radius belong to z's lines: at the two defaults that is shown elsewhere (`record_link`,
`rr_radius` and their small likes); for another z nothing ties the three fields. That 2 ^ 32 - 144
is the hash's bound: it was read off `Fmt.hDom`; no law here names that function. For proofs only;
the program, that is the Lean port built from OnBytes/, does not import this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Params.EntryDescRecordSmall
import OnBytes.Params.RecordRoundSmall

set_option autoImplicit false

namespace OnBytes.Params

/-- The three public files of a configuration, as bytes: the parameter file, the layout file, the
scale file. -/
structure StdCfg where
  pol : ByteArray
  lay : ByteArray
  KL : ByteArray

/-- The sizes at which a statement is made: what the first 32 lines of the parameter file say, the
shape of the stored tables, and the radius at which a stored table is read. -/
structure StdSize where
  lines : Lines
  shape : IndexShape
  eM : ℕ

/-- The full-size default of the setting "record with work". -/
def stdFull : StdSize := ⟨recordLines, recordLink.table, recordRadius⟩

/-- The small default. -/
def stdSmall : StdSize := ⟨smallRecordLines, smallRecordLink.table, smallRecordRadius⟩

/-- The clause on the lines: the reader of a parameter file returns z's lines on the parameter
file. -/
def stdLines (z : StdSize) (cfg : StdCfg) : Bool :=
  decide ((readLines cfg.pol).toOption.map (·.1) = some z.lines)

/-- The clause on the files' sizes: what is hashed for the configuration's digest, in one call, is
within the bound on the bytes in the domain of the format's hash (`Fmt.hDom`). -/
def stdBytes (cfg : StdCfg) : Bool :=
  decide ((Fmt.configBytes [cfg.pol, cfg.lay, cfg.KL]).size ≤ 2 ^ 32 - 144)

/-- What an entry file's statements ask of a configuration. -/
def stdEntry (z : StdSize) (cfg : StdCfg) : Bool := stdLines z cfg && stdBytes cfg

/-- From a yes: the lines. -/
theorem stdEntry_lines {z : StdSize} {cfg : StdCfg} (h : stdEntry z cfg = true) :
    (readLines cfg.pol).toOption.map (·.1) = some z.lines := by
  unfold stdEntry stdLines at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- From a yes: the sizes. -/
theorem stdEntry_bytes {z : StdSize} {cfg : StdCfg} (h : stdEntry z cfg = true) :
    (Fmt.configBytes [cfg.pol, cfg.lay, cfg.KL]).size ≤ 2 ^ 32 - 144 := by
  unfold stdEntry stdBytes at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- At the full-size default, from a yes: the parameter file reads as `recordLines`. Beside it
stand two theorems on `recordLines` that make no use of the yes or of the configuration: an entry's
sizes, codes and plan are the typed ones and the plan holds in the planner's reckoning
(`record_sized`); at every digest the parameter bytes of an entry's chain are spelled from the typed
plan, codes and shape. -/
theorem stdEntry_full {cfg : StdCfg} (h : stdEntry stdFull cfg = true) :
    (readLines cfg.pol).toOption.map (·.1) = some recordLines ∧
      (∃ P, entrySized recordLines =
          .ok (⟨recordLink, recordTable, ⟨recordG1, 97, recordStages⟩⟩, recordCodes, P) ∧
        P.plan = recordPlan ∧ P.holds = true) ∧
      ∀ c : ByteArray, entryParams recordLines c =
        .ok (Fmt.paramsBytes recordPlan c
          [("codes", spellCodes recordCodes), ("the link", spellLink recordLink)]) :=
  ⟨stdEntry_lines h, record_sized, record_params⟩

/-- The like at the small default: the first clause alone hangs on the yes. -/
theorem stdEntry_small {cfg : StdCfg} (h : stdEntry stdSmall cfg = true) :
    (readLines cfg.pol).toOption.map (·.1) = some smallRecordLines ∧
      (∃ P, entrySized smallRecordLines =
          .ok (⟨smallRecordLink, smallRecordTable, ⟨smallRecordG1, 97, smallRecordStages⟩⟩,
            smallRecordCodes, P) ∧
        P.plan = smallRecordPlan ∧ P.holds = true) ∧
      ∀ c : ByteArray, entryParams smallRecordLines c =
        .ok (Fmt.paramsBytes smallRecordPlan c
          [("codes", spellCodes smallRecordCodes), ("the link", spellLink smallRecordLink)]) :=
  ⟨stdEntry_lines h, small_record_sized, small_record_params⟩

end OnBytes.Params
