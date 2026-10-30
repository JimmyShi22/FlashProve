-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Oracle/VerdictOnFilesYes.lean: what a yes of the entry file's form for a run gives, as
statements: from `runEntryFilesFull cfg d = true` (OnBytes/K/Oracle/VerdictOnFilesRun.lean; and the
small like) to a yes of the closed check, and of "read, then check", at the function on bit strings
that is made from the format's hash.

Why. The form for a run is a value of Bool that an evaluator can find. What its being true says of
the closed check followed from two lemmas by a few lines that stood in no file. Here they stand.

Main names (namespace `OnBytes.K.Oracle`; each also with Small):
  `verifyEntryFull_of_runFiles`: there is a value a that the asking half returns on the files at the
    format's own oracle on bytes, and `verifyEntryFull cfg a Run.oBits = true`. No premise beside
    the yes.
  `verifyEntryFilesFull_of_runFiles`: `verifyEntryFilesFull cfg d Run.oBits = true`, where what is
    hashed for the digest of the three public files is within the hash's bound on lengths.

What is not claimed. CONDITIONALS: that the form for a run says yes on any files is an evaluation's
word, and no evaluation stands in this file (an asking file for the small example:
lean/Ask/EntryFilesSmall.lean; for the full size there is none). ONE FIXED FUNCTION: `Run.oBits` is
made from Lean's BLAKE2b through the format's byte coding: nothing is said at a drawn function, and
no probability stands here: a yes at one function shows that the closed check does not refuse
everything there, and no more: the fixed function stands here as a witness that a yes exists; no
proof around the verifier rests on it. All that the heads of VerdictOnFiles.lean and
VerdictOnFilesRun.lean do not claim. Nothing on soundness. For proofs only; no program imports this
file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Oracle.VerdictOnFilesRun

set_option autoImplicit false

namespace OnBytes.K.Oracle
open Rom TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.EntryPageSafe (gOf gOf_oracle)
open OnBytes.Tie (recordGround smallRecordGround linkAtCfg keyAt AskedE askedAt askedAt_oBits)
open OnBytes.Slice.Shapes (Cfg)

/-- **What a yes of the form for a run gives, at the full size**: the asking half returns a value a
at the format's own oracle on bytes, and the closed check says yes on a at the function on bit
strings that is made from the format's hash. No premise beside the yes. -/
theorem verifyEntryFull_of_runFiles (cfg : Cfg) (d : Slice.Shapes.Files)
    (h : runEntryFilesFull cfg d = true) :
    ∃ a, askedAt _root_.Fmt.oracle
        (linkAtCfg recordGround.q (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))
        (keyAt recordGround.q.link.table (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
          d.key).2.2 d.ent = some a ∧
      verifyEntryFull cfg a _root_.Run.oBits = true := by
  unfold runEntryFilesFull at h
  cases ha : askedAt _root_.Fmt.oracle
      (linkAtCfg recordGround.q (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))
      (keyAt recordGround.q.link.table (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
        d.key).2.2 d.ent with
  | none =>
    rw [ha] at h
    cases h
  | some a =>
    rw [ha] at h
    refine ⟨a, rfl, ?_⟩
    rw [← gOf_oracle, ← runEntryFull_eq]
    exact h

/-- The same for "read, then check" on the files. Asked beside the yes: what is hashed for the
digest of the three public files is within the hash's bound on lengths. -/
theorem verifyEntryFilesFull_of_runFiles (cfg : Cfg)
    (hb : (_root_.Fmt.configBytes [cfg.pol, cfg.lay, cfg.KL]).size ≤ 2 ^ 32 - 144)
    (d : Slice.Shapes.Files) (h : runEntryFilesFull cfg d = true) :
    verifyEntryFilesFull cfg d _root_.Run.oBits = true :=
  (runEntryFilesFull_eq cfg hb d).symm.trans h

/-- **What a yes of the form for a run gives, at the small example**: the asking half returns a
value a at the format's own oracle on bytes, and the closed check says yes on a at the function on
bit strings that is made from the format's hash. No premise beside the yes. -/
theorem verifyEntrySmall_of_runFiles (cfg : Cfg) (d : Slice.Shapes.Files)
    (h : runEntryFilesSmall cfg d = true) :
    ∃ a, askedAt _root_.Fmt.oracle
        (linkAtCfg smallRecordGround.q (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))
        (keyAt smallRecordGround.q.link.table
          (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]) d.key).2.2 d.ent = some a ∧
      verifyEntrySmall cfg a _root_.Run.oBits = true := by
  unfold runEntryFilesSmall at h
  cases ha : askedAt _root_.Fmt.oracle
      (linkAtCfg smallRecordGround.q (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))
      (keyAt smallRecordGround.q.link.table (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
        d.key).2.2 d.ent with
  | none =>
    rw [ha] at h
    cases h
  | some a =>
    rw [ha] at h
    refine ⟨a, rfl, ?_⟩
    rw [← gOf_oracle, ← runEntrySmall_eq]
    exact h

/-- The same for "read, then check" on the files. Asked beside the yes: what is hashed for the
digest of the three public files is within the hash's bound on lengths. -/
theorem verifyEntryFilesSmall_of_runFiles (cfg : Cfg)
    (hb : (_root_.Fmt.configBytes [cfg.pol, cfg.lay, cfg.KL]).size ≤ 2 ^ 32 - 144)
    (d : Slice.Shapes.Files) (h : runEntryFilesSmall cfg d = true) :
    verifyEntryFilesSmall cfg d _root_.Run.oBits = true :=
  (runEntryFilesSmall_eq cfg hb d).symm.trans h

end OnBytes.K.Oracle

#print axioms OnBytes.K.Oracle.verifyEntryFull_of_runFiles
#print axioms OnBytes.K.Oracle.verifyEntryFilesFull_of_runFiles
#print axioms OnBytes.K.Oracle.verifyEntrySmall_of_runFiles
#print axioms OnBytes.K.Oracle.verifyEntryFilesSmall_of_runFiles
