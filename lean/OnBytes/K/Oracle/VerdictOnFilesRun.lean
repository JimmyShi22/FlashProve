-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Oracle/VerdictOnFilesRun.lean: "read, then check" of an entry file
(OnBytes/K/Oracle/VerdictOnFiles.lean) at the format's hash, in a form for a run.

Why. `verifyEntryFilesFull cfg d g` takes a function g on all bit strings. At the function that is
made from the format's hash (`Run.oBits`) it is equal to a term that hashes bytes and goes along
short lists, which Lean's evaluator can be given.

Main names (namespace `OnBytes.K.Oracle`; each also with Small, at the small example):
  `runEntryFilesFull cfg d`: the digest of the three public files as the format makes it; the key
    file's table by a plain parse; the asking half's value at the format's own oracle on bytes
    (`askedAt Fmt.oracle`, OnBytes/Tie/EntryAsked.lean); then `runEntryFull` at that oracle
    (OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean).
  `runEntryFilesFull_eq`: it is `verifyEntryFilesFull cfg d Run.oBits`, where what is hashed for the
    digest of the three public files has at most 2 ^ 32 - 144 bytes.
  `verifyEntryFilesFull_of_conv`: from a run behind the strict converter: if `convE`
    (OnBytes/TypedOracleCompiler/Slice/EntryConv.lean) returns a on the key file's table and the entry file, and
    `runEntryFull cfg a Fmt.oracle` is true, and two lengths are within the hash's bound, then
    `verifyEntryFilesFull cfg d Run.oBits` is true.

What is not claimed. No run is on record here: that any of these terms says yes on any files, or no
on damaged ones, is not shown. An evaluation is a run and no theorem. ONE FIXED HASH: the bounds of
VerdictOnFiles.lean are over a drawn function, and no theorem carries a probability from there to
here: that step is the assumption of every argument in the random-oracle model. THE FUNCTION OF
WHICH THE BOUND SPEAKS IS `verifyEntryFilesFull` | `Small`, of (public files, files, hash function):
these two terms are its value at one function, written otherwise. The hash is not an argument of
these two terms: at another function on bytes no equation is given. The program does not call them.
All that the heads of VerdictOnFiles.lean and EntryVerdictRun.lean do not claim. Nothing on
soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Oracle.VerdictOnFiles
import OnBytes.K.Oracle.NotEmpty

set_option autoImplicit false

namespace OnBytes.K.Oracle
open Rom TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.EntryPageSafe (gOf gOf_oracle)
open OnBytes.Tie (recordGround smallRecordGround linkAtCfg keyAt AskedE askedAt askedAt_oBits)
open OnBytes.Slice.Shapes (Cfg)

/-- **The form for a run, at the format's hash, at the full size**: the digest of the three public
files as the format makes it; the key file's table by a plain parse; the asking half's value at the
format's own oracle on bytes; then the closed check's form for a run at that oracle. -/
def runEntryFilesFull (cfg : Cfg) (d : Slice.Shapes.Files) : Bool :=
  match askedAt _root_.Fmt.oracle
      (linkAtCfg recordGround.q (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))
      (keyAt recordGround.q.link.table (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
        d.key).2.2 d.ent with
  | none => false
  | some a => runEntryFull cfg a _root_.Fmt.oracle

/-- The form for a run is "read, then check" at the function on bit strings that is made from the
format's hash. Asked: what is hashed for the digest of the three public files is within the hash's
bound on lengths. -/
theorem runEntryFilesFull_eq (cfg : Cfg)
    (hb : (_root_.Fmt.configBytes [cfg.pol, cfg.lay, cfg.KL]).size ≤ 2 ^ 32 - 144)
    (d : Slice.Shapes.Files) :
    runEntryFilesFull cfg d = verifyEntryFilesFull cfg d _root_.Run.oBits := by
  unfold runEntryFilesFull verifyEntryFilesFull readEntry
  rw [askedAt_oBits, OnBytes.Slice.Shapes.dgOf_own₀ cfg hb]
  cases askedAt _root_.Fmt.oracle
      (linkAtCfg recordGround.q (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))
      (keyAt recordGround.q.link.table (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
        d.key).2.2 d.ent with
  | none => rfl
  | some a =>
    show runEntryFull cfg a _root_.Fmt.oracle = verifyEntryFull cfg a _root_.Run.oBits
    rw [runEntryFull_eq, gOf_oracle]

/-- **The form for a run, at the format's hash, at the small example**: the digest of the three
public files as the format makes it; the key file's table by a plain parse; the asking half's value
at the format's own oracle on bytes; then the closed check's form for a run at that oracle. -/
def runEntryFilesSmall (cfg : Cfg) (d : Slice.Shapes.Files) : Bool :=
  match askedAt _root_.Fmt.oracle
      (linkAtCfg smallRecordGround.q (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))
      (keyAt smallRecordGround.q.link.table (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
        d.key).2.2 d.ent with
  | none => false
  | some a => runEntrySmall cfg a _root_.Fmt.oracle

/-- The form for a run is "read, then check" at the function on bit strings that is made from the
format's hash. Asked: what is hashed for the digest of the three public files is within the hash's
bound on lengths. -/
theorem runEntryFilesSmall_eq (cfg : Cfg)
    (hb : (_root_.Fmt.configBytes [cfg.pol, cfg.lay, cfg.KL]).size ≤ 2 ^ 32 - 144)
    (d : Slice.Shapes.Files) :
    runEntryFilesSmall cfg d = verifyEntryFilesSmall cfg d _root_.Run.oBits := by
  unfold runEntryFilesSmall verifyEntryFilesSmall readEntry
  rw [askedAt_oBits, OnBytes.Slice.Shapes.dgOf_own₀ cfg hb]
  cases askedAt _root_.Fmt.oracle
      (linkAtCfg smallRecordGround.q (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))
      (keyAt smallRecordGround.q.link.table (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
        d.key).2.2 d.ent with
  | none => rfl
  | some a =>
    show runEntrySmall cfg a _root_.Fmt.oracle = verifyEntrySmall cfg a _root_.Run.oBits
    rw [runEntrySmall_eq, gOf_oracle]

/-- What the strict converter returns has the table that it was given as its first table. -/
theorem convE_first {q : Params.Link} {table : Params.TableName} {ent : ByteArray} {a : AskedE}
    (hcv : convE q table ent = some a) : a.first = table := by
  unfold convE at hcv
  cases hr : Entry.read q table ent with
  | error e =>
    rw [hr] at hcv
    cases hcv
  | ok r =>
    rw [hr] at hcv
    obtain ⟨l0, -, hcv⟩ := Option.bind_eq_some_iff.1 hcv
    obtain ⟨l1, -, rfl⟩ := Option.map_eq_some_iff.1 hcv
    rfl

/-- **From a run behind the strict converter to the yes of "read, then check" at the format's hash,
at the full size.** If the strict converter returns a on the key file's table and the entry file, at
the format's digest of the three public files, and the closed check's form for a run says yes on a
at the format's oracle, then "read, then check" says yes on the files at the function made from the
format's hash. Asked beside: two lengths are within the hash's bound. A conditional: that its
premises hold of any files is a run's word. -/
theorem verifyEntryFilesFull_of_conv (cfg : Cfg)
    (hb : (_root_.Fmt.configBytes [cfg.pol, cfg.lay, cfg.KL]).size ≤ 2 ^ 32 - 144)
    (d : Slice.Shapes.Files) (a : AskedE) (he : d.ent.size + 16 ≤ 2 ^ 32 - 144)
    (hcv : convE (linkAtCfg recordGround.q (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))
      (keyAt recordGround.q.link.table (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
        d.key).2.2 d.ent = some a)
    (hrun : runEntryFull cfg a _root_.Fmt.oracle = true) :
    verifyEntryFilesFull cfg d _root_.Run.oBits = true := by
  have hy : verifyEntryFull cfg a _root_.Run.oBits = true := by
    rw [← gOf_oracle, ← runEntryFull_eq]
    exact hrun
  have h0 := (askedFit_roots _ a ((verifyEntryFull_iff cfg a _).1 hy).1).1
  rw [convE_first hcv] at h0
  refine (verifyEntryFilesFull_iff cfg d _).2 ⟨a, ?_, hy⟩
  unfold readEntry
  rw [OnBytes.Slice.Shapes.dgOf_own₀ cfg hb]
  exact asked_of_conv recordGround (Params.configurationDigest_size _) h0 he hcv

/-- **From a run behind the strict converter to the yes of "read, then check" at the format's hash,
at the small example.** If the strict converter returns a on the key file's table and the entry
file, at the format's digest of the three public files, and the closed check's form for a run says
yes on a at the format's oracle, then "read, then check" says yes on the files at the function made
from the format's hash. Asked beside: two lengths are within the hash's bound. A conditional: that
its premises hold of any files is a run's word. -/
theorem verifyEntryFilesSmall_of_conv (cfg : Cfg)
    (hb : (_root_.Fmt.configBytes [cfg.pol, cfg.lay, cfg.KL]).size ≤ 2 ^ 32 - 144)
    (d : Slice.Shapes.Files) (a : AskedE) (he : d.ent.size + 16 ≤ 2 ^ 32 - 144)
    (hcv : convE
      (linkAtCfg smallRecordGround.q (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))
      (keyAt smallRecordGround.q.link.table (Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
        d.key).2.2 d.ent = some a)
    (hrun : runEntrySmall cfg a _root_.Fmt.oracle = true) :
    verifyEntryFilesSmall cfg d _root_.Run.oBits = true := by
  have hy : verifyEntrySmall cfg a _root_.Run.oBits = true := by
    rw [← gOf_oracle, ← runEntrySmall_eq]
    exact hrun
  have h0 := (askedFit_roots _ a ((verifyEntrySmall_iff cfg a _).1 hy).1).1
  rw [convE_first hcv] at h0
  refine (verifyEntryFilesSmall_iff cfg d _).2 ⟨a, ?_, hy⟩
  unfold readEntry
  rw [OnBytes.Slice.Shapes.dgOf_own₀ cfg hb]
  exact asked_of_conv smallRecordGround (Params.configurationDigest_size _) h0 he hcv

end OnBytes.K.Oracle

#print axioms OnBytes.K.Oracle.runEntryFilesFull_eq
#print axioms OnBytes.K.Oracle.runEntryFilesSmall_eq
#print axioms OnBytes.K.Oracle.convE_first
#print axioms OnBytes.K.Oracle.verifyEntryFilesFull_of_conv
#print axioms OnBytes.K.Oracle.verifyEntryFilesSmall_of_conv
