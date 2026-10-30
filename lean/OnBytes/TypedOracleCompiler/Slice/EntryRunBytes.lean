-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryRunBytes.lean: the bytes' side of the run on an entry file.

Five byte strings (the three public files, the key file, the entry file) are taken either to the
stage that refuses, or to all that the verifier's side takes: the digest c, the parameters q, and
what the converter made (both tables, both lists of seeds, the chain as read).

The parameters come from a ground (typed values), not from the files. So the public files are tested
first (`stdEntry`: the parameter file's lines are the setting's; the three files are within the
hash's bound): else the pipeline would not look at the parameter file at all. Untrusted but for that
test. Nothing is marked noncomputable.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryConv
import OnBytes.TypedOracleCompiler.Slice.EntryDescOk
import OnBytes.Params.Std

set_option autoImplicit false

namespace TypedOracleCompiler.Slice

open OnBytes.Tie (EntryGround AskedE linkAtCfg keyAt)

/-- What the bytes' side hands on. -/
structure PrepE where
  /-- the digest of the three public files -/
  c : ByteArray
  /-- it has 32 bytes -/
  hc : c.size = 32
  /-- the parameters of the entry's chain at that digest -/
  q : OnBytes.Params.Link
  /-- what the converter made of key file and entry file -/
  a : AskedE

/-- THE BYTES' SIDE. lax = false: the converter is the port's own strict reading (`convE`); lax
= true: the lenient one (`convLax`). `.error` names the stage: "std" (the public files are not the
setting's), "converter" (the port's reading of the entry file refuses, or a table has no seeds). -/
def prepE (G : EntryGround) (z : OnBytes.Params.StdSize) (lax : Bool) (pol lay kl key ent : ByteArray) :
    Except String PrepE :=
  if OnBytes.Params.stdEntry z ⟨pol, lay, kl⟩ then
    match (if lax then convLax else convE) (linkAtCfg G.q
        (OnBytes.Params.configurationDigest [pol, lay, kl]))
        (keyAt G.q.link.table (OnBytes.Params.configurationDigest [pol, lay, kl]) key).2.2 ent with
    | none => .error "converter"
    | some a =>
      .ok ⟨OnBytes.Params.configurationDigest [pol, lay, kl], OnBytes.Params.configurationDigest_size _,
        linkAtCfg G.q (OnBytes.Params.configurationDigest [pol, lay, kl]), a⟩
  else .error "std"

/-- At the small example. -/
def prepSmall (lax : Bool) (pol lay kl key ent : ByteArray) : Except String PrepE :=
  prepE OnBytes.Tie.smallRecordGround OnBytes.Params.stdSmall lax pol lay kl key ent

end TypedOracleCompiler.Slice
