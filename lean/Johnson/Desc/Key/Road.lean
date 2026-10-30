-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/Road.lean: a key file's description from what the verifier program reads of the
public files, the layout file and the digest of the public files. Definitions only, all computable;
nothing is proved here.

The verifier program's planner (`Model.Verify.planned`) makes four steps: it reads the three public
files (`publicOf`), computes their digest, sizes and plans the seven chains (`chainsOf`) and builds
the links of a request's chain (`builtOf`). The first two call a concrete hash function: `publicOf`
holds the public tables against the digests in the parameter file. `madeAt` takes what these two
return as arguments, makes the other two steps, and lists the sendings of what they return
(`Johnson.G.sendsFrom`). So it returns a whole record of the type that `Johnson.G.OfPlan.madeOf`
returns, and its text names no hash function. (Of what its term reaches through other files this
file says nothing.)

Main names.
  madeAt X lay cfg: the planner's whole answer, and the sendings of the key's and of the proof's
    three chains each; the entry chain's list is made and not kept.
  descAt X lay cfg: the key file's description (`descriptionFromPlan`) at that record.

Limits. That X is what `publicOf` returns at the public files, that lay is the layout file among
them and that cfg is their digest is not asked here: they are the caller's to hand in. Of cfg the
description's own test on the plan refuses 32 zero bytes and nothing else. The planner sizes and
plans all seven chains, also those that a key file has not. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Key.Desc
import Johnson.G.SendsFrom

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

open OnBytes
open Johnson.G.OfPlan (Made)

/-- **The planner's whole answer and the sendings**, from what the program has read of the public
files, the layout file and the digest: the last two steps of `Model.Verify.planned`, in its order,
and the list of the sendings, of which the key's three and the proof's three are kept; the fourth,
the entry chain's, is made and dropped (the record has no field for it). -/
def madeAt (X : Model.Verify.Public) (lay cfg : ByteArray) : Except String Made := do
  let chains ← Model.Verify.chainsOf X (some lay) cfg
  let built ← Model.Verify.builtOf X chains
  match ← Johnson.G.sendsFrom chains.made with
  | [k0, k1, k2, _, p0, p1, p2] =>
    pure ⟨{ X := X, cfg := cfg, chains := chains, built := built }, (k0, k1, k2), (p0, p1, p2)⟩
  | _ => throw "the list of sendings has not seven chains (key 0 1 2, entry, proof 0 1 2)"

/-- **The key file's description**, from the same three. -/
def descAt (X : Model.Verify.Public) (lay cfg : ByteArray) : Except String (FileDescription Xi) :=
  (madeAt X lay cfg).bind fun m => descriptionFromPlan m

end VerifiableInference.Desc.Key
