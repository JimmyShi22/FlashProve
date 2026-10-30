-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/VerifyChains.lean: the parameter bytes and the plans of the seven chains of a call's
files.

Every chain of a key, an entry and a proof begins with a hash call on its parameter bytes. These
bytes hold the plan of the chain's rounds, the codes and the shapes of the protocol. The C++
verifier makes them from the three configuration files and from what the sub-proofs' plans declare
(verifier/src/vf_segments.inc, buildLinksH; blocks/frame/configure.h). This file does the same, with
the planner of OnBytes/Params/Configure.lean:
 1. the sub-proofs declare their arrays (OnBytes/Model/StagesLinks.lean, declareLinks);
 2. the layout file says into which oracle messages the arrays go (OnBytes/Plan/ReqFrame.lean);
 3. the planner sizes the codes, and the links are tested against the sizes and the layout;
 4. the planner makes the plan of every chain with a bound on each round's error, tests its
    conditions, and writes out the parameter bytes;
 5. the bytes are read back, so that what the checks use is parsed out of the very bytes that the
    chains' reader hashes.
Nothing of a key, an entry, a request or a proof is read here.

Main definitions: `configuration`, `shapesOf`, `Chains`, `chainsOf`.
What is not claimed: no theorem is stated here. In particular, it is not shown that the planner's
bounds on the rounds' errors are true bounds.
-/
import OnBytes.Model.VerifyLinks
import OnBytes.Model.VerifySubproofs
import OnBytes.Params.Configure
import OnBytes.Params.Chains
import OnBytes.Plan.ReqFrame

namespace OnBytes.Model.Verify

open OnBytes.Model.Stages

/-- The digest of the three configuration files that every chain binds. The files come in the order
parameter file, layout file, scale file. -/
def configuration (pol layout KL : ByteArray) : ByteArray :=
  Params.configurationDigest [pol, layout, KL]

/-- Returns the links, with the names of the arrays that each reads, and what the planner takes from
the sub-proofs' plans and the layout file. The tests come in the order of the C++ routine
buildLinksH: the order and the number of the links, the declared arrays, the layout file, and then
the tests of `shapesWith` on the number of the links and on the layout of the weight table (the
committed matrix of weights). A folder without a layout file is refused at the point where the C++
verifier needs the file. -/
def shapesOf (X : Public) (layoutFile : Option ByteArray) :
    Except String (Array LinkH × Params.Shapes) := do
  let links ← linksOf X default
  headLast links
  linksCount links
  let (links, declared) ← declareLinks links X.NGr X.p4
  let file ←
    match layoutFile.bind Plan.layoutRead with
    | some f => pure f
    | none => throw "plan-layout"
  let (reqLinks, layout) ←
    match Plan.reqFrame declared file X.P.frame.answers with
    | some x => pure x
    | none => throw "plan-layout"
  pure (links, ← shapesWith X reqLinks layout (links.toList.map (·.gid)))

/-- The seven chains: what the planner has made, and the parameter bytes as read back. -/
structure Chains where
  /-- the sizes, the plans with their rounds' errors, and the parameter bytes -/
  made : Params.Configured
  /-- the key's three chains -/
  key : Params.KeyChains
  /-- the entry's chain -/
  link : Params.Link
  /-- the proof's three chains -/
  proof : Params.ProofChains

/-- The parameter bytes of a chain. -/
def Chains.bytes (c : Chains) : ChainName → ByteArray
  | .keyOneTime => c.made.keyOneTime
  | .keyShared => c.made.keyShared
  | .keySecond => c.made.keySecond
  | .link => c.made.entryLink
  | .proofFirst => c.made.first
  | .proofShared => c.made.shared
  | .proofSecond => c.made.second

/-- Makes the seven chains. cfg: the digest of the configuration files. The caller must have made X
and cfg from the same three files of which layoutFile is one.

The sizes are made first and the links are tested against them, as in the C++ routine buildLinksH.
The planner makes them once more on its way to the plans. It is given 0 as the requested bits: each
stage compares the bits of the call with its own file's plan. If the reader of the parameter bytes
does not accept the planner's bytes, that is a fault of this program.

The chains of the key, of the entry and of the proof each hold the shape of the weight table and
the digest of the configuration files. That the three files' chains hold the same ones is not
tested: all seven strings of bytes come out of one call of the planner. -/
def chainsOf (X : Public) (layoutFile : Option ByteArray) (cfg : ByteArray) :
    Except String Chains := do
  let (links, shapes) ← shapesOf X layoutFile
  let z ← Params.sized X.P.frame shapes
  linksFit links z.proof.codes z.proof.request shapes.layout z.proof.batch.shape.kCol
  let made ← Params.configure X.P.frame shapes cfg 0
  match Params.KeyChains.read made.keyOneTime made.keyShared made.keySecond,
      Params.Link.read made.entryLink,
      Params.ProofChains.read made.first made.shared made.second with
  | some key, some link, some proof =>
    pure { made := made, key := key, link := link, proof := proof }
  | _, _, _ => throw "internal-parameter-bytes-not-read"

/-- The names with which this file itself refuses. -/
def namesChains : List String := ["plan-layout", "internal-parameter-bytes-not-read"]

end OnBytes.Model.Verify
