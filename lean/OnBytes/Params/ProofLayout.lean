-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/ProofLayout.lean: the layout of a proof file as one value, computed from the three
public files.

A proof file is, in this order (docs/format/FORMAT.md, R14.1, R14.2): the head of twelve bytes,
whose last four are the number of the stored copy on which the proof was made; the request's first
chain; the request's place in its batch's binding tree; the batch's shared chain; the request's
second chain. No part has a word for its own length. What a reader must know before it sees such a
file is public, and this file says it in one term, `proofLayout`: for each of the three chains its
description at blank content and what the dry run of its block leaves; the bytes of the parts that
are no chain; and, for the first chain, which link sends which oracle messages and which array lies
where in them.

The road. `Model.Verify.planned` makes and reads back the parameter bytes of all seven chains and
builds the links. The first chain's block is made at a request of no content and run dry. How it is
made (`firstBlockAt`) is written here a second time, after four steps in the text of
`Model.Verify.requestRun` and the first line of `Proof.check`; no law ties the two. So are the
labels of the shared and the second chain (after `Proof.tailPublic`) and the order of the two
strings that `First.describe` takes (after `Model.Verify.requestRun`); no law and no test ties these
either. What comes after the first chain is laid out as in a key file, under a proof's own two
labels (OnBytes/Params/KeyLayout.lean).

Which array lies where is not told anew: it is the two items "request's shape" and "layout" of the
first chain's parameter bytes, as `Params.First.read` has read them back (`ReqShape`, `ReqLayout`:
OnBytes/Params/Items.lean). They are hashed into the chain's first query. The read-offs here only
lay them out as rows: `messagesOf`, `arraysOf`. Where an element of an array lies in its oracle
message's table follows from the array's blocks by the rule in the comment of `LaidBlock`; that rule
is not said a second time here.

What is content and no layout: the table's root and answers, the number of the stored copy, the
request (its tokens, the covered positions, and the digests in the item "request"), the reply, and
what a key file's tail has. The table is blank, the number is 0, and the request is the request of
no content: tokens 0, the last position alone covered, the reply 0. The statement's item "request"
is what the program's `Proof.requestItem` makes of that request; it holds digests, so it is not
blank, but it has the length of every such item, 708 bytes (R15.1): the function returns nothing
else. The item "the request file's words" is that request's own bytes.

Main definitions: `requestWords`, `blankRequest`, `wordsBytes`, `firstBlockAt`, `ProofLayout`,
`proofLayoutAt`, `proofLayout`, `ProofLayout.parts`, `messagesOf`, `arraysOf`.
Not yet cut as OnBytes/Params/EntryLayout.lean is: the value holds the digest of the public files
and the parameter bytes, which are answers of the hash, beside what follows without a hash.
What is not claimed: no theorem is stated here or elsewhere on these definitions, and no test of
them lies in this tree: by Lean's evaluator one dry run of a proof's first block takes minutes. That
the dry run does not depend on the request is not proved.
A VALUE IS NO ADMISSION OF THE PUBLIC FILES: `Model.Verify.planned` takes no bits of a caller, and
the program's stages ask further tests before they say yes.

-/
import OnBytes.Params.KeyLayout

set_option autoImplicit false

namespace OnBytes.Params

open OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages

/-- The words of a request file for T tokens, as `Model.Head.stFromCall` reads them: the T tokens,
then the first covered position r and the position e after the last. All tokens are the same here.
-/
def requestWords (T : Nat) (token r e : Nat) : Array UInt32 :=
  Array.replicate T (UInt32.ofNat token) ++ #[UInt32.ofNat r, UInt32.ofNat e]

/-- The request of no content: tokens 0; the last position alone is covered. -/
def blankRequest (T : Nat) : Array UInt32 := requestWords T 0 (T - 1) T

/-- The words as a file's bytes, four each, the lowest first. -/
def wordsBytes (w : Array UInt32) : ByteArray :=
  w.foldl (fun b x => b ++ (Fmt.u64n x.toNat).extract 0 4) ByteArray.empty

/-- The block of a proof's first chain at the words of a request file and of a reply file. It is a
second writing of four steps in the text of `Model.Verify.requestRun` and of the first line of
`Proof.check`; no law ties the two. -/
def firstBlockAt (p : Verify.Planned) (request reply : Array UInt32) :
    Except String (Blk Proof.FirstEnd) := do
  let X := p.X
  let so ← Head.stFromCall request reply X.T
  let cov ← Head.coveredOf so X.T X.P.h.V
  let links := p.built.links.zipWith (fun b l => { b with run := l.run }) (← linksOf X cov)
  let c := p.chains.proof
  pure (Proof.firstBlock c.first (runLinksH links c.first X.layers.wsLay) (ofNat so.y))

/-- The layout of a proof file. -/
structure ProofLayout where
  /-- the three chains' parameter bytes as the program has read them back -/
  chains : ProofChains
  /-- the first chain -/
  first : ChainLayout
  /-- the place in the binding tree, the shared chain, the second chain -/
  tail : TailLayout

/-- The layout, made at the words of a request and the reply 0. Refused where `firstBlockAt` refuses
the request, and where a dry run, the request's item or a description is not made. The two labels
and the order of the two strings for `First.describe` are written here a second time; no law and no
test ties them to `Proof.tailPublic` and `Model.Verify.requestRun`. -/
def proofLayoutAt (x : ConfigurationFiles) (p : Verify.Planned) (request : Array UInt32) :
    Except String ProofLayout := do
  let c := p.chains.proof
  let block ← firstBlockAt p request #[0]
  let made : Option ProofLayout := do
    let (d1, first) ← chainDryWith block (Proof.firstStart c.first)
    let item ← Proof.requestItem x.policy x.scales (wordsBytes request)
    let spec1 ← c.first.describe (blankTableOf c.first.lin.fold.index) 0 item (wordsBytes request)
      d1.rounds
    let t ← tailLayoutOf c.shared c.second c.first.binding labelSharedProof labelSecondProof first
      (rootsSent d1.rounds)
    pure ⟨c, ⟨spec1, d1⟩, t⟩
  match made with
  | some L => pure L
  | none => throw "proof-parameters"

/-- **The layout of a proof file, from the three public files.** It is no admission of the files. -/
def proofLayout (x : ConfigurationFiles) : Except String ProofLayout := do
  let p ← plannedOf x
  proofLayoutAt x p (blankRequest p.X.T)

namespace ProofLayout

/-- The parts of a proof file, in the file's order (R14.1, R14.2). -/
def parts (L : ProofLayout) : List Fmt.FilePart :=
  [.outside "head: the kind" 4, .outside "head: the version" 4,
    .outside "head: the number of the stored copy" 4, .chain "first" L.first.spec] ++ L.tail.parts

end ProofLayout

/-- The oracle messages of the links, in the chain's order, off the item "request's shape": the
link, from 0; the message's number in its link; its shape; its class of leaves; in which of the
link's prover's messages it is sent; for how many later links its main rows are kept. -/
def messagesOf (f : First) : List (Nat × Nat × ReqMessage) :=
  f.shape.link.zipIdx.flatMap fun l => l.1.messages.zipIdx.map fun m => (l.2, m.2, m.1)

/-- The arrays of the links, off the item "layout": the link, from 0, and the array: its name, which
of its link's oracle messages holds it, its rows and columns, and the blocks in which it is laid
(`LaidBlock`). -/
def arraysOf (f : First) : List (Nat × ReqArray) :=
  f.layout.link.zipIdx.flatMap fun l => l.1.map fun a => (l.2, a)

end OnBytes.Params
