-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Maker/Parsed.lean: the struct of record: what the prover's side hands to the Lean verifier
in the place of its three files (key file, entry file, proof file).

Purpose. An untrusted parser outside Lean (tools/parser/) turns the prover's three files into one
value of `Parsed`. The rule of this struct: it holds what is cut from the prover's files, and what
the proof type of `innerCompiledVerifier` (Johnson/Top/InnerCompiledVerifier.lean) has a place of its own for; nothing else
that the plan or a hash call gives; and no field twice: each table, each run of random bytes, each
list of seeds stands in one place. (Some quantities still stand more than once: whole paths repeat
each other and their neighbours' leaves; `bindRoot` and the seeds repeat what they are made of,
because the proof type has a place for them; the lists' lengths repeat the plan.)
States. No theorem. Five structures, and the way back to the two structs of the other parsed form:
  `Parsed.Table`, `Parsed.Round`, `Parsed.Chains`, `Parsed.Link`, `Parsed`: the struct.
  `Parsed.runW`: a chain's run value, made from the chain's label, its parameter bytes and 32 more
    bytes by the format's two calls (169, 172: Fmt/Rules4.lean), through the hash h as a letter;
    with the three refusals of the format's own `startChainW` (a label not below 2^32; bytes that
    are not 32; a value of 32 zero bytes).
  `Parsed.Chains.runsW`: the three run values of a key file's or a proof file's chains: the first
    and the third from the file's random bytes, the second from the binding tree's root.
  `Parsed.Chains.keyRunsW`, `Parsed.Chains.proofRunsW`, `Parsed.Link.runW`: the same at the labels
    and the parameter bytes of a key's, a proof's and a link's chains as OnBytes/Params/Chains.lean
    holds them: one source for both, the one from which the chains' first queries are spelt
    (`silentKey`, `silentProof`, OnBytes/Maker/Page/Silent.lean).
  `Parsed.rootsFit`: both tables' roots have 32 bytes.
  `Parsed.Chains.carrier`: the struct `Carrier.File` (OnBytes/Maker/Carrier.lean), filled of
    a `Chains`, a table, a copy's number, three run values, the data D and the binding tree's shape.
    A tree's chain and the number of places are laid from D and the shape, not read; the first
    chain's last round, the seal, which sends nothing, is laid bare.
  `Parsed.Link.leafP`: the struct `LeafP` (OnBytes/ShellOf/EntryParsed.lean), filled of a
    `Link`, the two tables and a run value.
Does not show: that any value of `Parsed` is accepted or refused by anything; that the parser can be
trusted (every value of `Parsed` is the prover's word); anything about the files that a value was
made from; anything about soundness. Which chains' parameters, data and shape are handed to these
functions is the caller's duty: they come from the user's public files and never from here.


-/
import OnBytes.Maker.CarrierTyping
import OnBytes.ShellOf.EntryParsed
import VerifiableInference.Statements

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker

open _root_.Fmt (Ext ItemValue)

/-- A stored table as its file names it, with its record's seeds. -/
structure Parsed.Table where
  /-- cut: bytes 8 to 39 of the file -/
  root : ByteArray
  /-- cut: the list behind the root -/
  answers : List Ext
  /-- the parser's hashing: seed by seed a point and a factor. The key's and the link's record have
  a place for them, and `innerCompiledVerifier` itself draws them again and compares (`outOfDomainSeedIs`,
  Johnson/TypedOracleCompiler/RecCompile/CmsAns.lean). As triples of words, like the answers: whoever lays a record
  maps `E.ofTriple` over both -/
  seeds : List (List Ext × Ext)

/-- A round: the items of its message, and its nonce. The nonce is a word, so it is below 2^64 by
its type: by the head of OnBytes/Maker/Page/Guard.lean a round's nonces n and n + 2^64 spell one
string. In the other struct a nonce is a natural number, bounded only in that the other form
gives it eight bytes. -/
structure Parsed.Round where
  /-- all items of the message in their order, the roots among them -/
  items : List ItemValue
  /-- 0 where the round has no proof of work -/
  nonce : UInt64

/-- The three chains of a key file or of a proof file. -/
structure Parsed.Chains where
  /-- cut: the 32 random bytes in front of rounds1 -/
  rand1 : ByteArray
  /-- the first chain's rounds WITHOUT ITS LAST, the seal, which sends nothing -/
  rounds1 : List Parsed.Round
  /-- the shared chain's rounds, all -/
  rounds2 : List Parsed.Round
  /-- cut: the 32 random bytes in front of rounds3 (in the format's names the second chain) -/
  rand3 : ByteArray
  /-- that chain's rounds, all -/
  rounds3 : List Parsed.Round
  /-- a tree's number among all roots that the three chains send, and its opened leaves -/
  trees : List (ℕ × List Carrier.Row)
  stored : List Carrier.Row
  /-- the parser's hashing; the proof string's `rtreq`, which the compiled verifier tests -/
  bindRoot : ByteArray
  place : ℕ
  slotSalt : ByteArray
  slotPath : List ByteArray

/-- The one chain of an entry file. -/
structure Parsed.Link where
  /-- cut: the 32 random bytes in front of the chain's first round -/
  rand : ByteArray
  rounds : List Parsed.Round
  trees : List (ℕ × List Carrier.Row)
  /-- the opened leaves of the first table -/
  stored0 : List Carrier.Row
  /-- the opened leaves of the further table -/
  stored1 : List Carrier.Row

/-- **What the prover's side fills.** -/
structure Parsed where
  /-- the key file's table -/
  first : Parsed.Table
  /-- the key file's chains -/
  key : Parsed.Chains
  /-- the entry file's table -/
  further : Parsed.Table
  /-- the entry file's chain -/
  link : Parsed.Link
  /-- the number in the proof file's head. (There it names an entry file; here, with one further
  table and one link, it picks nothing.) A word: the first chain's
  statement spells it modulo 2^64 (`Fmt.u64n`; `First.statement`, OnBytes/Params/Chains.lean). The
  file has four bytes for it: a value from 2^32 on is spelt by no proof file -/
  copy : UInt64
  /-- the proof file's chains -/
  proof : Parsed.Chains
  /-- the tokens behind prompt and output in the window: the padding of
  VerifiableInference/RequestOfTokens.lean; in docs/glossary.md's words the filler tokens -/
  pad : List VerifiableInference.Token

namespace Parsed

section
variable {m : Type → Type} [Monad m] (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)

/-- A chain's run value. lab: the chain's label; params: its parameter bytes, from the plan; rnd:
the file's 32 random bytes, or the binding tree's root at a shared chain. Nothing: what
`_root_.Fmt.startChainW` refuses. -/
def runW (lab : Nat) (params rnd : ByteArray) : m (Option ByteArray) :=
  if lab < 2 ^ 32 ∧ rnd.size = 32 then do
    let pd ← _root_.Fmt.paramsDigestW h params
    let run ← _root_.Fmt.runValueW h lab pd rnd
    pure (if _root_.Fmt.runOk run then some run else none)
  else pure none

/-- The three run values. l₁ l₂ l₃: the chains' labels; q₁ q₂ q₃: their parameter bytes. -/
def Chains.runsW (l₁ l₂ l₃ : Nat) (q₁ q₂ q₃ : ByteArray) (c : Chains) :
    m (Option (ByteArray × ByteArray × ByteArray)) := do
  let r₁ ← runW h l₁ q₁ c.rand1
  let r₂ ← runW h l₂ q₂ c.bindRoot
  let r₃ ← runW h l₃ q₃ c.rand3
  pure (r₁.bind fun a => r₂.bind fun b => r₃.map fun d => (a, b, d))

/-- The three run values of a key file's chains. k: from the user's public files. -/
def Chains.keyRunsW (k : Params.KeyChains) (c : Chains) :
    m (Option (ByteArray × ByteArray × ByteArray)) :=
  c.runsW h Params.labelOneTime Params.labelShared Params.labelSecond k.oneTime.given.bytes
    k.shared.given.bytes k.second.given.bytes

/-- The three run values of a proof file's chains. p: from the user's public files. -/
def Chains.proofRunsW (p : Params.ProofChains) (c : Chains) :
    m (Option (ByteArray × ByteArray × ByteArray)) :=
  c.runsW h Params.labelFirst Params.labelSharedProof Params.labelSecondProof p.first.given.bytes
    p.shared.given.bytes p.second.given.bytes

/-- The run value of an entry file's chain. p: from the user's public files. -/
def Link.runW (p : Params.Link) (l : Link) : m (Option ByteArray) :=
  Parsed.runW h Params.labelLink p.given.bytes l.rand

end

/-- Both tables' roots have 32 bytes. (rand1, rand3, rand and bindRoot are held to 32 bytes by
`runW`. A root among a round's items and a digest of a path or of slotPath are held to no length
here: the typings lay them by `bytesToDig`, which reads 256 bits whatever the length.) -/
def rootsFit (F : Parsed) : Bool := F.first.root.size == 32 && F.further.root.size == 32

/-- A round in the other structs. -/
def Round.carrier (x : Round) : Carrier.Round := ⟨x.items, x.nonce.toNat⟩

/-- The other struct of a key file or a proof file. t: the table in front (the key file's own; at
a proof file the entry file's). copy: 0 at a key file. r: the three run values. -/
def Chains.carrier (D : WholeD) (s : Params.LinBindingShape) (t : Table) (copy : ℕ)
    (r : ByteArray × ByteArray × ByteArray) (c : Chains) : Carrier.File where
  root := t.root
  answers := t.answers
  run1 := r.1
  copy := copy
  rounds1 := c.rounds1.map Round.carrier ++ [⟨[], 0⟩]
  run2 := r.2.1
  rounds2 := c.rounds2.map Round.carrier
  run3 := r.2.2
  rounds3 := c.rounds3.map Round.carrier
  trees := c.trees.map fun x => ⟨x.1, Carrier.senderOf D x.1, x.2⟩
  stored := c.stored
  bindRoot := c.bindRoot
  place := c.place
  places := 2 ^ s.logLeaves
  slotSalt := c.slotSalt
  slotPath := c.slotPath

/-- A row in the entry file's other struct. -/
def rowP (x : Carrier.Row) : ShellOf.EntryParsed.RowP := ⟨x.leaf, x.column, x.salt, x.path⟩

/-- The other struct of an entry file. run: the chain's run value. -/
def Link.leafP (first further : Table) (run : ByteArray) (l : Link) :
    ShellOf.EntryParsed.LeafP where
  root0 := first.root
  answers0 := first.answers.map E.ofTriple
  root := further.root
  answers := further.answers.map E.ofTriple
  run := run
  rounds := l.rounds.map fun x => (x.items, x.nonce.toNat)
  trees := l.trees.map fun x => (x.1, x.2.map rowP)
  stored0 := l.stored0.map rowP
  stored1 := l.stored1.map rowP

end Parsed

end OnBytes.Maker
