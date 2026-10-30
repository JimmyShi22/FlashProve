-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/CodingFn.lean.
In OnBytes/TypedOracleCompiler: where the head below says "msg i rt pl … the root, if any" read "the list of the
round's roots". The spelling of a message (Run/PlanQSpell.lean: bytesL) is a total function: for too
few roots it writes nothing at the item "root", surplus roots it drops: so fbCall sends typed
queries that differ in rt alone to one string; the code that is proved one-to-one refuses such lists
(toRoots), and the verifier never asks them (takeRt).

Run/CodingFn.lean: from a typed query of the compiled verifier, and the number of a block of its
answer, to the hash call of the programs' format. Functions only: definitions that compute; no
inverse, no law, no theorem. The format page (FORMAT.md, which comes with the programs): this file
has not been held against the page as it ships, and may differ from it, for instance at R2.3, R2.4,
R3.1, R7.3 and R7.4. What a leaf's label holds more is the data's matter: PageD.leaf.
The run functions that use it agree with the programs' files that the tests hold
(Run/M2EngineT1.lean and the files beside it), which have not been held against the page as it
ships either.
The compiled verifier (Compile/Batch/Verifier.lean: verifyOneProtocol) asks typed oracles
(Compile/Batch/Oracles.lean). At a protocol with local rounds only these are: one chain query a
round, leaf queries, node queries. The protocol's tag t (test, link, or the online protocol) is a
parameter: the data, and with them every function here, stand at one tag; where no tag is written it
is "test" (a default of the record PageD), and the tag of a function is read off its data. The
programs' format makes every hash as one call with six fields: half, number, tree, index, start,
bytes (Fmt/Rules23.lean: OQ, oStr). Here each such typed query is sent to its call.
The data (PageD L t): what the format hashes and a typed query does not hold, or holds in typed
form:
    label  the chain's label
    kind, work  the kind's number and the bits of work of round i, by the chain's plan
    stm  the statement's bytes
    msg i rt pl  the prover's message of round i as bytes: the root, if any, and the items of the
        plain part, in the order sent (without the nonce)
    nonce i pl  the nonce of round i (a component of the typed plain part; 0 where the round has no
        work)
    leaf s  of a symbol with its position: what stands above the leaves' number in the label's first
        word, as one number (R2.1 to R2.4, R7.3, R7.4, as this file reads them: the
        tree's number + 2^16 (the words of the column) + 2^40 (the words of the file's salt));
        2^depth + position; the column's bytes with
        their fill (the fill hangs on the length of the file's salt: so this datum fixes that
        length; a typed salt of another length would get a wrong fill; the verifier's strict format
        fixes the length)
    cfg  the start of every vertex: a constant of the instance, the configuration's digest. (R3.1,
        R7.7). Its default, 32 zero bytes, is no configuration's digest: a literal that leaves it
        out has vertices that start from zeros
The map.
    round 0  the protocol has a trivial round 0. Its query (first format: a list of digests, the
        statement, a salt) is the call that makes the chain's first value: the one digest of the
        list stands for the parameters' digest, the salt for the run's value (an empty salt: a chain
        without random bytes); the record is empty. That call has one block: the chain value. The
        other blocks of round 0 have no call.
    round i > 0  typed round i is the format's round i: the chain's label stands in the tree's place
        (R3.1, R5.2); start := the chain value before; bytes := the message, the word of (kind,
        work, number of the call), the word of the nonce. Block b of the format's row is half (b mod
        2) of call (b div 2).
    blockNo  which block of the row a typed block is. A typed answer is K blocks of verifier message
        and then the chain value. Without work: chain value ↦ 0, message block k ↦ k + 1. With work:
        message block 0, which gives the test bits, ↦ 0; chain value ↦ 1; message block k ≥ 1 ↦ k +
        1.
    a leaf  of a symbol under the data's own tag (castTag: a leaf's body names its tag). The first
        256 bits of the typed salt stand for the run's value (the call's start); the rest is the
        file's salt.
    a node  the vertices' number, tree 0, index 0, start cfg; bytes: the two digests (nodeCallC;
        nodeCall: the same without a start).
    all else  no call (none): among it the chain queries and the leaves of the two other tags.
famOf O D: the family of typed oracle functions that a function O on the format's strings induces:
what has no call is answered by zeros.
What is not tested here: whether a query fits the plan (lengths of chain values, digests and salts;
a root where the plan has one; a plain part of the round that the query names). A bit string that is
no whole number of bytes is filled up with zeros. So this map is not injective as it stands; the
encoding of the queries with its inverse is another file's (Run/CodingPage.lean).
One tag at a time: a family for the three protocols at once (three chains with three labels, leaves
told apart) is not here.
What is not said. That the verifier's parser puts the parameters' digest and the run's value where
this map reads them. Anything on soundness or privacy.

Terms: lean/GLOSSARY.md.

-/
import Run.CodingFn
import Run.CodingBits
import Fmt.Rules23
import OnBytes.TypedOracleCompiler.Compile.Batch.Oracles

namespace TypedOracleCompiler.Run
open _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol
open _root_.Run

variable {I X : Type}

/-- What the format hashes and a typed query does not hold, or holds in typed form, for the chain of
the protocol under the tag t (where no tag is written: "test"). -/
structure PageD (L : BatchProtocolWithLeafBody I X) (t : Tag := .test) where
  label : Nat
  kind  : Nat → Nat
  work  : Nat → Nat
  stm   : Option X → ByteArray
  msg   : Nat → List ByteArray → PlainPart (shapeOf L t) (annOf L t) → ByteArray
  nonce : Nat → PlainPart (shapeOf L t) (annOf L t) → Nat
  /-- TWO: of a leaf's BODY (in the library: of a symbol with its position; leafCall tests the tag
  there: here that test is this function's own); none: no call -/
  leaf  : L.Bd → Option (Nat × Nat × ByteArray)
  /-- the start of every vertex: a constant of the instance (the configuration's digest); 32 zero
  bytes: a vertex without a start -/
  cfg   : ByteArray := _root_.Fmt.zero32

variable {L : BatchProtocolWithLeafBody I X} {t : Tag}

/-- A chain query and a block of its answer. -/
def fbCall (D : PageD L t) (K : Nat) (q : FbIn 256 L t) (j : Fin (K + 1)) : Option _root_.Fmt.OQ :=
  match q.round, q.head with
  | 0, .f1 [pd] x salt =>
      if j.val = K then
        some ⟨0, 160, 0, D.label, _root_.Fmt.zero32, firstBytes (digToBytes pd) (D.stm x) salt⟩
      else none
  | i + 1, .f2 none ρ =>
      let b := blockNo (D.work (i + 1)) K j
      some ⟨UInt8.ofNat (b % 2),
        162, D.label, i + 1, bitsToBytes ρ,
        roundBytes (D.msg (i + 1) (q.rt.map digToBytes) q.plain) (D.kind (i + 1)) (D.work (i + 1))
          (b / 2) (D.nonce (i + 1) q.plain)⟩
  | _, _ => none

/-- A leaf query. -/
def leafCall (D : PageD L t) (q : LeafIn L) : Option _root_.Fmt.OQ :=
  (D.leaf q.body).map fun z =>
    ⟨0, 164, z.1, z.2.1, bitsToBytes (q.salt.take 256), z.2.2 ++ bitsToBytes (q.salt.drop 256)⟩

/-- The typed oracle functions that a function on the format's strings induces. -/
def famOf (O : ByteArray → ByteArray) (D : PageD L t) (K : Nat) : Fam (typedOracleFamily 256 K L)
  | .leaf, q => ansOf O (leafCall D q)
  | .node, q => ansOf O (nodeCallC D.cfg q)
  | .fb t', q =>
      match castTag (F := fun t => FbIn 256 L t) t t' q with
      | some q => (fun k => ansOf O (fbCall D K q k.castSucc), ansOf O (fbCall D K q (Fin.last K)))
      | none => (fun _ _ => false, fun _ => false)
  | .fbw _ _, _ => (fun _ _ => false, fun _ => false)
  | .rleaf, _ => fun _ => false
  | .rnode, _ => fun _ => false
  | .g _, _ => fun _ => false
  | .ann, _ => ()
  | .other, _ => fun _ => false

-- the page's known answer of a vertex: start pattern(32), bytes pattern(64)

end TypedOracleCompiler.Run
