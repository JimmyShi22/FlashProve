-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CodingFn.lean: from a typed query of the compiled verifier, and the number of a block of its
answer, to the hash call of the programs' format. (The hash: `Fmt.formatHash`, Fmt/Rules23.lean: BLAKE2b, no
key, the start in its parameter block, of 16-byte label and bytes.)

Functions only: definitions that compute; no inverse, no law, no theorem (but for three theorems on
`castTag`).
The format page (docs/format/FORMAT.md, which comes with the programs): this file has not been held
against the page as it ships, and may differ from it. What a leaf's label holds beyond the tree's
number is left to the data (`PageD.leaf`). This file may differ at R2.3, R2.4, R3.1, R7.3 and R7.4
for instance. The run functions that use it agree with the programs' files that the tests hold
(Run/M2EngineT1.lean and the files beside it), which have not been held against the page as it
ships either.



The compiled verifier (`verifyOneProtocol`, Compile/Batch/Verifier.lean) asks typed oracles
(Compile/Batch/Oracles.lean). At a protocol with local rounds only these are: one chain query a
round, leaf queries, node queries. The protocol's tag t (test, link, or the online protocol) is a
parameter. The data stand at one tag, and with them every function here; the tag of a function is
read off its data. The programs' format makes every hash as one call with six fields: half, number,
tree, index, start, bytes (`OQ`, `oStr`, Fmt/Rules23.lean).

Main names:
  `PageD L t`, the data. Its fields:
    `label`: the chain's label.
    `kind`, `work`: the kind's number and the bits of work (proof of work) of round i, by the
      chain's plan.
    `stm`: the statement's bytes.
    `msg i rt pl`: the prover's message of round i as bytes: the root, if any, and the items of the
      plain part, in the order sent (without the nonce).
    `nonce i pl`: the nonce of round i (a component of the typed plain part; 0 where the round has
      no work).
    `leaf s`: three values of a symbol with its position. First, what stands above the leaves'
      number in the label's first word, as one number: the tree's number + 2^16 * (the words of the
      column) + 2^40 * (the words of the file's salt) (in the edition that this file follows,
      R2.1 to R2.4, R7.3, R7.4).
      Second, 2^depth + position. Third, the column's bytes with
      their fill. The fill hangs on the length of the file's salt: so this datum fixes that length;
      a typed salt of another length would get a wrong fill; the verifier's strict format fixes the
      length.
    `cfg` is the start of every vertex. It is a constant of the instance, the configuration's digest
      (R3.1, R7.7). Its default, 32 zero bytes, is no configuration's digest: a `PageD` that is
      written without this field has vertices that start from zeros.
  `fbCall`, `leafCall`, `nodeCallC`, the map:
    round 0: the protocol has a trivial round 0. Its query (first format: a list of digests, the
      statement, a salt) is the call that makes the chain's first value. The one digest of the list
      stands for the parameters' digest, the salt for the run's value (an empty salt: a chain
      without random bytes); the record is empty. (The parameters' digest, the record and the run's
      value are the arguments pd, record, run of `Fmt.firstBytes`, Fmt/Rules4.lean.) That call has
      one block: the chain value. The other blocks of round 0 have no call.
    round i > 0: typed round i is the format's round i: the chain's label stands in the tree's place
      (R3.1, R5.2); start := the chain value before; bytes := the message, the word of (kind, work,
      number of the call), the word of the nonce. Block b of the format's row is half (b mod 2) of
      call (b div 2).
    `blockNo`: which block of the row a typed block is. A typed answer is K blocks of verifier
      message and then the chain value. Without work: chain value ↦ 0, message block k ↦ k + 1. With
      work: message block 0, which gives the test bits, ↦ 0; chain value ↦ 1; message block k ≥ 1 ↦
      k + 1.
    a leaf: it has a call if its body is a symbol under the data's own tag (`castTag`: a leaf's body
      names its tag). The first 256 bits of the typed salt stand for the run's value (the call's
      start); the rest is the file's salt.
    a node: the vertices' number, tree 0, index 0, start cfg; bytes: the two digests (`nodeCallC`;
      `nodeCall`: the same without a start).
    all else: no call (none): among it the chain queries and the leaves of the two other tags.
  `famOf O D K`: what has no call is answered by zeros.

Notation:
  `160`: the number under which the format makes a chain's first value (`Fmt.firstValueW`,
    Fmt/Rules4.lean);
  `162`: the number under which the format hashes a round's query (`Fmt.callW`, Fmt/Rules5.lean);
  `164`: the number under which the leaves of a run's tree are hashed (`Fmt.leafNo`,
    Fmt/Rules7.lean);
  `166`: the number under which the format hashes an inner vertex (`Fmt.vertexW`);
  `L`: an interface (`BatchProtocol`, Iop/Batch.lean);
  `D`: the data (`PageD L t`);
  `O`: a function on the format's strings.

Limits: on the comparison with the format page see "The format page" above. What is not tested here:
whether a query fits the plan (lengths of chain values, digests and salts; a root where the plan has
one; a plain part of the round that the query names). A bit string that is no whole number of bytes
is filled up with zeros. So this map is not injective as it stands; the encoding of the queries with
its inverse is another file's (Run/CodingPage.lean).
One tag at a time: a family for the three protocols at once (three chains with three labels, leaves
told apart) is not here.
This file does not say: that the verifier's parser puts the parameters' digest and the run's value
where this map reads them; anything on soundness or privacy.

Terms: lean/GLOSSARY.md.
-/
import Run.CodingBits
import Fmt.Rules23
import Compile.Batch.Oracles

namespace Run
open Compile Compile.Batch Iop Rom

variable {I X : Type}

/-- A value whose type depends on a tag, read at another tag: `some` of the value if the two tags
are equal, else `none`. -/
def castTag {F : Tag → Type} (t t' : Tag) (x : F t') : Option (F t) :=
  if h : t' = t then some (h ▸ x) else none

theorem castTag_self {F : Tag → Type} (t : Tag) (x : F t) : castTag (F := F) t t x = some x :=
  dif_pos rfl

theorem castTag_ne {F : Tag → Type} {t t' : Tag} (h : t' ≠ t) (x : F t') :
    castTag (F := F) t t' x = none := dif_neg h

/-- What is read is the value itself, as a pair of tag and value. -/
theorem castTag_some {F : Tag → Type} {t t' : Tag} {x : F t'} {y : F t}
    (h : castTag (F := F) t t' x = some y) :
    (⟨t', x⟩ : Σ t, F t) = ⟨t, y⟩ := by
  unfold castTag at h
  by_cases ht : t' = t
  · subst ht
    rw [dif_pos rfl] at h
    rw [← Option.some.inj h]
  · rw [dif_neg ht] at h
    cases h

/-- The data for the chain of the protocol under the tag t (where no tag is written: "test"): what
the format hashes and a typed query does not hold, or holds in typed form. -/
structure PageD (L : BatchProtocol I X) (t : Tag := .test) where
  label : Nat
  kind  : Nat → Nat
  work  : Nat → Nat
  stm   : Option X → ByteArray
  msg   : Nat → Option ByteArray → PlainPart (shapeOf L t) (annOf L t) → ByteArray
  nonce : Nat → PlainPart (shapeOf L t) (annOf L t) → Nat
  leaf  : SymAny (shapeOf L t) → Nat × Nat × ByteArray
  /-- The start of every vertex: a constant of the instance (the configuration's digest); 32 zero
  bytes: a vertex without a start. -/
  cfg   : ByteArray := _root_.Fmt.zero32

/-- Which block of the format's row a typed block is; w: the round's bits of work; typed block K is
the chain value. -/
def blockNo (w K : Nat) (j : Fin (K + 1)) : Nat :=
  if j.val = K then (if w = 0 then 0 else 1)
  else if w = 0 then j.val + 1
  else if j.val = 0 then 0 else j.val + 1

variable {L : BatchProtocol I X} {t : Tag}

/-- The bytes of the call that makes a chain's first value. -/
def firstBytes (pd st : ByteArray) (salt : Bits) : ByteArray :=
  pd ++ _root_.Fmt.u64n st.size ++ st ++ _root_.Fmt.u64n 0 ++
    (if salt.isEmpty then _root_.Fmt.u64n 0 else _root_.Fmt.u64n 1 ++ bitsToBytes salt)

/-- The bytes of call c of a round. -/
def roundBytes (msg : ByteArray) (kind w c nonce : Nat) : ByteArray :=
  msg ++ _root_.Fmt.u64n (kind + 256 * w + 65536 * c) ++ _root_.Fmt.u64n nonce

/-- The call of a chain query and a block of its answer, if there is one. -/
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

/-- The call of a leaf query, if there is one. -/
def leafCall (D : PageD L t) (q : LeafIn L) : Option _root_.Fmt.OQ :=
  match q.body with
  | some (.inr ⟨t', s⟩) =>
      (castTag (F := fun t => SymAny (shapeOf L t)) t t' s).map fun s =>
        ⟨0, 164, (D.leaf s).1, (D.leaf s).2.1, bitsToBytes (q.salt.take 256),
          (D.leaf s).2.2 ++ bitsToBytes (q.salt.drop 256)⟩
  | _ => none

/-- The call of a node query, without a start. -/
def nodeCall (q : Bits × Bits) : Option _root_.Fmt.OQ :=
  some ⟨0, 166, 0, 0, _root_.Fmt.zero32, bitsToBytes q.1 ++ bitsToBytes q.2⟩

/-- The call of a node query, with the start of the vertices. -/
def nodeCallC (cfg : ByteArray) (q : Bits × Bits) : Option _root_.Fmt.OQ :=
  some ⟨0, 166, 0, 0, cfg, bitsToBytes q.1 ++ bitsToBytes q.2⟩

/-- The format's string of a call. -/
def strOf (c : _root_.Fmt.OQ) : ByteArray :=
  _root_.Fmt.oStr c.half c.number c.tree c.index c.start c.bytes

/-- The answer of O at a call; zeros where there is none. -/
def ansOf (O : ByteArray → ByteArray) : Option _root_.Fmt.OQ → Dig 256
  | some c => bytesToDig (O (strOf c))
  | none => fun _ => false

/-- The typed oracle functions that a function on the format's strings induces. -/
def famOf (O : ByteArray → ByteArray) (D : PageD L t) (K : Nat) : Fam (spec 256 K L)
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

#guard (List.range 4).map (fun j => blockNo 0 3 (Fin.ofNat 4 j)) == [1, 2, 3, 0]
#guard (List.range 4).map (fun j => blockNo 8 3 (Fin.ofNat 4 j)) == [0, 2, 3, 1]
#guard (nodeCall (bytesToBits (_root_.Fmt.pattern 32), bytesToBits (_root_.Fmt.pattern 32 5 1))).map (fun c => (strOf c).size) == some 145
-- the page's known answer of a vertex (of an edition that is not the one that ships): start
-- pattern(32), bytes pattern(64)
#guard _root_.Fmt.hex (digToBytes (ansOf _root_.Fmt.oracle (nodeCallC (_root_.Fmt.pattern 32) (bytesToBits ((_root_.Fmt.pattern 64).extract 0 32), bytesToBits ((_root_.Fmt.pattern 64).extract 32 64))))) == "af2a19aa20cc89e1e740e2ec4d34a275eae7bff385fcfc64e3064ccd7cc1b3f8"

end Run
