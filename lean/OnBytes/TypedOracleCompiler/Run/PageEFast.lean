-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageEFast.lean: a fast family of typed oracle functions for an entry's verifier,
made of the format's own hash (Lean's BLAKE2b): each typed query that the entry's page writes in the
format is answered by the call of `Fmt.formatHash` at the arguments of the query's row. Definitions that
compute.

Why. The typed verifier of an entry runs under a family of oracle functions. The family of the
theorems is "the page's": `readBlocks (EntryPage.implE …) g`: spell the typed query as a string, ask
the one oracle.
At the format's realised oracle that string's answer is a call of the format's hash (RowsE.lean,
RowsE3.lean, RowsH.lean). For an evaluation on a real file one wants the call itself, without the
strings. This file writes that family down.

 The answer is made first as bytes, then decoded, as the sibling's OnBytes/TypedOracleCompiler/Run/CodingFnThin.lean
 does (`famB`, `decP`, `famP`), for this reason: a digest is a function of the bit's number; where a
 definition's result has a function's type the compiler puts the whole body, the hash call with it,
 under that λ, and the hash is computed anew for every bit that is read (that file's head: "why,
 second", "what was tried").
 - `leafB`: a leaf query at a body that is a string: `Strings.rd2` reads number, place's word, index
 and bytes off the body; the typed salt's first 256 bits are the start, the rest goes behind the
 bytes;
 - `nodeB`: a vertex: the hash under 166, the configuration's digest as the start;
 - `msgL`, `nonceL`: a written round's message's bytes and nonce, read off a plain part of some
 round by recursion along the rounds' data; `msgE`, `nonceE`: the same behind the front;
 - `rowB`: a round's typed answer as K + 1 byte strings: typed block j is the format's block
 `blockNo work K j` of the round's row (`Fmt.block`); the last is the tail. All K + 1 are computed
 when the query is asked, each by a call of its own (so each call of the format is hashed twice);
 - `tailB`: K empty strings and a tail;
 - `linkB`: chain queries under the tag of Link: round 0, head `.f1 [r₀, r₁] (some x) salt`: the
 tail is the hash under 160 on the two tables' items; the K blocks of a verifier's message are empty
 (decoded: zeros) there;
   round k + 1, head `.f2 none ρ`: `rowB` at the written round k's kind and work;
 - `testB`: the seeds' chain's two queries;
 - `famFastB P K o q`: the answer to a typed query as an array of byte strings;
 - `famFastE P K` : Fam (typedOracleFamily 256 K (Le D early e)) := o, q ↦ the sibling's `decP` of `famFastB`.

Main definitions: `leafB`, `nodeB`, `rowB`, `linkB`, `testB`, `famFastB`, `famFastE`.

What is not said. Nothing is proved here. That it agrees with the page's family at the realised
oracle: where the query is one that the page writes and the call lies in the domain of the format's
hash, and, at round 0 of either chain, for the tail alone (the page's family has there K blocks
behind its escape; this one has zeros): that is not said in this library. At a query
that the page does not write in the format the two differ: this family tests nothing (no length, no
bound, not `Strings.ok2`, not the start of a stored leaf). How often the evaluator calls the hash is
a fact about a compiler, no theorem, and not counted here. A sealed round without work would
have its tail elsewhere at the page. Nothing on soundness. The sibling is a second
version of the library's soundness road, under OnBytes/TypedOracleCompiler/.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.EntryFb
import OnBytes.TypedOracleCompiler.StringsBoth
import OnBytes.TypedOracleCompiler.Run.CodingFnThin

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PageEFast
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.EntryFb
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-! ## A written round's message and nonce, off a plain part -/

/-- The message's bytes, from the roots' bytes and a plain part of some written round. -/
def msgL (C : _root_.Run.PQ.CK) : (ds : List PQ.RD) → List ByteArray → PQ.PBL C ds → ByteArray
  | [], _, z => z.elim
  | d :: _, rt, .inl (.inr p) => PQ.bytesL rt d.items (GPlain.old (b := d.entry.work) p)
  | _ :: _, _, .inl (.inl _) => ByteArray.empty
  | _ :: ds, rt, .inr z => msgL C ds rt z

/-- The nonce. -/
def nonceL (C : _root_.Run.PQ.CK) : (ds : List PQ.RD) → PQ.PBL C ds → ℕ
  | [], z => z.elim
  | d :: _, .inl (.inr p) => GPlain.nonce (b := d.entry.work) p
  | _ :: _, .inl (.inl _) => 0
  | _ :: ds, .inr z => nonceL C ds z

/-! ## A round's typed answer, as bytes -/

/-- A round's typed answer as K + 1 byte strings, from the format's own row of blocks; the last is
the tail. -/
def rowB (K lab : ℕ) (ρ : ByteArray) (i : ℕ) (msg : ByteArray) (kind : _root_.Fmt.Kind)
    (w nonce : ℕ) :
    Array ByteArray :=
  Array.ofFn (n := K + 1) fun j => _root_.Fmt.block lab ρ i msg kind w nonce (blockNo w K j)

/-- K empty strings and a tail. -/
def tailB (K : ℕ) (b : ByteArray) : Array ByteArray :=
  Array.ofFn (n := K + 1) fun j => if j.val = K then b else ByteArray.empty

variable {Sd : Type} {D : XD}
  {early : (List T3 × List T3) × Sd → (List T3 × List T3) × Sd} {e : _root_.Fmt.Entry}
  (P : PinsE D early e) (K : ℕ)

/-- A leaf query. -/
def leafB (q : LeafIn (Le D early e)) : ByteArray :=
  _root_.Fmt.formatHash (Strings.rd2 q.body).1 (Strings.rd2 q.body).2.1 (Strings.rd2 q.body).2.2.1
    (bitsToBytes (q.salt.take 256))
    ((Strings.rd2 q.body).2.2.2 ++ bitsToBytes (q.salt.drop 256))

/-- A vertex query. -/
def nodeB (q : Bits × Bits) : ByteArray :=
  _root_.Fmt.formatHash 166 0 0 P.cfg (bitsToBytes q.1 ++ bitsToBytes q.2)

/-- The message's bytes, off a plain part of the link's whole shape. -/
def msgE (rt : List ByteArray) : PlainPart (shE D early e) (annOf (Le D early e) .link) → ByteArray
  | .inl _ => ByteArray.empty
  | .inr z => msgL D.C D.ds rt z

/-- The nonce. -/
def nonceE : PlainPart (shE D early e) (annOf (Le D early e) .link) → ℕ
  | .inl _ => 0
  | .inr z => nonceL D.C D.ds z

/-- A chain query under the tag of Link. -/
def linkB (q : FbIn 256 (Le D early e) .link) : Array ByteArray :=
  match q.round, q.head with
  | 0, .f1 [r₀, r₁] (some x) salt =>
    tailB K (_root_.Fmt.formatHash 160 0 P.l _root_.Fmt.zero32
      (_root_.Fmt.firstBytes (digToBytes P.pd)
        (_root_.Fmt.tableItem "the first table" (digToBytes r₀) x.1.1 ++
          _root_.Fmt.tableItem "the further table" (digToBytes r₁) x.1.2)
        ByteArray.empty (runOf salt)))
  | k + 1, .f2 none ρ =>
    match D.ds[k]? with
    | some d =>
      rowB K P.l (bitsToBytes ρ) (k + 1) (msgE (q.rt.map digToBytes) q.plain) d.kind d.entry.work
        (nonceE q.plain)
    | none => #[]
  | _, _ => #[]

/-- A chain query under the seeds' tag. -/
def testB (q : FbIn 256 (Le D early e) .test) : Array ByteArray :=
  match q.round, q.head with
  | 0, .f1 [cm] none [] =>
    tailB K (_root_.Fmt.formatHash 160 0 _root_.Fmt.recordLabel _root_.Fmt.zero32
      (_root_.Fmt.firstBytes _root_.Fmt.zero32 (digToBytes cm ++ P.rest) ByteArray.empty none))
  | 1, .f2 none ρ => rowB K _root_.Fmt.recordLabel (bitsToBytes ρ) 1 ByteArray.empty .seeds 0 0
  | _, _ => #[]

/-- The answer to a typed query as bytes: one string for a leaf or a vertex, K + 1 for a chain query
under the link's or the seeds' tag, none elsewhere. -/
def famFastB : (o : (typedOracleFamily 256 K (Le D early e)).ι) → (typedOracleFamily 256 K (Le D early e)).Dom o →
    Array ByteArray
  | .leaf, q => #[leafB q]
  | .node, q => #[nodeB P q]
  | .fb .link, q => linkB P K q
  | .fb .test, q => testB P K q
  | _, _ => #[]

/-- The fast family: the bytes, decoded by the sibling's `decP`. Zeros where there are no bytes. -/
def famFastE : Fam (typedOracleFamily 256 K (Le D early e)) :=
  fun o q => decP (fun _ : Unit => Le D early e) K o (famFastB P K o q)

end TypedOracleCompiler.Run.PageEFast
