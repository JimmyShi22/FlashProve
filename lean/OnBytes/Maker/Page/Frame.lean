-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/Frame.lean: from a typed query of the compiled verifier of a key file, an entry
file or a proof file, and the number of a block of its answer, to the string that the programs'
format hashes there; and the family of typed oracle functions that a function on these strings
induces. Definitions alone: functions that compute; no inverse, no law, no theorem.

WHAT KIND OF OBJECT THIS IS. `gJ P O` is a FUNCTION of the typed query: `O` at the query's string.
It is meant to carry a yes of the programs' verifier, which hashes strings, to a yes of the typed
verifier, which asks typed oracles; nothing in this file does so. IT IS NO ENCODING IN THE SENSE OF
THE SOUNDNESS THEOREM (`Rom.OracleCoding`, Rom/Family.lean: one to one, and onto all strings): the labels
are letters of the data here, and nothing in this file asks that the key file's differ from the
proof file's; the vertices' and the request tree's calls bear no tag at all. More causes of
one string for two queries: the roots and the plain part of a query for the slot value, the roots at
the three silent rounds, and whatever of a first query's fields the data's `stm₁`, `stm₂`, `stm₃` do
not read. So this file does nothing for the theorem's passage from typed oracles to one hash
function. The data may hold digests that are made by the same hash (`pd₁`, `pd₂`, `pd₃`, `cfg`):
then the string hangs on `O` too.

After Run/CodingFn.lean and OnBytes/TypedOracleCompiler/Run/CodingFn.lean, which do the same for one chain under one
tag (`PageD`, `fbCall`, `famOf`). The format makes every hash as one call with six fields: half,
number, tree, index, start, bytes (`Fmt.OQ`, `Fmt.oStr`, Fmt/Rules23.lean).

THE TYPED ROUNDS OF A FILE WITH THREE JOINED CHAINS: 0 the front round | 1 .. n₁ the first chain's
rounds without its seal | J = n₁ + 1 the joining round | J + 1 .. J + n₂ the second chain's rounds,
its seal the last | J3 = J + n₂ + 1 the seam | J3 + 1 .. J3 + n₃ the third chain's rounds.
  fb, round 0, head f1, the tail's block       160, tree 0, index lab₁, start zeros
  fb, rounds 1 .. n₁, head f2 without x        162, tree lab₁, index i
  g, round J                                   162, tree lab₁, index J: no message, kind 6, no work:
                                               block 1 of that row
  fb, round J, head f4, the tail's block       160, tree 0, index lab₂
  fb, rounds J + 1 .. J + n₂, head f5          162, tree lab₂, index i - J; at the last of them the
                                               typed tail is the row's block 1
  fb, round J3, head f3, the tail's block      160, tree 0, index lab₃
  fb, rounds J3 + 1 .. J3 + n₃, head f2        162, tree lab₃, index i - J3
  rleaf                                        173, index read off the typed string, start cfg
  rnode                                        178, tree 0, index 0, start cfg
  node                                         166, tree 0, index 0, start cfg
  leaf                                         the datum `leaf`
Block b of a row is half (b mod 2) of call (b div 2).

What the file contains.
  `PBt L t`: the plain parts of the protocol under the tag t.
  `FileJ L t`: what the format hashes in a file's three chains and a typed query does not hold, or
    holds in typed form.
  `FileJ.J`, `FileJ.J3`, `rowCall`, `firstCall`, `fbCallJ`, `gCallJ`: a chain query's call.
  `rleafCall`, `rnodeCall`: the request tree's.
  `PageJ L K`: the data of the page: the configuration's digest, the key file's and the proof file's
    data, the bytes of a request leaf's salt, the leaves' calls; and four partial spellings that are
    taken as they are from elsewhere: the entry file's chain queries, chain queries under the key
    file's tag (meant: the seeds' two; the type does not bound them), leaves (likewise not bounded),
    and strings of the spare oracle.
  `blocksJ`: the number of blocks of an answer.
  `callJ`: the call of a typed query and a block, at the rows above.
  `codeJ`: the string of a typed query and a block. Where one of the four partial spellings writes,
    the string is that one's.
  `ansJ`, `gJ`: the family. What has no string is answered by zeros: so the typed verifier under
    `gJ P O` is another verifier than the programs': where a query has no string its answer is a
    constant; neither follows from the other by anything in this file. A term for statements, no
    verifier to run. A PROVER'S STRING CAN REACH A QUERY WITHOUT A STRING: the request tree's leaf,
    at another length of the field `rsalt`. So no verdict is taken by `(verifyOneProtocol ..).det (gJ P O)`:
    the run that refuses at such a query is `verifyGuard` (OnBytes/Maker/Page/GuardVerify.lean).

What is not tested here: whether a query fits the plan (lengths of chain values, digests and salts;
as many roots as the plan has; a plain part of the round that the query names). A bit string that is
no whole number of bytes is filled up with zeros. A query of the format f2 that holds an instance
has no string.

What is not claimed. That the strings are those that the programs hash at a file. That a call's
arguments lie in the domain of the format's hash (`Fmt.hDom`). That data exist at any interface.
Nothing on any hash. Nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Run.CodingFn

set_option autoImplicit false

namespace OnBytes.Maker.Page

open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol
open _root_.Run

variable {I X : Type}

/-- The plain parts of the protocol under the tag t. -/
abbrev PBt (L : BatchProtocolWithLeafBody I X) (t : Tag) : Type := PlainPart (shapeOf L t) (annOf L t)

/-- **What the format hashes in a file's three chains and a typed query does not hold, or holds in
typed form.** -/
structure FileJ (L : BatchProtocolWithLeafBody I X) (t : Tag) where
  /-- the three chains' labels -/
  lab₁ : ℕ
  lab₂ : ℕ
  lab₃ : ℕ
  /-- the digests of the three chains' parameter bytes -/
  pd₁ : ByteArray
  pd₂ : ByteArray
  pd₃ : ByteArray
  /-- the first chain's rounds, less its seal -/
  n₁ : ℕ
  /-- the second chain's rounds, with its seal -/
  n₂ : ℕ
  /-- the third chain's rounds -/
  n₃ : ℕ
  /-- the kind's number, by the typed round -/
  kind : ℕ → ℕ
  /-- the bits of work, by the typed round -/
  work : ℕ → ℕ
  /-- the prover's message of the typed round i as bytes: the roots and the items of the plain part,
  in the order sent, without the nonce -/
  msg : ℕ → List ByteArray → PBt L t → ByteArray
  /-- the nonce of the typed round i -/
  nonce : ℕ → PBt L t → ℕ
  /-- the first chain's statement: from the outer roots, the instance and the front round's plain
  part -/
  stm₁ : List (Dig 256) → Option X → PBt L t → ByteArray
  /-- the second chain's statement: from the outer roots, the request root and the joining round's
  shared plain part -/
  stm₂ : List (Dig 256) → Bits → PBt L t → ByteArray
  /-- the second chain's run value: from that plain part -/
  run₂ : PBt L t → Bits
  /-- the third chain's statement: from the second chain's seal, the first chain's seal and the
  seam's plain part -/
  stm₃ : Bits → Bits → PBt L t → ByteArray
  /-- the third chain's run value: from that plain part -/
  run₃ : PBt L t → Bits

variable {L : BatchProtocolWithLeafBody I X} {t : Tag}

/-- The typed round of the joining round. -/
def FileJ.J (F : FileJ L t) : ℕ := F.n₁ + 1

/-- The typed round of the seam. -/
def FileJ.J3 (F : FileJ L t) : ℕ := F.n₁ + F.n₂ + 2

/-- The call of the typed block j of a round's row. ow: what orders the blocks (`blockNo`,
Run/CodingFn.lean): 0: the typed tail is the row's block 0; else it is block 1. -/
def rowCall (lab idx : ℕ) (ρ : Bits) (msg : ByteArray) (kind work nonce ow K : ℕ)
    (j : Fin (K + 1)) : Fmt.OQ :=
  ⟨UInt8.ofNat (blockNo ow K j % 2), 162, lab, idx, bitsToBytes ρ,
    roundBytes msg kind work (blockNo ow K j / 2) nonce⟩

/-- The call that makes a chain's first value. -/
def firstCall (lab : ℕ) (pd stm : ByteArray) (run : Bits) : Fmt.OQ :=
  ⟨0, 160, 0, lab, Fmt.zero32, firstBytes pd stm run⟩

/-- **A chain query and a block of its answer.** -/
def fbCallJ (F : FileJ L t) (K : ℕ) (q : FbIn 256 L t) (j : Fin (K + 1)) : Option Fmt.OQ :=
  match q.head with
  | .f1 cms x salt =>
    if q.round = 0 ∧ j.val = K then
      some (firstCall F.lab₁ F.pd₁ (F.stm₁ cms x q.plain) salt)
    else none
  | .f2 none ρ =>
    if 1 ≤ q.round ∧ q.round ≤ F.n₁ then
      some (rowCall F.lab₁ q.round ρ (F.msg q.round (q.rt.map digToBytes) q.plain)
        (F.kind q.round) (F.work q.round) (F.nonce q.round q.plain)
        (F.work q.round) K j)
    else if F.J3 + 1 ≤ q.round ∧ q.round ≤ F.J3 + F.n₃ then
      some (rowCall F.lab₃ (q.round - F.J3) ρ (F.msg q.round (q.rt.map digToBytes) q.plain)
        (F.kind q.round) (F.work q.round) (F.nonce q.round q.plain)
        (F.work q.round) K j)
    else none
  | .f2 (some _) _ => none
  | .f4 cms rtreq =>
    if q.round = F.J ∧ j.val = K then
      some (firstCall F.lab₂ F.pd₂ (F.stm₂ cms rtreq q.plain) (F.run₂ q.plain))
    else none
  | .f5 ρ =>
    if F.J + 1 ≤ q.round ∧ q.round ≤ F.J + F.n₂ then
      some (rowCall F.lab₂ (q.round - F.J) ρ (F.msg q.round (q.rt.map digToBytes) q.plain)
        (F.kind q.round) (F.work q.round) (F.nonce q.round q.plain)
        (if q.round = F.J + F.n₂ then 1 else F.work q.round) K j)
    else none
  | .f3 ρ0 c =>
    if q.round = F.J3 ∧ j.val = K then
      some (firstCall F.lab₃ F.pd₃ (F.stm₃ ρ0 c q.plain) (F.run₃ q.plain))
    else none

/-- **The slot value**: the call in which the first chain is sealed: no message, the kind 6, no
work; block 1 of its row. -/
def gCallJ (F : FileJ L t) (q : JoiningRoundQuery 256 L t) : Option Fmt.OQ :=
  if q.round = F.J then
    some ⟨1, 162, F.lab₁, F.J, bitsToBytes q.ρ, roundBytes ByteArray.empty 6 0 0 0⟩
  else none

/-- **A leaf of the request tree.** The typed string: 256 bits of the slot value; the salt's 8 sR
bits; one word of 64 bits: the leaf's index in its tree, 2 ^ depth + place. -/
def rleafCall (cfg : ByteArray) (sR : ℕ) (q : Bits) : Option Fmt.OQ :=
  if q.length = 256 + 8 * sR + 64 then
    some ⟨0, 173, Fmt.leafPlace 0 4 (sR / 8),
      (Fmt.wordAt (bitsToBytes (q.drop (256 + 8 * sR))) 0).toNat, cfg,
      bitsToBytes (q.take (256 + 8 * sR))⟩
  else none

/-- A vertex of the request tree. -/
def rnodeCall (cfg : ByteArray) (q : Bits × Bits) : Option Fmt.OQ :=
  some ⟨0, 178, 0, 0, cfg, bitsToBytes q.1 ++ bitsToBytes q.2⟩

/-- **The data of the page.** -/
structure PageJ (L : BatchProtocolWithLeafBody I X) (K : ℕ) where
  /-- the configuration's digest: the start of vertices and of the request tree -/
  cfg : ByteArray
  /-- the key file's chains, under the tag test -/
  key : FileJ L .test
  /-- the proof file's chains, under the tag onl -/
  proof : FileJ L .onl
  /-- the bytes of the salt of a leaf of the request tree -/
  sR : ℕ
  /-- a leaf of a tree over oracles or over a stored table -/
  leaf : LeafIn L → Option Fmt.OQ
  /-- taken as it is: the entry file's chain queries -/
  link : FbIn 256 L .link × Fin (K + 1) → Option (List Bool)
  /-- taken as it is: the seeds' chain queries, under the tag test -/
  seeds : FbIn 256 L .test × Fin (K + 1) → Option (List Bool)
  /-- taken as it is: the leaves that the entry file's walks ask -/
  leafX : LeafIn L → Option (List Bool)
  /-- taken as it is: the spare oracle's strings -/
  other : List Bool → Option (List Bool)

/-- The number of blocks of an answer. -/
def blocksJ (K : ℕ) : OracleName → ℕ
  | .fb _ => K + 1
  | .fbw _ _ => K + 1
  | _ => 1

variable {K : ℕ}

/-- **The format's call of a typed query and a block**, at the key file's and the proof file's
rows. -/
def callJ (P : PageJ L K) : (o : OracleName) → domOf 256 L o → Fin (blocksJ K o) → Option Fmt.OQ
  | .leaf, q, _ => P.leaf q
  | .node, q, _ => nodeCallC P.cfg q
  | .rleaf, q, _ => rleafCall P.cfg P.sR q
  | .rnode, q, _ => rnodeCall P.cfg q
  | .fb .test, q, j => fbCallJ P.key K q j
  | .fb .onl, q, j => fbCallJ P.proof K q j
  | .fb .link, _, _ => none
  | .fbw _ _, _, _ => none
  | .g .test, q, _ => gCallJ P.key q
  | .g .onl, q, _ => gCallJ P.proof q
  | .g .link, _, _ => none
  | .ann, _, _ => none
  | .other, _, _ => none

/-- What the four partial spellings write. -/
def takenJ (P : PageJ L K) : (o : OracleName) → domOf 256 L o → Fin (blocksJ K o) → Option (List Bool)
  | .leaf, q, _ => P.leafX q
  | .fb .test, q, j => P.seeds (q, j)
  | .fb .link, q, j => P.link (q, j)
  | .other, q, _ => P.other q
  | _, _, _ => none

/-- **The string of a typed query and a block.** -/
def codeJ (P : PageJ L K) (o : OracleName) (q : domOf 256 L o) (j : Fin (blocksJ K o)) : Option ByteArray :=
  match takenJ P o q j with
  | some s => some (bitsToBytes s)
  | none => (callJ P o q j).map strOf

/-- The answer of O at a string; zeros where there is none. -/
def ansJ (O : ByteArray → ByteArray) : Option ByteArray → Dig 256
  | some s => bytesToDig (O s)
  | none => fun _ => false

/-- **The typed oracle functions that a function on the format's strings induces.** -/
def gJ (P : PageJ L K) (O : ByteArray → ByteArray) : Fam (typedOracleFamily 256 K L)
  | .leaf, q => ansJ O (codeJ P .leaf q (0 : Fin 1))
  | .node, q => ansJ O (codeJ P .node q (0 : Fin 1))
  | .rleaf, q => ansJ O (codeJ P .rleaf q (0 : Fin 1))
  | .rnode, q => ansJ O (codeJ P .rnode q (0 : Fin 1))
  | .fb t, q =>
    (fun k => ansJ O (codeJ P (.fb t) q k.castSucc), ansJ O (codeJ P (.fb t) q (Fin.last K)))
  | .fbw _ _, _ => (fun _ _ => false, fun _ => false)
  | .g t, q => ansJ O (codeJ P (.g t) q (0 : Fin 1))
  | .ann, _ => ()
  | .other, q => ansJ O (codeJ P .other q (0 : Fin 1))

end OnBytes.Maker.Page
