-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/ParsedTyping.lean: from the struct of record (`Parsed`, OnBytes/Maker/Parsed.lean) to
the proof type of `innerCompiledVerifier` (Johnson/Top/InnerCompiledVerifier.lean): the signature, at letters.

AT LETTERS: IT CANNOT BE RUN: the object L, its marks aT and aL, and all that `Lay` holds are
letters.

States. No theorem.
  `InnerCompiledVerifierProof L aT aL`: the type of a proof of `innerSystem r` at r.protocol = L, r.offlineRoundSplits = aT, r.linkRoundSplits = aL: further
    tokens, the key (root, record), the typed proof (the copy's number; the key file's string; the
    further root, its record, the entry file's string; the proof file's string).
  `Lay L aT aL`: what the typing takes beside the struct. ALL OF IT COMES FROM THE USER's PUBLIC
    FILES AND THE HASH's ANSWER AT THEM, none of it from the struct: the parameters of the seven
    chains (the binding trees' shapes among them); the data of the two big files; four plain
    typings: of a table with its seeds as a record, and of the three earlier structs.
  `typeW h A F`: the typing. Its hash calls: chain by chain a call 169 and then a call 172, for
    seven chains: at most fourteen. WHOEVER MAKES `A` ASKS ONE MORE, AND FIRST: the configuration's
    digest, a hash of the public files: it begins the typed salt of every stored leaf, and every
    chain's parameter bytes hold it (`Given.cfg`, OnBytes/Params/Given.lean; `Fmt.paramsBytes … cfg`
    seven times in OnBytes/Params/Configure.lean). SO `typeW h A` AT A FIXED `A` IS NO READER OVER
    EVERY HASH: the reader is: ask the digest; make `A` of it; `typeW h A`: fifteen calls.
    `typeW` returns nothing where a root has not 32 bytes, a run value is refused, or one of the
    plain typings returns nothing.
WHERE EACH PART OF THE STRUCT LANDS. pad: the further tokens. first.root: the key's root.
first.seeds, first.answers: the key's record. copy: the copy's number. key: the key file's string.
further.root; further.seeds, further.answers: the link's root and record. link: the entry file's
string. proof: the proof file's string. Three values land twice, each time from the one
field: first.answers also in the key file's string, further.answers and copy also in the proof
file's string (plain parts of rounds that send no oracle): through the filled earlier structs.
NOTHING TIES `Lay`'s NINE LETTERS TO EACH OTHER: the data reach the typing by two roads (dataK,
dataP here; the data inside strT, strB), the binding trees' shapes by two; and within one letter a
`Params.Given` holds the bytes that are hashed beside the plan, digest and items that are read, tied
only if the value comes of `Given.read`. It can cost acceptance alone. When a description lies,
`Lay` is to be made by one function of the plan and the digest.
WHERE IT IS TO STAND. `soundForWith_via` (Johnson/Top/SoundVia.lean) takes a reader without coins,
with at most n queries, which is total: there the reader is the one just named, with a fixed proof
laid where it returns nothing, and the verifier that runs says no there. NOT YET OF THAT LEMMA's
TYPE: `typeW` stands in any monad at a letter h; that the lemma's algorithms are such a monad, with
an h that is one query a call, is shown in no file here. (Written before
Johnson/Top/ParsedReader.lean, which makes of `typeW` a reader with at most fifteen queries:
`reader`, `reader_asks`.) The lemma's reader sees prompt, output and the struct, never the
commitment.
Does not show: which h a sheet must hand in so that the digests made here are those that its check
makes itself (`Fmt.HO O` or `Fmt.HO (oBO O)`: the foot of OnBytes/ShellOf/EntryJoin.lean warns of
it); that anything is accepted; that the three plain typings at any written L are those of
OnBytes/Maker/CarrierTyping.lean and OnBytes/ShellOf/EntryParsed.lean; a count of queries as a
theorem; anything about soundness. A verifier behind this typing takes what it returns as the
prover's word.


-/
import OnBytes.Maker.Parsed
import Johnson.TypedOracleCompiler.RecCompile.FrontRoot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker.Parsed

open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig)

variable {I X : Type} (L : HolographicProtocol I X) (aT : RoundSplits L.offline.shape) (aL : RoundSplits L.link.shape)

/-- The proof type of `innerCompiledVerifier` at L, aT, aL. -/
abbrev InnerCompiledVerifierProof : Type :=
  List VerifiableInference.Token × (KeyRoot 256 L × OfflineLinkOnlineProof 256 L aT aL)

/-- What the typing takes beside the struct: from the user's public files and the hash's answer at
them (the configuration's digest), and from nothing else. -/
structure Lay where
  /-- the parameters of the key file's three chains, of the entry file's one, of the proof file's
  three -/
  parK : Params.KeyChains
  parL : Params.Link
  parP : Params.ProofChains
  /-- the data of the key file's chains, and of the proof file's. (The binding trees' shapes are
  read off parK and parP.) -/
  dataK : WholeD
  dataP : WholeD
  /-- four plain typings: their types bar a call of the letter h; that no written hash stands
  inside them is the duty of whoever fills `Lay`. A table's record: its seeds and its answers;
  nothing where the answers have not the shape's number or a word of them is not below p -/
  record : Table → Option L.Rec
  strT : Carrier.File → Option (OneProtocolProof 256 (batTC L aT))
  strL : ShellOf.EntryParsed.LeafP → Option (OneProtocolProof 256 (batLC L aL))
  strB : Carrier.File → Option (OneProtocolProof 256 L.onlineBatch)

variable {L aT aL}
variable {m : Type → Type} [Monad m] (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)

/-- The plain half of the typing: behind the seven run values. -/
def lay (A : Lay L aT aL) (F : Parsed) (rK rP : ByteArray × ByteArray × ByteArray)
    (rL : ByteArray) : Option (InnerCompiledVerifierProof L aT aL) :=
  (A.record F.first).bind fun c₀ => (A.record F.further).bind fun c₁ =>
  (A.strT (F.key.carrier A.dataK A.parK.oneTime.binding F.first 0 rK)).bind fun πT =>
    (A.strL (F.link.leafP F.first F.further rL)).bind fun πL =>
      (A.strB
        (F.proof.carrier A.dataP A.parP.first.binding F.further F.copy.toNat rP)).map fun πB =>
        (F.pad, (⟨bytesToDig F.first.root, c₀⟩,
          ⟨F.copy.toNat, some πT, (bytesToDig F.further.root, c₁, some πL), some πB⟩))

/-- **The typing.** -/
def typeW (A : Lay L aT aL) (F : Parsed) : m (Option (InnerCompiledVerifierProof L aT aL)) := do
  let rK ← F.key.keyRunsW h A.parK
  let rL ← F.link.runW h A.parL
  let rP ← F.proof.proofRunsW h A.parP
  pure (if F.rootsFit then
    rK.bind fun rK => rL.bind fun rL => rP.bind fun rP => lay A F rK rP rL else none)

end OnBytes.Maker.Parsed
