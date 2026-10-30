-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/ToldCommit.lean: THE HONEST COMMITTER BEHIND A PUBLIC READING, AS A TERM, LAID INTO A
TOLD RECORD (Johnson/Top/InnerCompiledVerifierByPublicReading.lean), AND ITS COUNT OF QUERIES. Definitions, statements and
proofs.

Why. Johnson/Top/OpensTold.lean shows binding of the told system's commitment under a law on the
record's committer (`CommitsBehind`: an equation of algorithms) and a bound on its queries. The
field `commit` of a told record is free: no statement on soundness reads it. Here the committer of
that law is written as a term over the record's other fields, so that the law holds by definition,
and its queries are counted.

Main names (namespace `VerifiableInference.OnPublicFiles`).
  `T.commitBehind ri sl b₀`: the public reading; `committerOverTypedOracles` (Johnson/TypedOracleCompiler/RecCompile/CommitOverTypedOracles.lean)
    at the wire of the record and the coding at the reading's value d; `T.part d` laid beside the
    key.
  `T.withCommit ri sl b₀ prove`: T with that committer, and a prover for what it keeps.
  `commitsBehind_withCommit`: the law of Johnson/Top/OpensTold.lean, by definition.
  `withCommit_V`, `withCommit_ext`, `withCommit_extractor`, `withCommit_at`: the verifier, the two
    extractors and the input at every d are T's own, by definition.
  **`queryBound_commitBehind`**: it asks at most tP + 2 · 2^depth + 2 (K + 1) queries, where tP
    bounds the public reading's.
  `queryBound_commit_systemE`: general in the scheme: the honest committer of `Rec.tokenArgumentSystem`
    (Johnson/Top/FrontEnc.lean) asks at most one query more than the scheme's.
  **`queryBound_commit_systemOn`**: so the honest committer of `(T.withCommit …).systemOn back nt`
    asks at most tP + 2 · 2^depth + 2 (K + 1) + 1 queries, at every index, whatever its coins.

WHO READS EACH LETTER (V: the told scheme's verifier; C: the committer; B: a bound; -: nobody here).
- T.Pub, T.part, T.Sd, T.m: V and C: THE SAME FIELDS IN BOTH. T.cA, T.Pt: V's side alone; not C.
- T.encT: V (the commitment is the hash function's answer at the told code) and the system's
  committer, behind C.
- R.queryLayout: V; C (`depth`, `K`, the writing of a leaf); B (`depth`, `K`). R.protocol: V; C (`wordLength`, `encodeIndex`, `honestOutOfDomainAnswer`,
  `EncodingRandomness`).
- ri, sl, b₀ (the coins' two enumerations; the filling beyond the word): C alone. Under "for all".
- prove: -. Under "for all". T.ISK, T.commit, T.prove: overwritten; nobody reads them.
- tP: B; tied by hP from below alone.
- back, nt, the coins: under "for all".
NOTHING THAT V READS STANDS UNDER "THERE IS": no statement here has one.

Limits.
- THE COMMITTER IS TIED TO NO PROGRAM: that a program's committer hashes these strings, in this
  order or at all, is not said.
- A count is a bound from above. One query counts as one, whatever its length.
- Nothing on opening-form binding (Johnson/Top/OpensTold.lean), no two openings, correctness of
  extraction or whatever else a key or a commitment fixes is proved here, nothing on hiding, nothing
  on acceptance: that the verifier says yes under a commitment of this committer is not said.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.OpensTold
import Rom.OneOfCount
import Rom.Prefix

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Rec
open Rom ZKCP

/-- **The honest committer of `tokenArgumentSystem` asks at most one query more than the scheme's**, at every
index, whatever its coins. -/
theorem queryBound_commit_systemE {I X IVK ISK Pf : Type}
    (G : ZKCP.Gen.Arg (rom 256) I X Unit IVK ISK Pf) (enc : IVK → Option ZKCP.Str) (bound : ℕ)
    (build : List Token × List Token → List Token → Option X) (π₀ : IVK × Pf)
    (nextToken : I → List Token → Option Token) (i : I) (t : ℕ) (h : (G.C i).QueryBound t)
    (coins : Fin (bound + 1)) :
    ((tokenArgumentSystem G enc bound build π₀ nextToken).commit i coins).toRandomized.QueryBound (t + 1) :=
  queryBound_deterministicOf _ (t + 1)
    (ZKCP.OComp.QueryBound.mapO _ _ (t + 1)
      (ZKCP.OComp.QueryBound.withCoins _ (t + 1) coins.val
        (ZKCP.queryBound_C_digestKey _ enc i t (Rom.queryBound_oneOf_C G i h))))

end VerifiableInference.Rec

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (ri : Enum R.protocol.EncodingRandomness) (sl : Enum (ℕ → Bits)) (b₀ : R.LeafBody)

/-- **The honest committer behind the public reading**: it reads the public value d, runs
`committerOverTypedOracles` at the wire of the record and the coding at d, and lays the told part beside the key. It
keeps the index and its coins. -/
def LayoutsByPublicReading.commitBehind (i : R.Index) :
    Rom.OComp (rom 256) ((Dig 256 × KeyRoot 256 R.protocol) × (R.Index × R.protocol.EncodingRandomness × (ℕ → Bits))) :=
  T.Pub.bind fun d =>
    ((committerOverTypedOracles R.queryLayout (T.Sd d) ri sl b₀ i).overOne (T.m d)).bind fun o =>
      .pure ((T.part d, o.1), o.2)

variable (prove : R.Index × R.protocol.EncodingRandomness × (ℕ → Bits) → (l : List (R.Instance × Unit)) →
  Rom.OComp (rom 256) (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) l))

/-- T with that committer, and a prover for what it keeps. The other fields are T's. -/
def LayoutsByPublicReading.withCommit : LayoutsByPublicReading R :=
  { T with
    ISK := R.Index × R.protocol.EncodingRandomness × (ℕ → Bits)
    commit := T.commitBehind ri sl b₀
    prove := prove }

/-- The law of Johnson/Top/OpensTold.lean holds of it by definition. -/
theorem commitsBehind_withCommit :
    CommitsBehind (T.withCommit ri sl b₀ prove) ri sl b₀ fun _ k => k := fun _ => rfl

/-- The verifier is T's. -/
theorem withCommit_V : (T.withCommit ri sl b₀ prove).scheme.V = T.scheme.V := rfl

/-- The extractor at a key is T's. -/
theorem withCommit_ext : (T.withCommit ri sl b₀ prove).ext = T.ext := rfl

/-- The named extractor is T's. -/
theorem withCommit_extractor : (T.withCommit ri sl b₀ prove).extractor = T.extractor := rfl

/-- The input at every d is T's. -/
theorem withCommit_at (d : T.D) : (T.withCommit ri sl b₀ prove).at d = T.at d := rfl

/-- **Its count**: the public reading's queries, two for each leaf of the tree, and the seed's two
typed queries of K + 1 digests each. -/
theorem queryBound_commitBehind (tP : ℕ) (hP : T.Pub.QueryBound tP) (i : R.Index) :
    (T.commitBehind ri sl b₀ i).QueryBound (tP + (2 * 2 ^ R.queryLayout.depth + 2 * (R.queryLayout.K + 1))) := by
  refine OComp.QueryBound.bind hP fun d => ?_
  have h := queryBound_committerOverTypedOracles_one R.queryLayout (T.Sd d) (T.m d) ri sl b₀ i
  rw [committerQueryCount_eq R.queryLayout (T.Sd d) (by norm_num) (T.m d)] at h
  exact OComp.QueryBound.bind (t := 0) h fun _ => trivial

/-- **The count of the system's honest committer**, at a cut type of indices: one query more, for
the key's code. -/
theorem queryBound_commit_systemOn {J : Type} (back : J → R.Index)
    (nt : J → List Token → Option Token) (tP : ℕ) (hP : T.Pub.QueryBound tP) (j : J)
    (coins : Fin (R.coinBound + 1)) :
    (((T.withCommit ri sl b₀ prove).systemOn back nt).commit j coins).toRandomized.QueryBound
      (tP + (2 * 2 ^ R.queryLayout.depth + 2 * (R.queryLayout.K + 1)) + 1) :=
  Rec.queryBound_commit_systemE ((T.withCommit ri sl b₀ prove).schemeOn back) T.encT R.coinBound R.buildInstance
    T.π₀ nt j _ (queryBound_commitBehind T ri sl b₀ tP hP (back j)) coins

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.Rec.queryBound_commit_systemE
#print axioms VerifiableInference.OnPublicFiles.commitsBehind_withCommit
#print axioms VerifiableInference.OnPublicFiles.withCommit_V
#print axioms VerifiableInference.OnPublicFiles.withCommit_ext
#print axioms VerifiableInference.OnPublicFiles.withCommit_extractor
#print axioms VerifiableInference.OnPublicFiles.withCommit_at
#print axioms VerifiableInference.OnPublicFiles.queryBound_commitBehind
#print axioms VerifiableInference.OnPublicFiles.queryBound_commit_systemOn
