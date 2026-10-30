-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/ToldCommitSalts.lean: THE TOLD SYSTEM'S COMMITMENT READS THE SALTS AT THE TREE'S PLACES
ALONE. Statements and proofs; general in the told record.

Why. Johnson/Top/ToldCommitAt.lean names the committer with two coins fixed. An enumeration of salts
can list them only as far as the tree reads them, so a statement "every setting of coins is reached"
ended at salts that AGREE with the given ones at the tree's places
Here: two such committers are one algorithm. What the committer KEEPS holds the salts whole,
so the sentence is false of the scheme's committer's value; it is stated of the commitment.

Main names.
  `Rec.commitE_of_key` (namespace `VerifiableInference.Rec`): `commitE` at the number n is: the
    scheme's committer at n, of whose result the key alone is kept; then the key's digest.
  `Rec.commit_systemE_congr_key`: two schemes with one code of keys whose committers, the key alone
    kept, agree at an index, at the numbers n and n': the two systems' committers there are one
    algorithm.
  `committerAtFixedCoins_key_congr` (namespace `VerifiableInference.OnPublicFiles`): `committerAtFixedCoins`
    (Johnson/TypedOracleCompiler/RecCompile/CommitOverTypedOracles.lean), the key alone kept, is one computation at two salts
    that agree at the first 2^depth places. By `committerTreeRoot_congr` (Johnson/Top/ToldReachAll.lean).
  **`commit_systemOn_salts`**: the committers of `(T.withCommit (enumOne r) (enumOne σ) b₀
    prove).systemOn back nt` and of the same at σ' are one algorithm at the number 0, where σ and σ'
    agree at the first 2^depth places. Premise besides: the public reading draws nothing.

Limits. An equation between two terms of this library: nothing on any program. Nothing on what the
committer keeps.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.ToldCommitAt
import Johnson.Top.ToldReachAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Rec
open Rom ZKCP

variable {I X IVK ISK Pf : Type}

/-- The digest laid beside the keys, and of the pair the digest kept: the digest. -/
theorem keyDigest_fst (enc : IVK → Option ZKCP.Str) (keys : IVK × ISK) :
    ((ZKCP.keyDigest (lam := 256) enc keys.1).mapO fun digest => (digest, keys)).mapO Prod.fst =
      ZKCP.keyDigest enc keys.1 := by
  unfold ZKCP.keyDigest
  split <;> rfl

/-- `commitE` at a number reads of the scheme's committer's result the key alone. -/
theorem commitE_of_key (G : ZKCP.Gen.Arg (rom 256) I X Unit IVK ISK Pf)
    (enc : IVK → Option ZKCP.Str) (bound : ℕ) (i : I) (coins : Fin (bound + 1)) :
    commitE G enc bound i coins =
      (ofRom (((G.C i).withCoins coins.val).bind fun keys => .pure keys.1)).bind
        (ZKCP.keyDigest enc) := by
  rw [commitE_eq, ZKCP.OComp.bind_mapO, ZKCP.SpecialAny.ofRom_bind, ZKCP.OComp.bind_bind]
  congr 1
  funext keys
  exact keyDigest_fst enc keys

/-- **Two systems whose schemes' committers give one key at two numbers commit alike there.** -/
theorem commit_systemE_congr_key (G G' : ZKCP.Gen.Arg (rom 256) I X Unit IVK ISK Pf)
    (enc : IVK → Option ZKCP.Str) (bound bound' : ℕ)
    (build : List Token × List Token → List Token → Option X) (π₀ : IVK × Pf)
    (nextToken : I → List Token → Option Token) (i : I) (n : Fin (bound + 1))
    (n' : Fin (bound' + 1))
    (h : (((G.C i).withCoins n.val).bind fun keys => Rom.OComp.pure keys.1) =
      ((G'.C i).withCoins n'.val).bind fun keys => Rom.OComp.pure keys.1) :
    (tokenArgumentSystem G enc bound build π₀ nextToken).commit i n =
      (tokenArgumentSystem G' enc bound' build π₀ nextToken).commit i n' := by
  show deterministicOf (commitE G enc bound i n) = deterministicOf (commitE G' enc bound' i n')
  rw [commitE_of_key, commitE_of_key, h]

end VerifiableInference.Rec

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- **The key reads the salts through the tree alone.** -/
theorem committerAtFixedCoins_key_congr {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type}
    {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (σ σ' : ℕ → Bits)
    (h : ∀ j, j < 2 ^ W.depth → σ j = σ' j) :
    ((committerAtFixedCoins W S b₀ i r σ).bind fun o => Rom.OComp.pure o.1) =
      (committerAtFixedCoins W S b₀ i r σ').bind fun o => Rom.OComp.pure o.1 := by
  unfold committerAtFixedCoins
  rw [committerTreeRoot_congr W b₀ (L.encodeIndex i r) σ σ' h]
  simp only [Rom.OComp.bind_assoc]
  rfl

variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (b₀ : R.LeafBody)
  (prove : R.Index × R.protocol.EncodingRandomness × (ℕ → Bits) → (l : List (R.Instance × Unit)) →
    Rom.OComp (rom 256) (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) l))

/-- The committer behind the public reading at two fixed coins, the key alone kept. -/
theorem commitBehind_key_congr (i : R.Index) (r : R.protocol.EncodingRandomness) (σ σ' : ℕ → Bits)
    (h : ∀ j, j < 2 ^ R.queryLayout.depth → σ j = σ' j) :
    ((T.Pub.bind fun d => ((committerAtFixedCoins R.queryLayout (T.Sd d) b₀ i r σ).overOne (T.m d)).bind
        fun o => Rom.OComp.pure ((T.part d, o.1), o.2)).bind fun keys => Rom.OComp.pure keys.1) =
      (T.Pub.bind fun d => ((committerAtFixedCoins R.queryLayout (T.Sd d) b₀ i r σ').overOne (T.m d)).bind
        fun o => Rom.OComp.pure ((T.part d, o.1), o.2)).bind fun keys => Rom.OComp.pure keys.1 := by
  have e : ∀ (d : T.D) (τ : ℕ → Bits),
      ((((committerAtFixedCoins R.queryLayout (T.Sd d) b₀ i r τ).overOne (T.m d)).bind
        fun o => Rom.OComp.pure ((T.part d, o.1), o.2)).bind fun keys => Rom.OComp.pure keys.1) =
      (((committerAtFixedCoins R.queryLayout (T.Sd d) b₀ i r τ).bind fun o => Rom.OComp.pure o.1).overOne (T.m d)).bind
        fun k => Rom.OComp.pure (T.part d, k) := by
    intro d τ
    rw [Rom.overOne_bind, Rom.OComp.bind_assoc, Rom.OComp.bind_assoc]
    rfl
  rw [Rom.OComp.bind_assoc, Rom.OComp.bind_assoc]
  congr 1
  funext d
  rw [e d σ, e d σ', committerAtFixedCoins_key_congr R.queryLayout (T.Sd d) b₀ i r σ σ' h]

/-- **THE COMMITMENT READS THE SALTS AT THE TREE'S PLACES ALONE.** -/
theorem commit_systemOn_salts {J : Type} (back : J → R.Index) (nt : J → List Token → Option Token)
    (noCoin : T.Pub.NoCoin) (j : J) (r : R.protocol.EncodingRandomness) (σ σ' : ℕ → Bits)
    (h : ∀ k, k < 2 ^ R.queryLayout.depth → σ k = σ' k) :
    ((T.withCommit (enumOne r) (enumOne σ) b₀ prove).systemOn back nt).commit j
        (⟨0, Nat.succ_pos _⟩ : Fin (R.coinBound + 1)) =
      ((T.withCommit (enumOne r) (enumOne σ') b₀ prove).systemOn back nt).commit j
        (⟨0, Nat.succ_pos _⟩ : Fin (R.coinBound + 1)) := by
  refine Rec.commit_systemE_congr_key
    ((T.withCommit (enumOne r) (enumOne σ) b₀ prove).schemeOn back)
    ((T.withCommit (enumOne r) (enumOne σ') b₀ prove).schemeOn back) T.encT R.coinBound R.coinBound R.buildInstance
    T.π₀ nt j _ _ ?_
  show ((T.commitBehind (enumOne r) (enumOne σ) b₀ (back j)).withCoins 0).bind
      (fun keys => Rom.OComp.pure keys.1) =
    ((T.commitBehind (enumOne r) (enumOne σ') b₀ (back j)).withCoins 0).bind
      fun keys => Rom.OComp.pure keys.1
  have e : ∀ τ : ℕ → Bits, (T.commitBehind (enumOne r) (enumOne τ) b₀ (back j)).withCoins 0 =
      T.Pub.bind fun d => ((committerAtFixedCoins R.queryLayout (T.Sd d) b₀ (back j) r τ).overOne (T.m d)).bind
        fun o => Rom.OComp.pure ((T.part d, o.1), o.2) :=
    fun τ => commitBehind_reach T (enumOne r) (enumOne τ) b₀ noCoin (back j) 0 0
  rw [e σ, e σ']
  exact commitBehind_key_congr T b₀ (back j) r σ σ' h

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.Rec.commitE_of_key
#print axioms VerifiableInference.Rec.commit_systemE_congr_key
#print axioms VerifiableInference.OnPublicFiles.committerAtFixedCoins_key_congr
#print axioms VerifiableInference.OnPublicFiles.commit_systemOn_salts
